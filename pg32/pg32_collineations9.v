Require Import ssreflect ssrfun ssrbool.
Require Import Generic.lemmas.
Require Import PG32.pg32_inductive PG32.pg32_spreads_collineations.
Require Import PG32.pg32_automorphisms.
Require Import PG32.pg32_automorphisms_inv.
Require Import Lists.List.
Import ListNotations.
Require Import Arith.

Lemma collineation_12096 : is_collineation fp_12096 fl_12096.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12096 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12096 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12096.

Lemma collineation_12097 : is_collineation fp_12097 fl_12097.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12097 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12097 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12097.

Lemma collineation_12098 : is_collineation fp_12098 fl_12098.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12098 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12098 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12098.

Lemma collineation_12099 : is_collineation fp_12099 fl_12099.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12099 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12099 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12099.

Lemma collineation_12100 : is_collineation fp_12100 fl_12100.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12100 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12100 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12100.

Lemma collineation_12101 : is_collineation fp_12101 fl_12101.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12101 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12101 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12101.

Lemma collineation_12102 : is_collineation fp_12102 fl_12102.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12102 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12102 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12102.

Lemma collineation_12103 : is_collineation fp_12103 fl_12103.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12103 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12103 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12103.

Lemma collineation_12104 : is_collineation fp_12104 fl_12104.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12104 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12104 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12104.

Lemma collineation_12105 : is_collineation fp_12105 fl_12105.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12105 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12105 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12105.

Lemma collineation_12106 : is_collineation fp_12106 fl_12106.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12106 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12106 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12106.

Lemma collineation_12107 : is_collineation fp_12107 fl_12107.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12107 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12107 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12107.

Lemma collineation_12108 : is_collineation fp_12108 fl_12108.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12108 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12108 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12108.

Lemma collineation_12109 : is_collineation fp_12109 fl_12109.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12109 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12109 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12109.

Lemma collineation_12110 : is_collineation fp_12110 fl_12110.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12110 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12110 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12110.

Lemma collineation_12111 : is_collineation fp_12111 fl_12111.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12111 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12111 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12111.

Lemma collineation_12112 : is_collineation fp_12112 fl_12112.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12112 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12112 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12112.

Lemma collineation_12113 : is_collineation fp_12113 fl_12113.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12113 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12113 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12113.

Lemma collineation_12114 : is_collineation fp_12114 fl_12114.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12114 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12114 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12114.

Lemma collineation_12115 : is_collineation fp_12115 fl_12115.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12115 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12115 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12115.

Lemma collineation_12116 : is_collineation fp_12116 fl_12116.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12116 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12116 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12116.

Lemma collineation_12117 : is_collineation fp_12117 fl_12117.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12117 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12117 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12117.

Lemma collineation_12118 : is_collineation fp_12118 fl_12118.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12118 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12118 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12118.

Lemma collineation_12119 : is_collineation fp_12119 fl_12119.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12119 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12119 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12119.

Lemma collineation_12120 : is_collineation fp_12120 fl_12120.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12120 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12120 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12120.

Lemma collineation_12121 : is_collineation fp_12121 fl_12121.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12121 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12121 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12121.

Lemma collineation_12122 : is_collineation fp_12122 fl_12122.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12122 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12122 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12122.

Lemma collineation_12123 : is_collineation fp_12123 fl_12123.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12123 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12123 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12123.

Lemma collineation_12124 : is_collineation fp_12124 fl_12124.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12124 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12124 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12124.

Lemma collineation_12125 : is_collineation fp_12125 fl_12125.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12125 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12125 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12125.

Lemma collineation_12126 : is_collineation fp_12126 fl_12126.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12126 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12126 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12126.

Lemma collineation_12127 : is_collineation fp_12127 fl_12127.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12127 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12127 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12127.

Lemma collineation_12128 : is_collineation fp_12128 fl_12128.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12128 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12128 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12128.

Lemma collineation_12129 : is_collineation fp_12129 fl_12129.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12129 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12129 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12129.

Lemma collineation_12130 : is_collineation fp_12130 fl_12130.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12130 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12130 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12130.

Lemma collineation_12131 : is_collineation fp_12131 fl_12131.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12131 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12131 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12131.

Lemma collineation_12132 : is_collineation fp_12132 fl_12132.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12132 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12132 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12132.

Lemma collineation_12133 : is_collineation fp_12133 fl_12133.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12133 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12133 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12133.

Lemma collineation_12134 : is_collineation fp_12134 fl_12134.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12134 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12134 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12134.

Lemma collineation_12135 : is_collineation fp_12135 fl_12135.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12135 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12135 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12135.

Lemma collineation_12136 : is_collineation fp_12136 fl_12136.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12136 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12136 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12136.

Lemma collineation_12137 : is_collineation fp_12137 fl_12137.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12137 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12137 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12137.

Lemma collineation_12138 : is_collineation fp_12138 fl_12138.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12138 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12138 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12138.

Lemma collineation_12139 : is_collineation fp_12139 fl_12139.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12139 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12139 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12139.

Lemma collineation_12140 : is_collineation fp_12140 fl_12140.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12140 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12140 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12140.

Lemma collineation_12141 : is_collineation fp_12141 fl_12141.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12141 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12141 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12141.

Lemma collineation_12142 : is_collineation fp_12142 fl_12142.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12142 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12142 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12142.

Lemma collineation_12143 : is_collineation fp_12143 fl_12143.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12143 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12143 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12143.

Lemma collineation_12144 : is_collineation fp_12144 fl_12144.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12144 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12144 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12144.

Lemma collineation_12145 : is_collineation fp_12145 fl_12145.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12145 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12145 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12145.

Lemma collineation_12146 : is_collineation fp_12146 fl_12146.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12146 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12146 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12146.

Lemma collineation_12147 : is_collineation fp_12147 fl_12147.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12147 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12147 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12147.

Lemma collineation_12148 : is_collineation fp_12148 fl_12148.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12148 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12148 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12148.

Lemma collineation_12149 : is_collineation fp_12149 fl_12149.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12149 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12149 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12149.

Lemma collineation_12150 : is_collineation fp_12150 fl_12150.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12150 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12150 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12150.

Lemma collineation_12151 : is_collineation fp_12151 fl_12151.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12151 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12151 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12151.

Lemma collineation_12152 : is_collineation fp_12152 fl_12152.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12152 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12152 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12152.

Lemma collineation_12153 : is_collineation fp_12153 fl_12153.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12153 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12153 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12153.

Lemma collineation_12154 : is_collineation fp_12154 fl_12154.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12154 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12154 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12154.

Lemma collineation_12155 : is_collineation fp_12155 fl_12155.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12155 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12155 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12155.

Lemma collineation_12156 : is_collineation fp_12156 fl_12156.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12156 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12156 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12156.

Lemma collineation_12157 : is_collineation fp_12157 fl_12157.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12157 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12157 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12157.

Lemma collineation_12158 : is_collineation fp_12158 fl_12158.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12158 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12158 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12158.

Lemma collineation_12159 : is_collineation fp_12159 fl_12159.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12159 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12159 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12159.

Lemma collineation_12160 : is_collineation fp_12160 fl_12160.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12160 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12160 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12160.

Lemma collineation_12161 : is_collineation fp_12161 fl_12161.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12161 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12161 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12161.

Lemma collineation_12162 : is_collineation fp_12162 fl_12162.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12162 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12162 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12162.

Lemma collineation_12163 : is_collineation fp_12163 fl_12163.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12163 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12163 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12163.

Lemma collineation_12164 : is_collineation fp_12164 fl_12164.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12164 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12164 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12164.

Lemma collineation_12165 : is_collineation fp_12165 fl_12165.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12165 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12165 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12165.

Lemma collineation_12166 : is_collineation fp_12166 fl_12166.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12166 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12166 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12166.

Lemma collineation_12167 : is_collineation fp_12167 fl_12167.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12167 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12167 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12167.

Lemma collineation_12168 : is_collineation fp_12168 fl_12168.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12168 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12168 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12168.

Lemma collineation_12169 : is_collineation fp_12169 fl_12169.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12169 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12169 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12169.

Lemma collineation_12170 : is_collineation fp_12170 fl_12170.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12170 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12170 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12170.

Lemma collineation_12171 : is_collineation fp_12171 fl_12171.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12171 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12171 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12171.

Lemma collineation_12172 : is_collineation fp_12172 fl_12172.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12172 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12172 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12172.

Lemma collineation_12173 : is_collineation fp_12173 fl_12173.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12173 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12173 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12173.

Lemma collineation_12174 : is_collineation fp_12174 fl_12174.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12174 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12174 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12174.

Lemma collineation_12175 : is_collineation fp_12175 fl_12175.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12175 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12175 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12175.

Lemma collineation_12176 : is_collineation fp_12176 fl_12176.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12176 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12176 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12176.

Lemma collineation_12177 : is_collineation fp_12177 fl_12177.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12177 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12177 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12177.

Lemma collineation_12178 : is_collineation fp_12178 fl_12178.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12178 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12178 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12178.

Lemma collineation_12179 : is_collineation fp_12179 fl_12179.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12179 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12179 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12179.

Lemma collineation_12180 : is_collineation fp_12180 fl_12180.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12180 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12180 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12180.

Lemma collineation_12181 : is_collineation fp_12181 fl_12181.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12181 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12181 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12181.

Lemma collineation_12182 : is_collineation fp_12182 fl_12182.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12182 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12182 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12182.

Lemma collineation_12183 : is_collineation fp_12183 fl_12183.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12183 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12183 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12183.

Lemma collineation_12184 : is_collineation fp_12184 fl_12184.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12184 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12184 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12184.

Lemma collineation_12185 : is_collineation fp_12185 fl_12185.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12185 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12185 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12185.

Lemma collineation_12186 : is_collineation fp_12186 fl_12186.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12186 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12186 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12186.

Lemma collineation_12187 : is_collineation fp_12187 fl_12187.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12187 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12187 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12187.

Lemma collineation_12188 : is_collineation fp_12188 fl_12188.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12188 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12188 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12188.

Lemma collineation_12189 : is_collineation fp_12189 fl_12189.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12189 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12189 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12189.

Lemma collineation_12190 : is_collineation fp_12190 fl_12190.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12190 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12190 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12190.

Lemma collineation_12191 : is_collineation fp_12191 fl_12191.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12191 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12191 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12191.

Lemma collineation_12192 : is_collineation fp_12192 fl_12192.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12192 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12192 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12192.

Lemma collineation_12193 : is_collineation fp_12193 fl_12193.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12193 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12193 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12193.

Lemma collineation_12194 : is_collineation fp_12194 fl_12194.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12194 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12194 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12194.

Lemma collineation_12195 : is_collineation fp_12195 fl_12195.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12195 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12195 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12195.

Lemma collineation_12196 : is_collineation fp_12196 fl_12196.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12196 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12196 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12196.

Lemma collineation_12197 : is_collineation fp_12197 fl_12197.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12197 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12197 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12197.

Lemma collineation_12198 : is_collineation fp_12198 fl_12198.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12198 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12198 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12198.

Lemma collineation_12199 : is_collineation fp_12199 fl_12199.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12199 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12199 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12199.

Lemma collineation_12200 : is_collineation fp_12200 fl_12200.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12200 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12200 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12200.

Lemma collineation_12201 : is_collineation fp_12201 fl_12201.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12201 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12201 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12201.

Lemma collineation_12202 : is_collineation fp_12202 fl_12202.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12202 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12202 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12202.

Lemma collineation_12203 : is_collineation fp_12203 fl_12203.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12203 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12203 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12203.

Lemma collineation_12204 : is_collineation fp_12204 fl_12204.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12204 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12204 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12204.

Lemma collineation_12205 : is_collineation fp_12205 fl_12205.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12205 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12205 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12205.

Lemma collineation_12206 : is_collineation fp_12206 fl_12206.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12206 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12206 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12206.

Lemma collineation_12207 : is_collineation fp_12207 fl_12207.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12207 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12207 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12207.

Lemma collineation_12208 : is_collineation fp_12208 fl_12208.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12208 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12208 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12208.

Lemma collineation_12209 : is_collineation fp_12209 fl_12209.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12209 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12209 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12209.

Lemma collineation_12210 : is_collineation fp_12210 fl_12210.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12210 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12210 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12210.

Lemma collineation_12211 : is_collineation fp_12211 fl_12211.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12211 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12211 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12211.

Lemma collineation_12212 : is_collineation fp_12212 fl_12212.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12212 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12212 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12212.

Lemma collineation_12213 : is_collineation fp_12213 fl_12213.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12213 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12213 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12213.

Lemma collineation_12214 : is_collineation fp_12214 fl_12214.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12214 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12214 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12214.

Lemma collineation_12215 : is_collineation fp_12215 fl_12215.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12215 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12215 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12215.

Lemma collineation_12216 : is_collineation fp_12216 fl_12216.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12216 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12216 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12216.

Lemma collineation_12217 : is_collineation fp_12217 fl_12217.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12217 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12217 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12217.

Lemma collineation_12218 : is_collineation fp_12218 fl_12218.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12218 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12218 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12218.

Lemma collineation_12219 : is_collineation fp_12219 fl_12219.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12219 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12219 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12219.

Lemma collineation_12220 : is_collineation fp_12220 fl_12220.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12220 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12220 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12220.

Lemma collineation_12221 : is_collineation fp_12221 fl_12221.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12221 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12221 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12221.

Lemma collineation_12222 : is_collineation fp_12222 fl_12222.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12222 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12222 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12222.

Lemma collineation_12223 : is_collineation fp_12223 fl_12223.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12223 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12223 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12223.

Lemma collineation_12224 : is_collineation fp_12224 fl_12224.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12224 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12224 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12224.

Lemma collineation_12225 : is_collineation fp_12225 fl_12225.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12225 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12225 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12225.

Lemma collineation_12226 : is_collineation fp_12226 fl_12226.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12226 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12226 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12226.

Lemma collineation_12227 : is_collineation fp_12227 fl_12227.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12227 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12227 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12227.

Lemma collineation_12228 : is_collineation fp_12228 fl_12228.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12228 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12228 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12228.

Lemma collineation_12229 : is_collineation fp_12229 fl_12229.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12229 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12229 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12229.

Lemma collineation_12230 : is_collineation fp_12230 fl_12230.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12230 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12230 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12230.

Lemma collineation_12231 : is_collineation fp_12231 fl_12231.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12231 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12231 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12231.

Lemma collineation_12232 : is_collineation fp_12232 fl_12232.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12232 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12232 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12232.

Lemma collineation_12233 : is_collineation fp_12233 fl_12233.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12233 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12233 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12233.

Lemma collineation_12234 : is_collineation fp_12234 fl_12234.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12234 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12234 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12234.

Lemma collineation_12235 : is_collineation fp_12235 fl_12235.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12235 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12235 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12235.

Lemma collineation_12236 : is_collineation fp_12236 fl_12236.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12236 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12236 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12236.

Lemma collineation_12237 : is_collineation fp_12237 fl_12237.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12237 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12237 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12237.

Lemma collineation_12238 : is_collineation fp_12238 fl_12238.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12238 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12238 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12238.

Lemma collineation_12239 : is_collineation fp_12239 fl_12239.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12239 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12239 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12239.

Lemma collineation_12240 : is_collineation fp_12240 fl_12240.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12240 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12240 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12240.

Lemma collineation_12241 : is_collineation fp_12241 fl_12241.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12241 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12241 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12241.

Lemma collineation_12242 : is_collineation fp_12242 fl_12242.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12242 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12242 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12242.

Lemma collineation_12243 : is_collineation fp_12243 fl_12243.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12243 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12243 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12243.

Lemma collineation_12244 : is_collineation fp_12244 fl_12244.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12244 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12244 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12244.

Lemma collineation_12245 : is_collineation fp_12245 fl_12245.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12245 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12245 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12245.

Lemma collineation_12246 : is_collineation fp_12246 fl_12246.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12246 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12246 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12246.

Lemma collineation_12247 : is_collineation fp_12247 fl_12247.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12247 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12247 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12247.

Lemma collineation_12248 : is_collineation fp_12248 fl_12248.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12248 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12248 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12248.

Lemma collineation_12249 : is_collineation fp_12249 fl_12249.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12249 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12249 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12249.

Lemma collineation_12250 : is_collineation fp_12250 fl_12250.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12250 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12250 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12250.

Lemma collineation_12251 : is_collineation fp_12251 fl_12251.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12251 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12251 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12251.

Lemma collineation_12252 : is_collineation fp_12252 fl_12252.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12252 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12252 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12252.

Lemma collineation_12253 : is_collineation fp_12253 fl_12253.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12253 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12253 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12253.

Lemma collineation_12254 : is_collineation fp_12254 fl_12254.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12254 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12254 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12254.

Lemma collineation_12255 : is_collineation fp_12255 fl_12255.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12255 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12255 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12255.

Lemma collineation_12256 : is_collineation fp_12256 fl_12256.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12256 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12256 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12256.

Lemma collineation_12257 : is_collineation fp_12257 fl_12257.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12257 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12257 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12257.

Lemma collineation_12258 : is_collineation fp_12258 fl_12258.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12258 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12258 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12258.

Lemma collineation_12259 : is_collineation fp_12259 fl_12259.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12259 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12259 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12259.

Lemma collineation_12260 : is_collineation fp_12260 fl_12260.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12260 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12260 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12260.

Lemma collineation_12261 : is_collineation fp_12261 fl_12261.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12261 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12261 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12261.

Lemma collineation_12262 : is_collineation fp_12262 fl_12262.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12262 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12262 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12262.

Lemma collineation_12263 : is_collineation fp_12263 fl_12263.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12263 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12263 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12263.

Lemma collineation_12264 : is_collineation fp_12264 fl_12264.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12264 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12264 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12264.

Lemma collineation_12265 : is_collineation fp_12265 fl_12265.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12265 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12265 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12265.

Lemma collineation_12266 : is_collineation fp_12266 fl_12266.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12266 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12266 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12266.

Lemma collineation_12267 : is_collineation fp_12267 fl_12267.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12267 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12267 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12267.

Lemma collineation_12268 : is_collineation fp_12268 fl_12268.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12268 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12268 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12268.

Lemma collineation_12269 : is_collineation fp_12269 fl_12269.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12269 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12269 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12269.

Lemma collineation_12270 : is_collineation fp_12270 fl_12270.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12270 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12270 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12270.

Lemma collineation_12271 : is_collineation fp_12271 fl_12271.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12271 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12271 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12271.

Lemma collineation_12272 : is_collineation fp_12272 fl_12272.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12272 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12272 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12272.

Lemma collineation_12273 : is_collineation fp_12273 fl_12273.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12273 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12273 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12273.

Lemma collineation_12274 : is_collineation fp_12274 fl_12274.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12274 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12274 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12274.

Lemma collineation_12275 : is_collineation fp_12275 fl_12275.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12275 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12275 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12275.

Lemma collineation_12276 : is_collineation fp_12276 fl_12276.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12276 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12276 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12276.

Lemma collineation_12277 : is_collineation fp_12277 fl_12277.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12277 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12277 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12277.

Lemma collineation_12278 : is_collineation fp_12278 fl_12278.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12278 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12278 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12278.

Lemma collineation_12279 : is_collineation fp_12279 fl_12279.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12279 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12279 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12279.

Lemma collineation_12280 : is_collineation fp_12280 fl_12280.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12280 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12280 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12280.

Lemma collineation_12281 : is_collineation fp_12281 fl_12281.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12281 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12281 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12281.

Lemma collineation_12282 : is_collineation fp_12282 fl_12282.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12282 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12282 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12282.

Lemma collineation_12283 : is_collineation fp_12283 fl_12283.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12283 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12283 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12283.

Lemma collineation_12284 : is_collineation fp_12284 fl_12284.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12284 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12284 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12284.

Lemma collineation_12285 : is_collineation fp_12285 fl_12285.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12285 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12285 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12285.

Lemma collineation_12286 : is_collineation fp_12286 fl_12286.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12286 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12286 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12286.

Lemma collineation_12287 : is_collineation fp_12287 fl_12287.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12287 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12287 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12287.

Lemma collineation_12288 : is_collineation fp_12288 fl_12288.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12288 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12288 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12288.

Lemma collineation_12289 : is_collineation fp_12289 fl_12289.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12289 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12289 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12289.

Lemma collineation_12290 : is_collineation fp_12290 fl_12290.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12290 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12290 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12290.

Lemma collineation_12291 : is_collineation fp_12291 fl_12291.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12291 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12291 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12291.

Lemma collineation_12292 : is_collineation fp_12292 fl_12292.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12292 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12292 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12292.

Lemma collineation_12293 : is_collineation fp_12293 fl_12293.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12293 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12293 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12293.

Lemma collineation_12294 : is_collineation fp_12294 fl_12294.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12294 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12294 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12294.

Lemma collineation_12295 : is_collineation fp_12295 fl_12295.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12295 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12295 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12295.

Lemma collineation_12296 : is_collineation fp_12296 fl_12296.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12296 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12296 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12296.

Lemma collineation_12297 : is_collineation fp_12297 fl_12297.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12297 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12297 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12297.

Lemma collineation_12298 : is_collineation fp_12298 fl_12298.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12298 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12298 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12298.

Lemma collineation_12299 : is_collineation fp_12299 fl_12299.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12299 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12299 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12299.

Lemma collineation_12300 : is_collineation fp_12300 fl_12300.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12300 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12300 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12300.

Lemma collineation_12301 : is_collineation fp_12301 fl_12301.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12301 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12301 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12301.

Lemma collineation_12302 : is_collineation fp_12302 fl_12302.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12302 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12302 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12302.

Lemma collineation_12303 : is_collineation fp_12303 fl_12303.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12303 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12303 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12303.

Lemma collineation_12304 : is_collineation fp_12304 fl_12304.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12304 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12304 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12304.

Lemma collineation_12305 : is_collineation fp_12305 fl_12305.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12305 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12305 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12305.

Lemma collineation_12306 : is_collineation fp_12306 fl_12306.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12306 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12306 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12306.

Lemma collineation_12307 : is_collineation fp_12307 fl_12307.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12307 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12307 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12307.

Lemma collineation_12308 : is_collineation fp_12308 fl_12308.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12308 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12308 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12308.

Lemma collineation_12309 : is_collineation fp_12309 fl_12309.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12309 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12309 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12309.

Lemma collineation_12310 : is_collineation fp_12310 fl_12310.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12310 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12310 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12310.

Lemma collineation_12311 : is_collineation fp_12311 fl_12311.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12311 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12311 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12311.

Lemma collineation_12312 : is_collineation fp_12312 fl_12312.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12312 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12312 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12312.

Lemma collineation_12313 : is_collineation fp_12313 fl_12313.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12313 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12313 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12313.

Lemma collineation_12314 : is_collineation fp_12314 fl_12314.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12314 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12314 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12314.

Lemma collineation_12315 : is_collineation fp_12315 fl_12315.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12315 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12315 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12315.

Lemma collineation_12316 : is_collineation fp_12316 fl_12316.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12316 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12316 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12316.

Lemma collineation_12317 : is_collineation fp_12317 fl_12317.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12317 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12317 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12317.

Lemma collineation_12318 : is_collineation fp_12318 fl_12318.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12318 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12318 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12318.

Lemma collineation_12319 : is_collineation fp_12319 fl_12319.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12319 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12319 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12319.

Lemma collineation_12320 : is_collineation fp_12320 fl_12320.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12320 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12320 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12320.

Lemma collineation_12321 : is_collineation fp_12321 fl_12321.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12321 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12321 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12321.

Lemma collineation_12322 : is_collineation fp_12322 fl_12322.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12322 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12322 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12322.

Lemma collineation_12323 : is_collineation fp_12323 fl_12323.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12323 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12323 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12323.

Lemma collineation_12324 : is_collineation fp_12324 fl_12324.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12324 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12324 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12324.

Lemma collineation_12325 : is_collineation fp_12325 fl_12325.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12325 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12325 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12325.

Lemma collineation_12326 : is_collineation fp_12326 fl_12326.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12326 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12326 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12326.

Lemma collineation_12327 : is_collineation fp_12327 fl_12327.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12327 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12327 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12327.

Lemma collineation_12328 : is_collineation fp_12328 fl_12328.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12328 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12328 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12328.

Lemma collineation_12329 : is_collineation fp_12329 fl_12329.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12329 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12329 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12329.

Lemma collineation_12330 : is_collineation fp_12330 fl_12330.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12330 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12330 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12330.

Lemma collineation_12331 : is_collineation fp_12331 fl_12331.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12331 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12331 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12331.

Lemma collineation_12332 : is_collineation fp_12332 fl_12332.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12332 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12332 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12332.

Lemma collineation_12333 : is_collineation fp_12333 fl_12333.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12333 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12333 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12333.

Lemma collineation_12334 : is_collineation fp_12334 fl_12334.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12334 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12334 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12334.

Lemma collineation_12335 : is_collineation fp_12335 fl_12335.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12335 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12335 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12335.

Lemma collineation_12336 : is_collineation fp_12336 fl_12336.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12336 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12336 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12336.

Lemma collineation_12337 : is_collineation fp_12337 fl_12337.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12337 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12337 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12337.

Lemma collineation_12338 : is_collineation fp_12338 fl_12338.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12338 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12338 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12338.

Lemma collineation_12339 : is_collineation fp_12339 fl_12339.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12339 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12339 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12339.

Lemma collineation_12340 : is_collineation fp_12340 fl_12340.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12340 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12340 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12340.

Lemma collineation_12341 : is_collineation fp_12341 fl_12341.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12341 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12341 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12341.

Lemma collineation_12342 : is_collineation fp_12342 fl_12342.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12342 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12342 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12342.

Lemma collineation_12343 : is_collineation fp_12343 fl_12343.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12343 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12343 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12343.

Lemma collineation_12344 : is_collineation fp_12344 fl_12344.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12344 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12344 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12344.

Lemma collineation_12345 : is_collineation fp_12345 fl_12345.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12345 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12345 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12345.

Lemma collineation_12346 : is_collineation fp_12346 fl_12346.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12346 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12346 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12346.

Lemma collineation_12347 : is_collineation fp_12347 fl_12347.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12347 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12347 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12347.

Lemma collineation_12348 : is_collineation fp_12348 fl_12348.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12348 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12348 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12348.

Lemma collineation_12349 : is_collineation fp_12349 fl_12349.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12349 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12349 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12349.

Lemma collineation_12350 : is_collineation fp_12350 fl_12350.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12350 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12350 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12350.

Lemma collineation_12351 : is_collineation fp_12351 fl_12351.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12351 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12351 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12351.

Lemma collineation_12352 : is_collineation fp_12352 fl_12352.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12352 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12352 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12352.

Lemma collineation_12353 : is_collineation fp_12353 fl_12353.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12353 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12353 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12353.

Lemma collineation_12354 : is_collineation fp_12354 fl_12354.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12354 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12354 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12354.

Lemma collineation_12355 : is_collineation fp_12355 fl_12355.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12355 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12355 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12355.

Lemma collineation_12356 : is_collineation fp_12356 fl_12356.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12356 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12356 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12356.

Lemma collineation_12357 : is_collineation fp_12357 fl_12357.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12357 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12357 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12357.

Lemma collineation_12358 : is_collineation fp_12358 fl_12358.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12358 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12358 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12358.

Lemma collineation_12359 : is_collineation fp_12359 fl_12359.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12359 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12359 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12359.

Lemma collineation_12360 : is_collineation fp_12360 fl_12360.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12360 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12360 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12360.

Lemma collineation_12361 : is_collineation fp_12361 fl_12361.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12361 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12361 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12361.

Lemma collineation_12362 : is_collineation fp_12362 fl_12362.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12362 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12362 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12362.

Lemma collineation_12363 : is_collineation fp_12363 fl_12363.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12363 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12363 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12363.

Lemma collineation_12364 : is_collineation fp_12364 fl_12364.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12364 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12364 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12364.

Lemma collineation_12365 : is_collineation fp_12365 fl_12365.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12365 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12365 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12365.

Lemma collineation_12366 : is_collineation fp_12366 fl_12366.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12366 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12366 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12366.

Lemma collineation_12367 : is_collineation fp_12367 fl_12367.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12367 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12367 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12367.

Lemma collineation_12368 : is_collineation fp_12368 fl_12368.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12368 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12368 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12368.

Lemma collineation_12369 : is_collineation fp_12369 fl_12369.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12369 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12369 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12369.

Lemma collineation_12370 : is_collineation fp_12370 fl_12370.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12370 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12370 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12370.

Lemma collineation_12371 : is_collineation fp_12371 fl_12371.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12371 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12371 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12371.

Lemma collineation_12372 : is_collineation fp_12372 fl_12372.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12372 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12372 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12372.

Lemma collineation_12373 : is_collineation fp_12373 fl_12373.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12373 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12373 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12373.

Lemma collineation_12374 : is_collineation fp_12374 fl_12374.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12374 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12374 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12374.

Lemma collineation_12375 : is_collineation fp_12375 fl_12375.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12375 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12375 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12375.

Lemma collineation_12376 : is_collineation fp_12376 fl_12376.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12376 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12376 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12376.

Lemma collineation_12377 : is_collineation fp_12377 fl_12377.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12377 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12377 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12377.

Lemma collineation_12378 : is_collineation fp_12378 fl_12378.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12378 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12378 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12378.

Lemma collineation_12379 : is_collineation fp_12379 fl_12379.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12379 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12379 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12379.

Lemma collineation_12380 : is_collineation fp_12380 fl_12380.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12380 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12380 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12380.

Lemma collineation_12381 : is_collineation fp_12381 fl_12381.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12381 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12381 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12381.

Lemma collineation_12382 : is_collineation fp_12382 fl_12382.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12382 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12382 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12382.

Lemma collineation_12383 : is_collineation fp_12383 fl_12383.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12383 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12383 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12383.

Lemma collineation_12384 : is_collineation fp_12384 fl_12384.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12384 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12384 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12384.

Lemma collineation_12385 : is_collineation fp_12385 fl_12385.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12385 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12385 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12385.

Lemma collineation_12386 : is_collineation fp_12386 fl_12386.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12386 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12386 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12386.

Lemma collineation_12387 : is_collineation fp_12387 fl_12387.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12387 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12387 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12387.

Lemma collineation_12388 : is_collineation fp_12388 fl_12388.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12388 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12388 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12388.

Lemma collineation_12389 : is_collineation fp_12389 fl_12389.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12389 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12389 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12389.

Lemma collineation_12390 : is_collineation fp_12390 fl_12390.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12390 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12390 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12390.

Lemma collineation_12391 : is_collineation fp_12391 fl_12391.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12391 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12391 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12391.

Lemma collineation_12392 : is_collineation fp_12392 fl_12392.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12392 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12392 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12392.

Lemma collineation_12393 : is_collineation fp_12393 fl_12393.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12393 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12393 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12393.

Lemma collineation_12394 : is_collineation fp_12394 fl_12394.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12394 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12394 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12394.

Lemma collineation_12395 : is_collineation fp_12395 fl_12395.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12395 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12395 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12395.

Lemma collineation_12396 : is_collineation fp_12396 fl_12396.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12396 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12396 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12396.

Lemma collineation_12397 : is_collineation fp_12397 fl_12397.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12397 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12397 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12397.

Lemma collineation_12398 : is_collineation fp_12398 fl_12398.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12398 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12398 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12398.

Lemma collineation_12399 : is_collineation fp_12399 fl_12399.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12399 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12399 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12399.

Lemma collineation_12400 : is_collineation fp_12400 fl_12400.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12400 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12400 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12400.

Lemma collineation_12401 : is_collineation fp_12401 fl_12401.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12401 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12401 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12401.

Lemma collineation_12402 : is_collineation fp_12402 fl_12402.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12402 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12402 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12402.

Lemma collineation_12403 : is_collineation fp_12403 fl_12403.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12403 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12403 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12403.

Lemma collineation_12404 : is_collineation fp_12404 fl_12404.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12404 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12404 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12404.

Lemma collineation_12405 : is_collineation fp_12405 fl_12405.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12405 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12405 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12405.

Lemma collineation_12406 : is_collineation fp_12406 fl_12406.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12406 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12406 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12406.

Lemma collineation_12407 : is_collineation fp_12407 fl_12407.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12407 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12407 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12407.

Lemma collineation_12408 : is_collineation fp_12408 fl_12408.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12408 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12408 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12408.

Lemma collineation_12409 : is_collineation fp_12409 fl_12409.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12409 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12409 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12409.

Lemma collineation_12410 : is_collineation fp_12410 fl_12410.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12410 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12410 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12410.

Lemma collineation_12411 : is_collineation fp_12411 fl_12411.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12411 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12411 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12411.

Lemma collineation_12412 : is_collineation fp_12412 fl_12412.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12412 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12412 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12412.

Lemma collineation_12413 : is_collineation fp_12413 fl_12413.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12413 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12413 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12413.

Lemma collineation_12414 : is_collineation fp_12414 fl_12414.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12414 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12414 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12414.

Lemma collineation_12415 : is_collineation fp_12415 fl_12415.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12415 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12415 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12415.

Lemma collineation_12416 : is_collineation fp_12416 fl_12416.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12416 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12416 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12416.

Lemma collineation_12417 : is_collineation fp_12417 fl_12417.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12417 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12417 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12417.

Lemma collineation_12418 : is_collineation fp_12418 fl_12418.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12418 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12418 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12418.

Lemma collineation_12419 : is_collineation fp_12419 fl_12419.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12419 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12419 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12419.

Lemma collineation_12420 : is_collineation fp_12420 fl_12420.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12420 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12420 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12420.

Lemma collineation_12421 : is_collineation fp_12421 fl_12421.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12421 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12421 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12421.

Lemma collineation_12422 : is_collineation fp_12422 fl_12422.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12422 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12422 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12422.

Lemma collineation_12423 : is_collineation fp_12423 fl_12423.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12423 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12423 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12423.

Lemma collineation_12424 : is_collineation fp_12424 fl_12424.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12424 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12424 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12424.

Lemma collineation_12425 : is_collineation fp_12425 fl_12425.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12425 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12425 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12425.

Lemma collineation_12426 : is_collineation fp_12426 fl_12426.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12426 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12426 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12426.

Lemma collineation_12427 : is_collineation fp_12427 fl_12427.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12427 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12427 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12427.

Lemma collineation_12428 : is_collineation fp_12428 fl_12428.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12428 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12428 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12428.

Lemma collineation_12429 : is_collineation fp_12429 fl_12429.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12429 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12429 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12429.

Lemma collineation_12430 : is_collineation fp_12430 fl_12430.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12430 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12430 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12430.

Lemma collineation_12431 : is_collineation fp_12431 fl_12431.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12431 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12431 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12431.

Lemma collineation_12432 : is_collineation fp_12432 fl_12432.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12432 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12432 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12432.

Lemma collineation_12433 : is_collineation fp_12433 fl_12433.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12433 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12433 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12433.

Lemma collineation_12434 : is_collineation fp_12434 fl_12434.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12434 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12434 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12434.

Lemma collineation_12435 : is_collineation fp_12435 fl_12435.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12435 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12435 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12435.

Lemma collineation_12436 : is_collineation fp_12436 fl_12436.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12436 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12436 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12436.

Lemma collineation_12437 : is_collineation fp_12437 fl_12437.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12437 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12437 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12437.

Lemma collineation_12438 : is_collineation fp_12438 fl_12438.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12438 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12438 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12438.

Lemma collineation_12439 : is_collineation fp_12439 fl_12439.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12439 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12439 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12439.

Lemma collineation_12440 : is_collineation fp_12440 fl_12440.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12440 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12440 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12440.

Lemma collineation_12441 : is_collineation fp_12441 fl_12441.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12441 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12441 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12441.

Lemma collineation_12442 : is_collineation fp_12442 fl_12442.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12442 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12442 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12442.

Lemma collineation_12443 : is_collineation fp_12443 fl_12443.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12443 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12443 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12443.

Lemma collineation_12444 : is_collineation fp_12444 fl_12444.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12444 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12444 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12444.

Lemma collineation_12445 : is_collineation fp_12445 fl_12445.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12445 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12445 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12445.

Lemma collineation_12446 : is_collineation fp_12446 fl_12446.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12446 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12446 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12446.

Lemma collineation_12447 : is_collineation fp_12447 fl_12447.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12447 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12447 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12447.

Lemma collineation_12448 : is_collineation fp_12448 fl_12448.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12448 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12448 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12448.

Lemma collineation_12449 : is_collineation fp_12449 fl_12449.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12449 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12449 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12449.

Lemma collineation_12450 : is_collineation fp_12450 fl_12450.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12450 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12450 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12450.

Lemma collineation_12451 : is_collineation fp_12451 fl_12451.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12451 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12451 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12451.

Lemma collineation_12452 : is_collineation fp_12452 fl_12452.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12452 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12452 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12452.

Lemma collineation_12453 : is_collineation fp_12453 fl_12453.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12453 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12453 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12453.

Lemma collineation_12454 : is_collineation fp_12454 fl_12454.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12454 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12454 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12454.

Lemma collineation_12455 : is_collineation fp_12455 fl_12455.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12455 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12455 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12455.

Lemma collineation_12456 : is_collineation fp_12456 fl_12456.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12456 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12456 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12456.

Lemma collineation_12457 : is_collineation fp_12457 fl_12457.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12457 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12457 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12457.

Lemma collineation_12458 : is_collineation fp_12458 fl_12458.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12458 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12458 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12458.

Lemma collineation_12459 : is_collineation fp_12459 fl_12459.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12459 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12459 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12459.

Lemma collineation_12460 : is_collineation fp_12460 fl_12460.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12460 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12460 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12460.

Lemma collineation_12461 : is_collineation fp_12461 fl_12461.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12461 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12461 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12461.

Lemma collineation_12462 : is_collineation fp_12462 fl_12462.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12462 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12462 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12462.

Lemma collineation_12463 : is_collineation fp_12463 fl_12463.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12463 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12463 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12463.

Lemma collineation_12464 : is_collineation fp_12464 fl_12464.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12464 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12464 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12464.

Lemma collineation_12465 : is_collineation fp_12465 fl_12465.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12465 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12465 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12465.

Lemma collineation_12466 : is_collineation fp_12466 fl_12466.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12466 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12466 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12466.

Lemma collineation_12467 : is_collineation fp_12467 fl_12467.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12467 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12467 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12467.

Lemma collineation_12468 : is_collineation fp_12468 fl_12468.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12468 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12468 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12468.

Lemma collineation_12469 : is_collineation fp_12469 fl_12469.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12469 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12469 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12469.

Lemma collineation_12470 : is_collineation fp_12470 fl_12470.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12470 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12470 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12470.

Lemma collineation_12471 : is_collineation fp_12471 fl_12471.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12471 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12471 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12471.

Lemma collineation_12472 : is_collineation fp_12472 fl_12472.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12472 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12472 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12472.

Lemma collineation_12473 : is_collineation fp_12473 fl_12473.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12473 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12473 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12473.

Lemma collineation_12474 : is_collineation fp_12474 fl_12474.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12474 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12474 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12474.

Lemma collineation_12475 : is_collineation fp_12475 fl_12475.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12475 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12475 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12475.

Lemma collineation_12476 : is_collineation fp_12476 fl_12476.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12476 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12476 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12476.

Lemma collineation_12477 : is_collineation fp_12477 fl_12477.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12477 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12477 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12477.

Lemma collineation_12478 : is_collineation fp_12478 fl_12478.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12478 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12478 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12478.

Lemma collineation_12479 : is_collineation fp_12479 fl_12479.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12479 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12479 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12479.

Lemma collineation_12480 : is_collineation fp_12480 fl_12480.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12480 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12480 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12480.

Lemma collineation_12481 : is_collineation fp_12481 fl_12481.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12481 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12481 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12481.

Lemma collineation_12482 : is_collineation fp_12482 fl_12482.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12482 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12482 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12482.

Lemma collineation_12483 : is_collineation fp_12483 fl_12483.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12483 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12483 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12483.

Lemma collineation_12484 : is_collineation fp_12484 fl_12484.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12484 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12484 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12484.

Lemma collineation_12485 : is_collineation fp_12485 fl_12485.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12485 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12485 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12485.

Lemma collineation_12486 : is_collineation fp_12486 fl_12486.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12486 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12486 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12486.

Lemma collineation_12487 : is_collineation fp_12487 fl_12487.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12487 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12487 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12487.

Lemma collineation_12488 : is_collineation fp_12488 fl_12488.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12488 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12488 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12488.

Lemma collineation_12489 : is_collineation fp_12489 fl_12489.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12489 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12489 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12489.

Lemma collineation_12490 : is_collineation fp_12490 fl_12490.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12490 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12490 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12490.

Lemma collineation_12491 : is_collineation fp_12491 fl_12491.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12491 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12491 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12491.

Lemma collineation_12492 : is_collineation fp_12492 fl_12492.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12492 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12492 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12492.

Lemma collineation_12493 : is_collineation fp_12493 fl_12493.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12493 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12493 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12493.

Lemma collineation_12494 : is_collineation fp_12494 fl_12494.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12494 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12494 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12494.

Lemma collineation_12495 : is_collineation fp_12495 fl_12495.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12495 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12495 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12495.

Lemma collineation_12496 : is_collineation fp_12496 fl_12496.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12496 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12496 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12496.

Lemma collineation_12497 : is_collineation fp_12497 fl_12497.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12497 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12497 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12497.

Lemma collineation_12498 : is_collineation fp_12498 fl_12498.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12498 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12498 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12498.

Lemma collineation_12499 : is_collineation fp_12499 fl_12499.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12499 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12499 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12499.

Lemma collineation_12500 : is_collineation fp_12500 fl_12500.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12500 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12500 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12500.

Lemma collineation_12501 : is_collineation fp_12501 fl_12501.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12501 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12501 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12501.

Lemma collineation_12502 : is_collineation fp_12502 fl_12502.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12502 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12502 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12502.

Lemma collineation_12503 : is_collineation fp_12503 fl_12503.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12503 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12503 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12503.

Lemma collineation_12504 : is_collineation fp_12504 fl_12504.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12504 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12504 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12504.

Lemma collineation_12505 : is_collineation fp_12505 fl_12505.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12505 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12505 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12505.

Lemma collineation_12506 : is_collineation fp_12506 fl_12506.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12506 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12506 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12506.

Lemma collineation_12507 : is_collineation fp_12507 fl_12507.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12507 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12507 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12507.

Lemma collineation_12508 : is_collineation fp_12508 fl_12508.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12508 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12508 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12508.

Lemma collineation_12509 : is_collineation fp_12509 fl_12509.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12509 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12509 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12509.

Lemma collineation_12510 : is_collineation fp_12510 fl_12510.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12510 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12510 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12510.

Lemma collineation_12511 : is_collineation fp_12511 fl_12511.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12511 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12511 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12511.

Lemma collineation_12512 : is_collineation fp_12512 fl_12512.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12512 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12512 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12512.

Lemma collineation_12513 : is_collineation fp_12513 fl_12513.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12513 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12513 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12513.

Lemma collineation_12514 : is_collineation fp_12514 fl_12514.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12514 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12514 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12514.

Lemma collineation_12515 : is_collineation fp_12515 fl_12515.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12515 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12515 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12515.

Lemma collineation_12516 : is_collineation fp_12516 fl_12516.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12516 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12516 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12516.

Lemma collineation_12517 : is_collineation fp_12517 fl_12517.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12517 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12517 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12517.

Lemma collineation_12518 : is_collineation fp_12518 fl_12518.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12518 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12518 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12518.

Lemma collineation_12519 : is_collineation fp_12519 fl_12519.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12519 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12519 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12519.

Lemma collineation_12520 : is_collineation fp_12520 fl_12520.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12520 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12520 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12520.

Lemma collineation_12521 : is_collineation fp_12521 fl_12521.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12521 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12521 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12521.

Lemma collineation_12522 : is_collineation fp_12522 fl_12522.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12522 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12522 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12522.

Lemma collineation_12523 : is_collineation fp_12523 fl_12523.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12523 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12523 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12523.

Lemma collineation_12524 : is_collineation fp_12524 fl_12524.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12524 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12524 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12524.

Lemma collineation_12525 : is_collineation fp_12525 fl_12525.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12525 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12525 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12525.

Lemma collineation_12526 : is_collineation fp_12526 fl_12526.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12526 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12526 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12526.

Lemma collineation_12527 : is_collineation fp_12527 fl_12527.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12527 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12527 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12527.

Lemma collineation_12528 : is_collineation fp_12528 fl_12528.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12528 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12528 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12528.

Lemma collineation_12529 : is_collineation fp_12529 fl_12529.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12529 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12529 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12529.

Lemma collineation_12530 : is_collineation fp_12530 fl_12530.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12530 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12530 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12530.

Lemma collineation_12531 : is_collineation fp_12531 fl_12531.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12531 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12531 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12531.

Lemma collineation_12532 : is_collineation fp_12532 fl_12532.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12532 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12532 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12532.

Lemma collineation_12533 : is_collineation fp_12533 fl_12533.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12533 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12533 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12533.

Lemma collineation_12534 : is_collineation fp_12534 fl_12534.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12534 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12534 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12534.

Lemma collineation_12535 : is_collineation fp_12535 fl_12535.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12535 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12535 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12535.

Lemma collineation_12536 : is_collineation fp_12536 fl_12536.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12536 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12536 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12536.

Lemma collineation_12537 : is_collineation fp_12537 fl_12537.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12537 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12537 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12537.

Lemma collineation_12538 : is_collineation fp_12538 fl_12538.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12538 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12538 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12538.

Lemma collineation_12539 : is_collineation fp_12539 fl_12539.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12539 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12539 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12539.

Lemma collineation_12540 : is_collineation fp_12540 fl_12540.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12540 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12540 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12540.

Lemma collineation_12541 : is_collineation fp_12541 fl_12541.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12541 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12541 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12541.

Lemma collineation_12542 : is_collineation fp_12542 fl_12542.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12542 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12542 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12542.

Lemma collineation_12543 : is_collineation fp_12543 fl_12543.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12543 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12543 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12543.

Lemma collineation_12544 : is_collineation fp_12544 fl_12544.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12544 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12544 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12544.

Lemma collineation_12545 : is_collineation fp_12545 fl_12545.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12545 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12545 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12545.

Lemma collineation_12546 : is_collineation fp_12546 fl_12546.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12546 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12546 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12546.

Lemma collineation_12547 : is_collineation fp_12547 fl_12547.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12547 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12547 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12547.

Lemma collineation_12548 : is_collineation fp_12548 fl_12548.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12548 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12548 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12548.

Lemma collineation_12549 : is_collineation fp_12549 fl_12549.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12549 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12549 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12549.

Lemma collineation_12550 : is_collineation fp_12550 fl_12550.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12550 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12550 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12550.

Lemma collineation_12551 : is_collineation fp_12551 fl_12551.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12551 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12551 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12551.

Lemma collineation_12552 : is_collineation fp_12552 fl_12552.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12552 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12552 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12552.

Lemma collineation_12553 : is_collineation fp_12553 fl_12553.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12553 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12553 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12553.

Lemma collineation_12554 : is_collineation fp_12554 fl_12554.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12554 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12554 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12554.

Lemma collineation_12555 : is_collineation fp_12555 fl_12555.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12555 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12555 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12555.

Lemma collineation_12556 : is_collineation fp_12556 fl_12556.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12556 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12556 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12556.

Lemma collineation_12557 : is_collineation fp_12557 fl_12557.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12557 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12557 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12557.

Lemma collineation_12558 : is_collineation fp_12558 fl_12558.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12558 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12558 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12558.

Lemma collineation_12559 : is_collineation fp_12559 fl_12559.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12559 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12559 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12559.

Lemma collineation_12560 : is_collineation fp_12560 fl_12560.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12560 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12560 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12560.

Lemma collineation_12561 : is_collineation fp_12561 fl_12561.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12561 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12561 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12561.

Lemma collineation_12562 : is_collineation fp_12562 fl_12562.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12562 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12562 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12562.

Lemma collineation_12563 : is_collineation fp_12563 fl_12563.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12563 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12563 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12563.

Lemma collineation_12564 : is_collineation fp_12564 fl_12564.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12564 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12564 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12564.

Lemma collineation_12565 : is_collineation fp_12565 fl_12565.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12565 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12565 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12565.

Lemma collineation_12566 : is_collineation fp_12566 fl_12566.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12566 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12566 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12566.

Lemma collineation_12567 : is_collineation fp_12567 fl_12567.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12567 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12567 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12567.

Lemma collineation_12568 : is_collineation fp_12568 fl_12568.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12568 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12568 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12568.

Lemma collineation_12569 : is_collineation fp_12569 fl_12569.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12569 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12569 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12569.

Lemma collineation_12570 : is_collineation fp_12570 fl_12570.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12570 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12570 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12570.

Lemma collineation_12571 : is_collineation fp_12571 fl_12571.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12571 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12571 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12571.

Lemma collineation_12572 : is_collineation fp_12572 fl_12572.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12572 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12572 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12572.

Lemma collineation_12573 : is_collineation fp_12573 fl_12573.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12573 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12573 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12573.

Lemma collineation_12574 : is_collineation fp_12574 fl_12574.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12574 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12574 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12574.

Lemma collineation_12575 : is_collineation fp_12575 fl_12575.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12575 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12575 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12575.

Lemma collineation_12576 : is_collineation fp_12576 fl_12576.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12576 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12576 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12576.

Lemma collineation_12577 : is_collineation fp_12577 fl_12577.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12577 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12577 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12577.

Lemma collineation_12578 : is_collineation fp_12578 fl_12578.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12578 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12578 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12578.

Lemma collineation_12579 : is_collineation fp_12579 fl_12579.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12579 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12579 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12579.

Lemma collineation_12580 : is_collineation fp_12580 fl_12580.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12580 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12580 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12580.

Lemma collineation_12581 : is_collineation fp_12581 fl_12581.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12581 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12581 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12581.

Lemma collineation_12582 : is_collineation fp_12582 fl_12582.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12582 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12582 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12582.

Lemma collineation_12583 : is_collineation fp_12583 fl_12583.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12583 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12583 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12583.

Lemma collineation_12584 : is_collineation fp_12584 fl_12584.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12584 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12584 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12584.

Lemma collineation_12585 : is_collineation fp_12585 fl_12585.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12585 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12585 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12585.

Lemma collineation_12586 : is_collineation fp_12586 fl_12586.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12586 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12586 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12586.

Lemma collineation_12587 : is_collineation fp_12587 fl_12587.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12587 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12587 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12587.

Lemma collineation_12588 : is_collineation fp_12588 fl_12588.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12588 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12588 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12588.

Lemma collineation_12589 : is_collineation fp_12589 fl_12589.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12589 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12589 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12589.

Lemma collineation_12590 : is_collineation fp_12590 fl_12590.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12590 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12590 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12590.

Lemma collineation_12591 : is_collineation fp_12591 fl_12591.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12591 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12591 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12591.

Lemma collineation_12592 : is_collineation fp_12592 fl_12592.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12592 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12592 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12592.

Lemma collineation_12593 : is_collineation fp_12593 fl_12593.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12593 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12593 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12593.

Lemma collineation_12594 : is_collineation fp_12594 fl_12594.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12594 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12594 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12594.

Lemma collineation_12595 : is_collineation fp_12595 fl_12595.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12595 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12595 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12595.

Lemma collineation_12596 : is_collineation fp_12596 fl_12596.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12596 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12596 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12596.

Lemma collineation_12597 : is_collineation fp_12597 fl_12597.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12597 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12597 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12597.

Lemma collineation_12598 : is_collineation fp_12598 fl_12598.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12598 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12598 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12598.

Lemma collineation_12599 : is_collineation fp_12599 fl_12599.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12599 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12599 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12599.

Lemma collineation_12600 : is_collineation fp_12600 fl_12600.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12600 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12600 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12600.

Lemma collineation_12601 : is_collineation fp_12601 fl_12601.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12601 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12601 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12601.

Lemma collineation_12602 : is_collineation fp_12602 fl_12602.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12602 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12602 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12602.

Lemma collineation_12603 : is_collineation fp_12603 fl_12603.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12603 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12603 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12603.

Lemma collineation_12604 : is_collineation fp_12604 fl_12604.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12604 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12604 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12604.

Lemma collineation_12605 : is_collineation fp_12605 fl_12605.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12605 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12605 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12605.

Lemma collineation_12606 : is_collineation fp_12606 fl_12606.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12606 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12606 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12606.

Lemma collineation_12607 : is_collineation fp_12607 fl_12607.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12607 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12607 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12607.

Lemma collineation_12608 : is_collineation fp_12608 fl_12608.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12608 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12608 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12608.

Lemma collineation_12609 : is_collineation fp_12609 fl_12609.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12609 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12609 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12609.

Lemma collineation_12610 : is_collineation fp_12610 fl_12610.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12610 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12610 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12610.

Lemma collineation_12611 : is_collineation fp_12611 fl_12611.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12611 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12611 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12611.

Lemma collineation_12612 : is_collineation fp_12612 fl_12612.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12612 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12612 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12612.

Lemma collineation_12613 : is_collineation fp_12613 fl_12613.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12613 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12613 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12613.

Lemma collineation_12614 : is_collineation fp_12614 fl_12614.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12614 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12614 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12614.

Lemma collineation_12615 : is_collineation fp_12615 fl_12615.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12615 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12615 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12615.

Lemma collineation_12616 : is_collineation fp_12616 fl_12616.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12616 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12616 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12616.

Lemma collineation_12617 : is_collineation fp_12617 fl_12617.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12617 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12617 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12617.

Lemma collineation_12618 : is_collineation fp_12618 fl_12618.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12618 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12618 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12618.

Lemma collineation_12619 : is_collineation fp_12619 fl_12619.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12619 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12619 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12619.

Lemma collineation_12620 : is_collineation fp_12620 fl_12620.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12620 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12620 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12620.

Lemma collineation_12621 : is_collineation fp_12621 fl_12621.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12621 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12621 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12621.

Lemma collineation_12622 : is_collineation fp_12622 fl_12622.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12622 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12622 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12622.

Lemma collineation_12623 : is_collineation fp_12623 fl_12623.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12623 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12623 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12623.

Lemma collineation_12624 : is_collineation fp_12624 fl_12624.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12624 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12624 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12624.

Lemma collineation_12625 : is_collineation fp_12625 fl_12625.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12625 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12625 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12625.

Lemma collineation_12626 : is_collineation fp_12626 fl_12626.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12626 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12626 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12626.

Lemma collineation_12627 : is_collineation fp_12627 fl_12627.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12627 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12627 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12627.

Lemma collineation_12628 : is_collineation fp_12628 fl_12628.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12628 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12628 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12628.

Lemma collineation_12629 : is_collineation fp_12629 fl_12629.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12629 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12629 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12629.

Lemma collineation_12630 : is_collineation fp_12630 fl_12630.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12630 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12630 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12630.

Lemma collineation_12631 : is_collineation fp_12631 fl_12631.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12631 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12631 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12631.

Lemma collineation_12632 : is_collineation fp_12632 fl_12632.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12632 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12632 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12632.

Lemma collineation_12633 : is_collineation fp_12633 fl_12633.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12633 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12633 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12633.

Lemma collineation_12634 : is_collineation fp_12634 fl_12634.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12634 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12634 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12634.

Lemma collineation_12635 : is_collineation fp_12635 fl_12635.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12635 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12635 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12635.

Lemma collineation_12636 : is_collineation fp_12636 fl_12636.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12636 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12636 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12636.

Lemma collineation_12637 : is_collineation fp_12637 fl_12637.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12637 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12637 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12637.

Lemma collineation_12638 : is_collineation fp_12638 fl_12638.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12638 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12638 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12638.

Lemma collineation_12639 : is_collineation fp_12639 fl_12639.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12639 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12639 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12639.

Lemma collineation_12640 : is_collineation fp_12640 fl_12640.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12640 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12640 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12640.

Lemma collineation_12641 : is_collineation fp_12641 fl_12641.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12641 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12641 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12641.

Lemma collineation_12642 : is_collineation fp_12642 fl_12642.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12642 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12642 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12642.

Lemma collineation_12643 : is_collineation fp_12643 fl_12643.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12643 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12643 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12643.

Lemma collineation_12644 : is_collineation fp_12644 fl_12644.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12644 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12644 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12644.

Lemma collineation_12645 : is_collineation fp_12645 fl_12645.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12645 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12645 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12645.

Lemma collineation_12646 : is_collineation fp_12646 fl_12646.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12646 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12646 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12646.

Lemma collineation_12647 : is_collineation fp_12647 fl_12647.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12647 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12647 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12647.

Lemma collineation_12648 : is_collineation fp_12648 fl_12648.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12648 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12648 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12648.

Lemma collineation_12649 : is_collineation fp_12649 fl_12649.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12649 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12649 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12649.

Lemma collineation_12650 : is_collineation fp_12650 fl_12650.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12650 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12650 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12650.

Lemma collineation_12651 : is_collineation fp_12651 fl_12651.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12651 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12651 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12651.

Lemma collineation_12652 : is_collineation fp_12652 fl_12652.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12652 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12652 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12652.

Lemma collineation_12653 : is_collineation fp_12653 fl_12653.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12653 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12653 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12653.

Lemma collineation_12654 : is_collineation fp_12654 fl_12654.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12654 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12654 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12654.

Lemma collineation_12655 : is_collineation fp_12655 fl_12655.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12655 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12655 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12655.

Lemma collineation_12656 : is_collineation fp_12656 fl_12656.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12656 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12656 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12656.

Lemma collineation_12657 : is_collineation fp_12657 fl_12657.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12657 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12657 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12657.

Lemma collineation_12658 : is_collineation fp_12658 fl_12658.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12658 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12658 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12658.

Lemma collineation_12659 : is_collineation fp_12659 fl_12659.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12659 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12659 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12659.

Lemma collineation_12660 : is_collineation fp_12660 fl_12660.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12660 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12660 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12660.

Lemma collineation_12661 : is_collineation fp_12661 fl_12661.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12661 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12661 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12661.

Lemma collineation_12662 : is_collineation fp_12662 fl_12662.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12662 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12662 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12662.

Lemma collineation_12663 : is_collineation fp_12663 fl_12663.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12663 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12663 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12663.

Lemma collineation_12664 : is_collineation fp_12664 fl_12664.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12664 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12664 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12664.

Lemma collineation_12665 : is_collineation fp_12665 fl_12665.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12665 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12665 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12665.

Lemma collineation_12666 : is_collineation fp_12666 fl_12666.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12666 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12666 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12666.

Lemma collineation_12667 : is_collineation fp_12667 fl_12667.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12667 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12667 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12667.

Lemma collineation_12668 : is_collineation fp_12668 fl_12668.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12668 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12668 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12668.

Lemma collineation_12669 : is_collineation fp_12669 fl_12669.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12669 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12669 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12669.

Lemma collineation_12670 : is_collineation fp_12670 fl_12670.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12670 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12670 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12670.

Lemma collineation_12671 : is_collineation fp_12671 fl_12671.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12671 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12671 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12671.

Lemma collineation_12672 : is_collineation fp_12672 fl_12672.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12672 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12672 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12672.

Lemma collineation_12673 : is_collineation fp_12673 fl_12673.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12673 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12673 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12673.

Lemma collineation_12674 : is_collineation fp_12674 fl_12674.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12674 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12674 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12674.

Lemma collineation_12675 : is_collineation fp_12675 fl_12675.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12675 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12675 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12675.

Lemma collineation_12676 : is_collineation fp_12676 fl_12676.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12676 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12676 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12676.

Lemma collineation_12677 : is_collineation fp_12677 fl_12677.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12677 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12677 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12677.

Lemma collineation_12678 : is_collineation fp_12678 fl_12678.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12678 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12678 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12678.

Lemma collineation_12679 : is_collineation fp_12679 fl_12679.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12679 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12679 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12679.

Lemma collineation_12680 : is_collineation fp_12680 fl_12680.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12680 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12680 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12680.

Lemma collineation_12681 : is_collineation fp_12681 fl_12681.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12681 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12681 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12681.

Lemma collineation_12682 : is_collineation fp_12682 fl_12682.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12682 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12682 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12682.

Lemma collineation_12683 : is_collineation fp_12683 fl_12683.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12683 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12683 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12683.

Lemma collineation_12684 : is_collineation fp_12684 fl_12684.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12684 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12684 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12684.

Lemma collineation_12685 : is_collineation fp_12685 fl_12685.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12685 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12685 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12685.

Lemma collineation_12686 : is_collineation fp_12686 fl_12686.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12686 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12686 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12686.

Lemma collineation_12687 : is_collineation fp_12687 fl_12687.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12687 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12687 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12687.

Lemma collineation_12688 : is_collineation fp_12688 fl_12688.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12688 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12688 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12688.

Lemma collineation_12689 : is_collineation fp_12689 fl_12689.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12689 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12689 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12689.

Lemma collineation_12690 : is_collineation fp_12690 fl_12690.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12690 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12690 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12690.

Lemma collineation_12691 : is_collineation fp_12691 fl_12691.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12691 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12691 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12691.

Lemma collineation_12692 : is_collineation fp_12692 fl_12692.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12692 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12692 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12692.

Lemma collineation_12693 : is_collineation fp_12693 fl_12693.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12693 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12693 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12693.

Lemma collineation_12694 : is_collineation fp_12694 fl_12694.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12694 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12694 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12694.

Lemma collineation_12695 : is_collineation fp_12695 fl_12695.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12695 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12695 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12695.

Lemma collineation_12696 : is_collineation fp_12696 fl_12696.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12696 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12696 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12696.

Lemma collineation_12697 : is_collineation fp_12697 fl_12697.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12697 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12697 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12697.

Lemma collineation_12698 : is_collineation fp_12698 fl_12698.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12698 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12698 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12698.

Lemma collineation_12699 : is_collineation fp_12699 fl_12699.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12699 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12699 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12699.

Lemma collineation_12700 : is_collineation fp_12700 fl_12700.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12700 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12700 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12700.

Lemma collineation_12701 : is_collineation fp_12701 fl_12701.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12701 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12701 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12701.

Lemma collineation_12702 : is_collineation fp_12702 fl_12702.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12702 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12702 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12702.

Lemma collineation_12703 : is_collineation fp_12703 fl_12703.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12703 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12703 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12703.

Lemma collineation_12704 : is_collineation fp_12704 fl_12704.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12704 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12704 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12704.

Lemma collineation_12705 : is_collineation fp_12705 fl_12705.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12705 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12705 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12705.

Lemma collineation_12706 : is_collineation fp_12706 fl_12706.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12706 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12706 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12706.

Lemma collineation_12707 : is_collineation fp_12707 fl_12707.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12707 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12707 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12707.

Lemma collineation_12708 : is_collineation fp_12708 fl_12708.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12708 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12708 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12708.

Lemma collineation_12709 : is_collineation fp_12709 fl_12709.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12709 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12709 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12709.

Lemma collineation_12710 : is_collineation fp_12710 fl_12710.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12710 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12710 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12710.

Lemma collineation_12711 : is_collineation fp_12711 fl_12711.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12711 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12711 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12711.

Lemma collineation_12712 : is_collineation fp_12712 fl_12712.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12712 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12712 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12712.

Lemma collineation_12713 : is_collineation fp_12713 fl_12713.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12713 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12713 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12713.

Lemma collineation_12714 : is_collineation fp_12714 fl_12714.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12714 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12714 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12714.

Lemma collineation_12715 : is_collineation fp_12715 fl_12715.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12715 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12715 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12715.

Lemma collineation_12716 : is_collineation fp_12716 fl_12716.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12716 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12716 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12716.

Lemma collineation_12717 : is_collineation fp_12717 fl_12717.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12717 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12717 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12717.

Lemma collineation_12718 : is_collineation fp_12718 fl_12718.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12718 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12718 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12718.

Lemma collineation_12719 : is_collineation fp_12719 fl_12719.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12719 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12719 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12719.

Lemma collineation_12720 : is_collineation fp_12720 fl_12720.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12720 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12720 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12720.

Lemma collineation_12721 : is_collineation fp_12721 fl_12721.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12721 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12721 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12721.

Lemma collineation_12722 : is_collineation fp_12722 fl_12722.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12722 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12722 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12722.

Lemma collineation_12723 : is_collineation fp_12723 fl_12723.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12723 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12723 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12723.

Lemma collineation_12724 : is_collineation fp_12724 fl_12724.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12724 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12724 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12724.

Lemma collineation_12725 : is_collineation fp_12725 fl_12725.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12725 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12725 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12725.

Lemma collineation_12726 : is_collineation fp_12726 fl_12726.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12726 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12726 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12726.

Lemma collineation_12727 : is_collineation fp_12727 fl_12727.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12727 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12727 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12727.

Lemma collineation_12728 : is_collineation fp_12728 fl_12728.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12728 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12728 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12728.

Lemma collineation_12729 : is_collineation fp_12729 fl_12729.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12729 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12729 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12729.

Lemma collineation_12730 : is_collineation fp_12730 fl_12730.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12730 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12730 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12730.

Lemma collineation_12731 : is_collineation fp_12731 fl_12731.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12731 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12731 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12731.

Lemma collineation_12732 : is_collineation fp_12732 fl_12732.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12732 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12732 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12732.

Lemma collineation_12733 : is_collineation fp_12733 fl_12733.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12733 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12733 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12733.

Lemma collineation_12734 : is_collineation fp_12734 fl_12734.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12734 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12734 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12734.

Lemma collineation_12735 : is_collineation fp_12735 fl_12735.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12735 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12735 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12735.

Lemma collineation_12736 : is_collineation fp_12736 fl_12736.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12736 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12736 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12736.

Lemma collineation_12737 : is_collineation fp_12737 fl_12737.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12737 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12737 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12737.

Lemma collineation_12738 : is_collineation fp_12738 fl_12738.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12738 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12738 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12738.

Lemma collineation_12739 : is_collineation fp_12739 fl_12739.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12739 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12739 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12739.

Lemma collineation_12740 : is_collineation fp_12740 fl_12740.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12740 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12740 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12740.

Lemma collineation_12741 : is_collineation fp_12741 fl_12741.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12741 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12741 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12741.

Lemma collineation_12742 : is_collineation fp_12742 fl_12742.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12742 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12742 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12742.

Lemma collineation_12743 : is_collineation fp_12743 fl_12743.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12743 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12743 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12743.

Lemma collineation_12744 : is_collineation fp_12744 fl_12744.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12744 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12744 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12744.

Lemma collineation_12745 : is_collineation fp_12745 fl_12745.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12745 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12745 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12745.

Lemma collineation_12746 : is_collineation fp_12746 fl_12746.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12746 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12746 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12746.

Lemma collineation_12747 : is_collineation fp_12747 fl_12747.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12747 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12747 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12747.

Lemma collineation_12748 : is_collineation fp_12748 fl_12748.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12748 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12748 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12748.

Lemma collineation_12749 : is_collineation fp_12749 fl_12749.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12749 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12749 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12749.

Lemma collineation_12750 : is_collineation fp_12750 fl_12750.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12750 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12750 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12750.

Lemma collineation_12751 : is_collineation fp_12751 fl_12751.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12751 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12751 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12751.

Lemma collineation_12752 : is_collineation fp_12752 fl_12752.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12752 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12752 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12752.

Lemma collineation_12753 : is_collineation fp_12753 fl_12753.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12753 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12753 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12753.

Lemma collineation_12754 : is_collineation fp_12754 fl_12754.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12754 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12754 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12754.

Lemma collineation_12755 : is_collineation fp_12755 fl_12755.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12755 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12755 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12755.

Lemma collineation_12756 : is_collineation fp_12756 fl_12756.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12756 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12756 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12756.

Lemma collineation_12757 : is_collineation fp_12757 fl_12757.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12757 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12757 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12757.

Lemma collineation_12758 : is_collineation fp_12758 fl_12758.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12758 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12758 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12758.

Lemma collineation_12759 : is_collineation fp_12759 fl_12759.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12759 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12759 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12759.

Lemma collineation_12760 : is_collineation fp_12760 fl_12760.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12760 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12760 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12760.

Lemma collineation_12761 : is_collineation fp_12761 fl_12761.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12761 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12761 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12761.

Lemma collineation_12762 : is_collineation fp_12762 fl_12762.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12762 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12762 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12762.

Lemma collineation_12763 : is_collineation fp_12763 fl_12763.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12763 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12763 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12763.

Lemma collineation_12764 : is_collineation fp_12764 fl_12764.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12764 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12764 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12764.

Lemma collineation_12765 : is_collineation fp_12765 fl_12765.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12765 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12765 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12765.

Lemma collineation_12766 : is_collineation fp_12766 fl_12766.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12766 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12766 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12766.

Lemma collineation_12767 : is_collineation fp_12767 fl_12767.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12767 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12767 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12767.

Lemma collineation_12768 : is_collineation fp_12768 fl_12768.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12768 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12768 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12768.

Lemma collineation_12769 : is_collineation fp_12769 fl_12769.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12769 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12769 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12769.

Lemma collineation_12770 : is_collineation fp_12770 fl_12770.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12770 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12770 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12770.

Lemma collineation_12771 : is_collineation fp_12771 fl_12771.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12771 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12771 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12771.

Lemma collineation_12772 : is_collineation fp_12772 fl_12772.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12772 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12772 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12772.

Lemma collineation_12773 : is_collineation fp_12773 fl_12773.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12773 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12773 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12773.

Lemma collineation_12774 : is_collineation fp_12774 fl_12774.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12774 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12774 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12774.

Lemma collineation_12775 : is_collineation fp_12775 fl_12775.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12775 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12775 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12775.

Lemma collineation_12776 : is_collineation fp_12776 fl_12776.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12776 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12776 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12776.

Lemma collineation_12777 : is_collineation fp_12777 fl_12777.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12777 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12777 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12777.

Lemma collineation_12778 : is_collineation fp_12778 fl_12778.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12778 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12778 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12778.

Lemma collineation_12779 : is_collineation fp_12779 fl_12779.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12779 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12779 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12779.

Lemma collineation_12780 : is_collineation fp_12780 fl_12780.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12780 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12780 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12780.

Lemma collineation_12781 : is_collineation fp_12781 fl_12781.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12781 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12781 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12781.

Lemma collineation_12782 : is_collineation fp_12782 fl_12782.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12782 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12782 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12782.

Lemma collineation_12783 : is_collineation fp_12783 fl_12783.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12783 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12783 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12783.

Lemma collineation_12784 : is_collineation fp_12784 fl_12784.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12784 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12784 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12784.

Lemma collineation_12785 : is_collineation fp_12785 fl_12785.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12785 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12785 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12785.

Lemma collineation_12786 : is_collineation fp_12786 fl_12786.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12786 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12786 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12786.

Lemma collineation_12787 : is_collineation fp_12787 fl_12787.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12787 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12787 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12787.

Lemma collineation_12788 : is_collineation fp_12788 fl_12788.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12788 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12788 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12788.

Lemma collineation_12789 : is_collineation fp_12789 fl_12789.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12789 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12789 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12789.

Lemma collineation_12790 : is_collineation fp_12790 fl_12790.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12790 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12790 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12790.

Lemma collineation_12791 : is_collineation fp_12791 fl_12791.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12791 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12791 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12791.

Lemma collineation_12792 : is_collineation fp_12792 fl_12792.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12792 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12792 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12792.

Lemma collineation_12793 : is_collineation fp_12793 fl_12793.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12793 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12793 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12793.

Lemma collineation_12794 : is_collineation fp_12794 fl_12794.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12794 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12794 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12794.

Lemma collineation_12795 : is_collineation fp_12795 fl_12795.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12795 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12795 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12795.

Lemma collineation_12796 : is_collineation fp_12796 fl_12796.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12796 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12796 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12796.

Lemma collineation_12797 : is_collineation fp_12797 fl_12797.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12797 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12797 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12797.

Lemma collineation_12798 : is_collineation fp_12798 fl_12798.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12798 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12798 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12798.

Lemma collineation_12799 : is_collineation fp_12799 fl_12799.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12799 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12799 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12799.

Lemma collineation_12800 : is_collineation fp_12800 fl_12800.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12800 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12800 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12800.

Lemma collineation_12801 : is_collineation fp_12801 fl_12801.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12801 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12801 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12801.

Lemma collineation_12802 : is_collineation fp_12802 fl_12802.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12802 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12802 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12802.

Lemma collineation_12803 : is_collineation fp_12803 fl_12803.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12803 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12803 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12803.

Lemma collineation_12804 : is_collineation fp_12804 fl_12804.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12804 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12804 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12804.

Lemma collineation_12805 : is_collineation fp_12805 fl_12805.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12805 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12805 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12805.

Lemma collineation_12806 : is_collineation fp_12806 fl_12806.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12806 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12806 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12806.

Lemma collineation_12807 : is_collineation fp_12807 fl_12807.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12807 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12807 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12807.

Lemma collineation_12808 : is_collineation fp_12808 fl_12808.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12808 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12808 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12808.

Lemma collineation_12809 : is_collineation fp_12809 fl_12809.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12809 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12809 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12809.

Lemma collineation_12810 : is_collineation fp_12810 fl_12810.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12810 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12810 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12810.

Lemma collineation_12811 : is_collineation fp_12811 fl_12811.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12811 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12811 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12811.

Lemma collineation_12812 : is_collineation fp_12812 fl_12812.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12812 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12812 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12812.

Lemma collineation_12813 : is_collineation fp_12813 fl_12813.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12813 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12813 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12813.

Lemma collineation_12814 : is_collineation fp_12814 fl_12814.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12814 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12814 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12814.

Lemma collineation_12815 : is_collineation fp_12815 fl_12815.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12815 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12815 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12815.

Lemma collineation_12816 : is_collineation fp_12816 fl_12816.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12816 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12816 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12816.

Lemma collineation_12817 : is_collineation fp_12817 fl_12817.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12817 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12817 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12817.

Lemma collineation_12818 : is_collineation fp_12818 fl_12818.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12818 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12818 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12818.

Lemma collineation_12819 : is_collineation fp_12819 fl_12819.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12819 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12819 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12819.

Lemma collineation_12820 : is_collineation fp_12820 fl_12820.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12820 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12820 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12820.

Lemma collineation_12821 : is_collineation fp_12821 fl_12821.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12821 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12821 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12821.

Lemma collineation_12822 : is_collineation fp_12822 fl_12822.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12822 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12822 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12822.

Lemma collineation_12823 : is_collineation fp_12823 fl_12823.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12823 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12823 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12823.

Lemma collineation_12824 : is_collineation fp_12824 fl_12824.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12824 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12824 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12824.

Lemma collineation_12825 : is_collineation fp_12825 fl_12825.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12825 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12825 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12825.

Lemma collineation_12826 : is_collineation fp_12826 fl_12826.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12826 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12826 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12826.

Lemma collineation_12827 : is_collineation fp_12827 fl_12827.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12827 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12827 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12827.

Lemma collineation_12828 : is_collineation fp_12828 fl_12828.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12828 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12828 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12828.

Lemma collineation_12829 : is_collineation fp_12829 fl_12829.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12829 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12829 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12829.

Lemma collineation_12830 : is_collineation fp_12830 fl_12830.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12830 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12830 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12830.

Lemma collineation_12831 : is_collineation fp_12831 fl_12831.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12831 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12831 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12831.

Lemma collineation_12832 : is_collineation fp_12832 fl_12832.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12832 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12832 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12832.

Lemma collineation_12833 : is_collineation fp_12833 fl_12833.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12833 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12833 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12833.

Lemma collineation_12834 : is_collineation fp_12834 fl_12834.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12834 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12834 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12834.

Lemma collineation_12835 : is_collineation fp_12835 fl_12835.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12835 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12835 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12835.

Lemma collineation_12836 : is_collineation fp_12836 fl_12836.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12836 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12836 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12836.

Lemma collineation_12837 : is_collineation fp_12837 fl_12837.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12837 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12837 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12837.

Lemma collineation_12838 : is_collineation fp_12838 fl_12838.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12838 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12838 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12838.

Lemma collineation_12839 : is_collineation fp_12839 fl_12839.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12839 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12839 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12839.

Lemma collineation_12840 : is_collineation fp_12840 fl_12840.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12840 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12840 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12840.

Lemma collineation_12841 : is_collineation fp_12841 fl_12841.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12841 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12841 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12841.

Lemma collineation_12842 : is_collineation fp_12842 fl_12842.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12842 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12842 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12842.

Lemma collineation_12843 : is_collineation fp_12843 fl_12843.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12843 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12843 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12843.

Lemma collineation_12844 : is_collineation fp_12844 fl_12844.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12844 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12844 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12844.

Lemma collineation_12845 : is_collineation fp_12845 fl_12845.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12845 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12845 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12845.

Lemma collineation_12846 : is_collineation fp_12846 fl_12846.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12846 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12846 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12846.

Lemma collineation_12847 : is_collineation fp_12847 fl_12847.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12847 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12847 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12847.

Lemma collineation_12848 : is_collineation fp_12848 fl_12848.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12848 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12848 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12848.

Lemma collineation_12849 : is_collineation fp_12849 fl_12849.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12849 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12849 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12849.

Lemma collineation_12850 : is_collineation fp_12850 fl_12850.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12850 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12850 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12850.

Lemma collineation_12851 : is_collineation fp_12851 fl_12851.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12851 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12851 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12851.

Lemma collineation_12852 : is_collineation fp_12852 fl_12852.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12852 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12852 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12852.

Lemma collineation_12853 : is_collineation fp_12853 fl_12853.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12853 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12853 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12853.

Lemma collineation_12854 : is_collineation fp_12854 fl_12854.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12854 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12854 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12854.

Lemma collineation_12855 : is_collineation fp_12855 fl_12855.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12855 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12855 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12855.

Lemma collineation_12856 : is_collineation fp_12856 fl_12856.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12856 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12856 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12856.

Lemma collineation_12857 : is_collineation fp_12857 fl_12857.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12857 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12857 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12857.

Lemma collineation_12858 : is_collineation fp_12858 fl_12858.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12858 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12858 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12858.

Lemma collineation_12859 : is_collineation fp_12859 fl_12859.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12859 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12859 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12859.

Lemma collineation_12860 : is_collineation fp_12860 fl_12860.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12860 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12860 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12860.

Lemma collineation_12861 : is_collineation fp_12861 fl_12861.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12861 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12861 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12861.

Lemma collineation_12862 : is_collineation fp_12862 fl_12862.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12862 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12862 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12862.

Lemma collineation_12863 : is_collineation fp_12863 fl_12863.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12863 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12863 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12863.

Lemma collineation_12864 : is_collineation fp_12864 fl_12864.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12864 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12864 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12864.

Lemma collineation_12865 : is_collineation fp_12865 fl_12865.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12865 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12865 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12865.

Lemma collineation_12866 : is_collineation fp_12866 fl_12866.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12866 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12866 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12866.

Lemma collineation_12867 : is_collineation fp_12867 fl_12867.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12867 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12867 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12867.

Lemma collineation_12868 : is_collineation fp_12868 fl_12868.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12868 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12868 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12868.

Lemma collineation_12869 : is_collineation fp_12869 fl_12869.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12869 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12869 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12869.

Lemma collineation_12870 : is_collineation fp_12870 fl_12870.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12870 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12870 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12870.

Lemma collineation_12871 : is_collineation fp_12871 fl_12871.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12871 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12871 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12871.

Lemma collineation_12872 : is_collineation fp_12872 fl_12872.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12872 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12872 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12872.

Lemma collineation_12873 : is_collineation fp_12873 fl_12873.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12873 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12873 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12873.

Lemma collineation_12874 : is_collineation fp_12874 fl_12874.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12874 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12874 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12874.

Lemma collineation_12875 : is_collineation fp_12875 fl_12875.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12875 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12875 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12875.

Lemma collineation_12876 : is_collineation fp_12876 fl_12876.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12876 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12876 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12876.

Lemma collineation_12877 : is_collineation fp_12877 fl_12877.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12877 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12877 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12877.

Lemma collineation_12878 : is_collineation fp_12878 fl_12878.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12878 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12878 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12878.

Lemma collineation_12879 : is_collineation fp_12879 fl_12879.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12879 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12879 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12879.

Lemma collineation_12880 : is_collineation fp_12880 fl_12880.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12880 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12880 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12880.

Lemma collineation_12881 : is_collineation fp_12881 fl_12881.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12881 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12881 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12881.

Lemma collineation_12882 : is_collineation fp_12882 fl_12882.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12882 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12882 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12882.

Lemma collineation_12883 : is_collineation fp_12883 fl_12883.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12883 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12883 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12883.

Lemma collineation_12884 : is_collineation fp_12884 fl_12884.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12884 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12884 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12884.

Lemma collineation_12885 : is_collineation fp_12885 fl_12885.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12885 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12885 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12885.

Lemma collineation_12886 : is_collineation fp_12886 fl_12886.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12886 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12886 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12886.

Lemma collineation_12887 : is_collineation fp_12887 fl_12887.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12887 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12887 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12887.

Lemma collineation_12888 : is_collineation fp_12888 fl_12888.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12888 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12888 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12888.

Lemma collineation_12889 : is_collineation fp_12889 fl_12889.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12889 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12889 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12889.

Lemma collineation_12890 : is_collineation fp_12890 fl_12890.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12890 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12890 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12890.

Lemma collineation_12891 : is_collineation fp_12891 fl_12891.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12891 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12891 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12891.

Lemma collineation_12892 : is_collineation fp_12892 fl_12892.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12892 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12892 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12892.

Lemma collineation_12893 : is_collineation fp_12893 fl_12893.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12893 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12893 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12893.

Lemma collineation_12894 : is_collineation fp_12894 fl_12894.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12894 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12894 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12894.

Lemma collineation_12895 : is_collineation fp_12895 fl_12895.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12895 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12895 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12895.

Lemma collineation_12896 : is_collineation fp_12896 fl_12896.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12896 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12896 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12896.

Lemma collineation_12897 : is_collineation fp_12897 fl_12897.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12897 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12897 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12897.

Lemma collineation_12898 : is_collineation fp_12898 fl_12898.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12898 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12898 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12898.

Lemma collineation_12899 : is_collineation fp_12899 fl_12899.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12899 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12899 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12899.

Lemma collineation_12900 : is_collineation fp_12900 fl_12900.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12900 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12900 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12900.

Lemma collineation_12901 : is_collineation fp_12901 fl_12901.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12901 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12901 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12901.

Lemma collineation_12902 : is_collineation fp_12902 fl_12902.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12902 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12902 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12902.

Lemma collineation_12903 : is_collineation fp_12903 fl_12903.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12903 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12903 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12903.

Lemma collineation_12904 : is_collineation fp_12904 fl_12904.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12904 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12904 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12904.

Lemma collineation_12905 : is_collineation fp_12905 fl_12905.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12905 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12905 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12905.

Lemma collineation_12906 : is_collineation fp_12906 fl_12906.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12906 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12906 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12906.

Lemma collineation_12907 : is_collineation fp_12907 fl_12907.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12907 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12907 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12907.

Lemma collineation_12908 : is_collineation fp_12908 fl_12908.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12908 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12908 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12908.

Lemma collineation_12909 : is_collineation fp_12909 fl_12909.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12909 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12909 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12909.

Lemma collineation_12910 : is_collineation fp_12910 fl_12910.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12910 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12910 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12910.

Lemma collineation_12911 : is_collineation fp_12911 fl_12911.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12911 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12911 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12911.

Lemma collineation_12912 : is_collineation fp_12912 fl_12912.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12912 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12912 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12912.

Lemma collineation_12913 : is_collineation fp_12913 fl_12913.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12913 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12913 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12913.

Lemma collineation_12914 : is_collineation fp_12914 fl_12914.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12914 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12914 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12914.

Lemma collineation_12915 : is_collineation fp_12915 fl_12915.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12915 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12915 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12915.

Lemma collineation_12916 : is_collineation fp_12916 fl_12916.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12916 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12916 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12916.

Lemma collineation_12917 : is_collineation fp_12917 fl_12917.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12917 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12917 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12917.

Lemma collineation_12918 : is_collineation fp_12918 fl_12918.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12918 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12918 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12918.

Lemma collineation_12919 : is_collineation fp_12919 fl_12919.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12919 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12919 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12919.

Lemma collineation_12920 : is_collineation fp_12920 fl_12920.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12920 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12920 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12920.

Lemma collineation_12921 : is_collineation fp_12921 fl_12921.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12921 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12921 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12921.

Lemma collineation_12922 : is_collineation fp_12922 fl_12922.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12922 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12922 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12922.

Lemma collineation_12923 : is_collineation fp_12923 fl_12923.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12923 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12923 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12923.

Lemma collineation_12924 : is_collineation fp_12924 fl_12924.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12924 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12924 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12924.

Lemma collineation_12925 : is_collineation fp_12925 fl_12925.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12925 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12925 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12925.

Lemma collineation_12926 : is_collineation fp_12926 fl_12926.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12926 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12926 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12926.

Lemma collineation_12927 : is_collineation fp_12927 fl_12927.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12927 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12927 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12927.

Lemma collineation_12928 : is_collineation fp_12928 fl_12928.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12928 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12928 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12928.

Lemma collineation_12929 : is_collineation fp_12929 fl_12929.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12929 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12929 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12929.

Lemma collineation_12930 : is_collineation fp_12930 fl_12930.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12930 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12930 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12930.

Lemma collineation_12931 : is_collineation fp_12931 fl_12931.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12931 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12931 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12931.

Lemma collineation_12932 : is_collineation fp_12932 fl_12932.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12932 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12932 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12932.

Lemma collineation_12933 : is_collineation fp_12933 fl_12933.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12933 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12933 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12933.

Lemma collineation_12934 : is_collineation fp_12934 fl_12934.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12934 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12934 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12934.

Lemma collineation_12935 : is_collineation fp_12935 fl_12935.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12935 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12935 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12935.

Lemma collineation_12936 : is_collineation fp_12936 fl_12936.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12936 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12936 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12936.

Lemma collineation_12937 : is_collineation fp_12937 fl_12937.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12937 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12937 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12937.

Lemma collineation_12938 : is_collineation fp_12938 fl_12938.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12938 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12938 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12938.

Lemma collineation_12939 : is_collineation fp_12939 fl_12939.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12939 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12939 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12939.

Lemma collineation_12940 : is_collineation fp_12940 fl_12940.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12940 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12940 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12940.

Lemma collineation_12941 : is_collineation fp_12941 fl_12941.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12941 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12941 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12941.

Lemma collineation_12942 : is_collineation fp_12942 fl_12942.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12942 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12942 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12942.

Lemma collineation_12943 : is_collineation fp_12943 fl_12943.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12943 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12943 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12943.

Lemma collineation_12944 : is_collineation fp_12944 fl_12944.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12944 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12944 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12944.

Lemma collineation_12945 : is_collineation fp_12945 fl_12945.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12945 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12945 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12945.

Lemma collineation_12946 : is_collineation fp_12946 fl_12946.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12946 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12946 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12946.

Lemma collineation_12947 : is_collineation fp_12947 fl_12947.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12947 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12947 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12947.

Lemma collineation_12948 : is_collineation fp_12948 fl_12948.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12948 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12948 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12948.

Lemma collineation_12949 : is_collineation fp_12949 fl_12949.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12949 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12949 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12949.

Lemma collineation_12950 : is_collineation fp_12950 fl_12950.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12950 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12950 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12950.

Lemma collineation_12951 : is_collineation fp_12951 fl_12951.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12951 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12951 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12951.

Lemma collineation_12952 : is_collineation fp_12952 fl_12952.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12952 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12952 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12952.

Lemma collineation_12953 : is_collineation fp_12953 fl_12953.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12953 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12953 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12953.

Lemma collineation_12954 : is_collineation fp_12954 fl_12954.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12954 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12954 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12954.

Lemma collineation_12955 : is_collineation fp_12955 fl_12955.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12955 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12955 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12955.

Lemma collineation_12956 : is_collineation fp_12956 fl_12956.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12956 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12956 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12956.

Lemma collineation_12957 : is_collineation fp_12957 fl_12957.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12957 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12957 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12957.

Lemma collineation_12958 : is_collineation fp_12958 fl_12958.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12958 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12958 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12958.

Lemma collineation_12959 : is_collineation fp_12959 fl_12959.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12959 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12959 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12959.

Lemma collineation_12960 : is_collineation fp_12960 fl_12960.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12960 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12960 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12960.

Lemma collineation_12961 : is_collineation fp_12961 fl_12961.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12961 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12961 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12961.

Lemma collineation_12962 : is_collineation fp_12962 fl_12962.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12962 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12962 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12962.

Lemma collineation_12963 : is_collineation fp_12963 fl_12963.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12963 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12963 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12963.

Lemma collineation_12964 : is_collineation fp_12964 fl_12964.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12964 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12964 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12964.

Lemma collineation_12965 : is_collineation fp_12965 fl_12965.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12965 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12965 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12965.

Lemma collineation_12966 : is_collineation fp_12966 fl_12966.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12966 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12966 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12966.

Lemma collineation_12967 : is_collineation fp_12967 fl_12967.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12967 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12967 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12967.

Lemma collineation_12968 : is_collineation fp_12968 fl_12968.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12968 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12968 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12968.

Lemma collineation_12969 : is_collineation fp_12969 fl_12969.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12969 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12969 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12969.

Lemma collineation_12970 : is_collineation fp_12970 fl_12970.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12970 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12970 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12970.

Lemma collineation_12971 : is_collineation fp_12971 fl_12971.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12971 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12971 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12971.

Lemma collineation_12972 : is_collineation fp_12972 fl_12972.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12972 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12972 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12972.

Lemma collineation_12973 : is_collineation fp_12973 fl_12973.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12973 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12973 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12973.

Lemma collineation_12974 : is_collineation fp_12974 fl_12974.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12974 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12974 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12974.

Lemma collineation_12975 : is_collineation fp_12975 fl_12975.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12975 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12975 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12975.

Lemma collineation_12976 : is_collineation fp_12976 fl_12976.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12976 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12976 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12976.

Lemma collineation_12977 : is_collineation fp_12977 fl_12977.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12977 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12977 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12977.

Lemma collineation_12978 : is_collineation fp_12978 fl_12978.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12978 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12978 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12978.

Lemma collineation_12979 : is_collineation fp_12979 fl_12979.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12979 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12979 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12979.

Lemma collineation_12980 : is_collineation fp_12980 fl_12980.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12980 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12980 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12980.

Lemma collineation_12981 : is_collineation fp_12981 fl_12981.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12981 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12981 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12981.

Lemma collineation_12982 : is_collineation fp_12982 fl_12982.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12982 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12982 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12982.

Lemma collineation_12983 : is_collineation fp_12983 fl_12983.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12983 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12983 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12983.

Lemma collineation_12984 : is_collineation fp_12984 fl_12984.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12984 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12984 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12984.

Lemma collineation_12985 : is_collineation fp_12985 fl_12985.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12985 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12985 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12985.

Lemma collineation_12986 : is_collineation fp_12986 fl_12986.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12986 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12986 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12986.

Lemma collineation_12987 : is_collineation fp_12987 fl_12987.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12987 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12987 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12987.

Lemma collineation_12988 : is_collineation fp_12988 fl_12988.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12988 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12988 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12988.

Lemma collineation_12989 : is_collineation fp_12989 fl_12989.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12989 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12989 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12989.

Lemma collineation_12990 : is_collineation fp_12990 fl_12990.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12990 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12990 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12990.

Lemma collineation_12991 : is_collineation fp_12991 fl_12991.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12991 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12991 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12991.

Lemma collineation_12992 : is_collineation fp_12992 fl_12992.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12992 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12992 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12992.

Lemma collineation_12993 : is_collineation fp_12993 fl_12993.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12993 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12993 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12993.

Lemma collineation_12994 : is_collineation fp_12994 fl_12994.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12994 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12994 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12994.

Lemma collineation_12995 : is_collineation fp_12995 fl_12995.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12995 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12995 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12995.

Lemma collineation_12996 : is_collineation fp_12996 fl_12996.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12996 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12996 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12996.

Lemma collineation_12997 : is_collineation fp_12997 fl_12997.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12997 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12997 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12997.

Lemma collineation_12998 : is_collineation fp_12998 fl_12998.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12998 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12998 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12998.

Lemma collineation_12999 : is_collineation fp_12999 fl_12999.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_12999 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_12999 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_12999.

Lemma collineation_13000 : is_collineation fp_13000 fl_13000.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13000 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13000 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13000.

Lemma collineation_13001 : is_collineation fp_13001 fl_13001.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13001 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13001 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13001.

Lemma collineation_13002 : is_collineation fp_13002 fl_13002.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13002 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13002 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13002.

Lemma collineation_13003 : is_collineation fp_13003 fl_13003.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13003 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13003 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13003.

Lemma collineation_13004 : is_collineation fp_13004 fl_13004.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13004 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13004 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13004.

Lemma collineation_13005 : is_collineation fp_13005 fl_13005.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13005 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13005 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13005.

Lemma collineation_13006 : is_collineation fp_13006 fl_13006.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13006 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13006 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13006.

Lemma collineation_13007 : is_collineation fp_13007 fl_13007.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13007 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13007 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13007.

Lemma collineation_13008 : is_collineation fp_13008 fl_13008.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13008 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13008 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13008.

Lemma collineation_13009 : is_collineation fp_13009 fl_13009.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13009 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13009 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13009.

Lemma collineation_13010 : is_collineation fp_13010 fl_13010.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13010 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13010 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13010.

Lemma collineation_13011 : is_collineation fp_13011 fl_13011.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13011 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13011 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13011.

Lemma collineation_13012 : is_collineation fp_13012 fl_13012.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13012 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13012 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13012.

Lemma collineation_13013 : is_collineation fp_13013 fl_13013.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13013 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13013 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13013.

Lemma collineation_13014 : is_collineation fp_13014 fl_13014.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13014 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13014 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13014.

Lemma collineation_13015 : is_collineation fp_13015 fl_13015.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13015 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13015 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13015.

Lemma collineation_13016 : is_collineation fp_13016 fl_13016.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13016 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13016 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13016.

Lemma collineation_13017 : is_collineation fp_13017 fl_13017.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13017 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13017 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13017.

Lemma collineation_13018 : is_collineation fp_13018 fl_13018.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13018 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13018 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13018.

Lemma collineation_13019 : is_collineation fp_13019 fl_13019.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13019 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13019 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13019.

Lemma collineation_13020 : is_collineation fp_13020 fl_13020.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13020 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13020 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13020.

Lemma collineation_13021 : is_collineation fp_13021 fl_13021.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13021 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13021 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13021.

Lemma collineation_13022 : is_collineation fp_13022 fl_13022.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13022 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13022 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13022.

Lemma collineation_13023 : is_collineation fp_13023 fl_13023.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13023 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13023 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13023.

Lemma collineation_13024 : is_collineation fp_13024 fl_13024.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13024 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13024 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13024.

Lemma collineation_13025 : is_collineation fp_13025 fl_13025.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13025 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13025 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13025.

Lemma collineation_13026 : is_collineation fp_13026 fl_13026.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13026 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13026 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13026.

Lemma collineation_13027 : is_collineation fp_13027 fl_13027.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13027 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13027 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13027.

Lemma collineation_13028 : is_collineation fp_13028 fl_13028.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13028 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13028 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13028.

Lemma collineation_13029 : is_collineation fp_13029 fl_13029.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13029 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13029 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13029.

Lemma collineation_13030 : is_collineation fp_13030 fl_13030.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13030 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13030 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13030.

Lemma collineation_13031 : is_collineation fp_13031 fl_13031.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13031 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13031 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13031.

Lemma collineation_13032 : is_collineation fp_13032 fl_13032.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13032 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13032 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13032.

Lemma collineation_13033 : is_collineation fp_13033 fl_13033.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13033 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13033 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13033.

Lemma collineation_13034 : is_collineation fp_13034 fl_13034.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13034 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13034 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13034.

Lemma collineation_13035 : is_collineation fp_13035 fl_13035.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13035 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13035 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13035.

Lemma collineation_13036 : is_collineation fp_13036 fl_13036.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13036 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13036 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13036.

Lemma collineation_13037 : is_collineation fp_13037 fl_13037.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13037 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13037 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13037.

Lemma collineation_13038 : is_collineation fp_13038 fl_13038.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13038 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13038 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13038.

Lemma collineation_13039 : is_collineation fp_13039 fl_13039.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13039 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13039 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13039.

Lemma collineation_13040 : is_collineation fp_13040 fl_13040.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13040 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13040 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13040.

Lemma collineation_13041 : is_collineation fp_13041 fl_13041.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13041 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13041 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13041.

Lemma collineation_13042 : is_collineation fp_13042 fl_13042.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13042 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13042 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13042.

Lemma collineation_13043 : is_collineation fp_13043 fl_13043.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13043 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13043 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13043.

Lemma collineation_13044 : is_collineation fp_13044 fl_13044.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13044 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13044 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13044.

Lemma collineation_13045 : is_collineation fp_13045 fl_13045.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13045 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13045 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13045.

Lemma collineation_13046 : is_collineation fp_13046 fl_13046.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13046 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13046 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13046.

Lemma collineation_13047 : is_collineation fp_13047 fl_13047.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13047 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13047 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13047.

Lemma collineation_13048 : is_collineation fp_13048 fl_13048.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13048 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13048 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13048.

Lemma collineation_13049 : is_collineation fp_13049 fl_13049.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13049 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13049 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13049.

Lemma collineation_13050 : is_collineation fp_13050 fl_13050.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13050 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13050 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13050.

Lemma collineation_13051 : is_collineation fp_13051 fl_13051.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13051 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13051 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13051.

Lemma collineation_13052 : is_collineation fp_13052 fl_13052.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13052 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13052 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13052.

Lemma collineation_13053 : is_collineation fp_13053 fl_13053.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13053 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13053 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13053.

Lemma collineation_13054 : is_collineation fp_13054 fl_13054.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13054 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13054 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13054.

Lemma collineation_13055 : is_collineation fp_13055 fl_13055.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13055 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13055 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13055.

Lemma collineation_13056 : is_collineation fp_13056 fl_13056.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13056 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13056 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13056.

Lemma collineation_13057 : is_collineation fp_13057 fl_13057.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13057 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13057 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13057.

Lemma collineation_13058 : is_collineation fp_13058 fl_13058.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13058 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13058 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13058.

Lemma collineation_13059 : is_collineation fp_13059 fl_13059.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13059 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13059 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13059.

Lemma collineation_13060 : is_collineation fp_13060 fl_13060.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13060 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13060 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13060.

Lemma collineation_13061 : is_collineation fp_13061 fl_13061.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13061 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13061 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13061.

Lemma collineation_13062 : is_collineation fp_13062 fl_13062.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13062 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13062 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13062.

Lemma collineation_13063 : is_collineation fp_13063 fl_13063.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13063 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13063 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13063.

Lemma collineation_13064 : is_collineation fp_13064 fl_13064.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13064 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13064 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13064.

Lemma collineation_13065 : is_collineation fp_13065 fl_13065.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13065 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13065 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13065.

Lemma collineation_13066 : is_collineation fp_13066 fl_13066.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13066 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13066 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13066.

Lemma collineation_13067 : is_collineation fp_13067 fl_13067.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13067 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13067 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13067.

Lemma collineation_13068 : is_collineation fp_13068 fl_13068.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13068 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13068 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13068.

Lemma collineation_13069 : is_collineation fp_13069 fl_13069.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13069 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13069 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13069.

Lemma collineation_13070 : is_collineation fp_13070 fl_13070.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13070 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13070 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13070.

Lemma collineation_13071 : is_collineation fp_13071 fl_13071.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13071 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13071 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13071.

Lemma collineation_13072 : is_collineation fp_13072 fl_13072.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13072 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13072 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13072.

Lemma collineation_13073 : is_collineation fp_13073 fl_13073.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13073 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13073 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13073.

Lemma collineation_13074 : is_collineation fp_13074 fl_13074.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13074 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13074 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13074.

Lemma collineation_13075 : is_collineation fp_13075 fl_13075.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13075 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13075 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13075.

Lemma collineation_13076 : is_collineation fp_13076 fl_13076.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13076 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13076 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13076.

Lemma collineation_13077 : is_collineation fp_13077 fl_13077.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13077 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13077 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13077.

Lemma collineation_13078 : is_collineation fp_13078 fl_13078.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13078 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13078 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13078.

Lemma collineation_13079 : is_collineation fp_13079 fl_13079.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13079 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13079 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13079.

Lemma collineation_13080 : is_collineation fp_13080 fl_13080.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13080 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13080 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13080.

Lemma collineation_13081 : is_collineation fp_13081 fl_13081.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13081 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13081 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13081.

Lemma collineation_13082 : is_collineation fp_13082 fl_13082.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13082 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13082 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13082.

Lemma collineation_13083 : is_collineation fp_13083 fl_13083.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13083 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13083 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13083.

Lemma collineation_13084 : is_collineation fp_13084 fl_13084.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13084 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13084 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13084.

Lemma collineation_13085 : is_collineation fp_13085 fl_13085.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13085 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13085 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13085.

Lemma collineation_13086 : is_collineation fp_13086 fl_13086.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13086 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13086 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13086.

Lemma collineation_13087 : is_collineation fp_13087 fl_13087.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13087 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13087 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13087.

Lemma collineation_13088 : is_collineation fp_13088 fl_13088.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13088 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13088 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13088.

Lemma collineation_13089 : is_collineation fp_13089 fl_13089.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13089 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13089 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13089.

Lemma collineation_13090 : is_collineation fp_13090 fl_13090.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13090 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13090 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13090.

Lemma collineation_13091 : is_collineation fp_13091 fl_13091.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13091 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13091 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13091.

Lemma collineation_13092 : is_collineation fp_13092 fl_13092.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13092 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13092 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13092.

Lemma collineation_13093 : is_collineation fp_13093 fl_13093.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13093 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13093 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13093.

Lemma collineation_13094 : is_collineation fp_13094 fl_13094.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13094 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13094 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13094.

Lemma collineation_13095 : is_collineation fp_13095 fl_13095.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13095 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13095 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13095.

Lemma collineation_13096 : is_collineation fp_13096 fl_13096.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13096 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13096 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13096.

Lemma collineation_13097 : is_collineation fp_13097 fl_13097.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13097 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13097 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13097.

Lemma collineation_13098 : is_collineation fp_13098 fl_13098.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13098 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13098 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13098.

Lemma collineation_13099 : is_collineation fp_13099 fl_13099.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13099 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13099 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13099.

Lemma collineation_13100 : is_collineation fp_13100 fl_13100.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13100 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13100 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13100.

Lemma collineation_13101 : is_collineation fp_13101 fl_13101.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13101 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13101 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13101.

Lemma collineation_13102 : is_collineation fp_13102 fl_13102.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13102 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13102 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13102.

Lemma collineation_13103 : is_collineation fp_13103 fl_13103.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13103 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13103 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13103.

Lemma collineation_13104 : is_collineation fp_13104 fl_13104.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13104 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13104 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13104.

Lemma collineation_13105 : is_collineation fp_13105 fl_13105.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13105 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13105 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13105.

Lemma collineation_13106 : is_collineation fp_13106 fl_13106.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13106 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13106 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13106.

Lemma collineation_13107 : is_collineation fp_13107 fl_13107.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13107 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13107 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13107.

Lemma collineation_13108 : is_collineation fp_13108 fl_13108.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13108 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13108 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13108.

Lemma collineation_13109 : is_collineation fp_13109 fl_13109.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13109 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13109 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13109.

Lemma collineation_13110 : is_collineation fp_13110 fl_13110.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13110 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13110 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13110.

Lemma collineation_13111 : is_collineation fp_13111 fl_13111.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13111 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13111 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13111.

Lemma collineation_13112 : is_collineation fp_13112 fl_13112.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13112 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13112 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13112.

Lemma collineation_13113 : is_collineation fp_13113 fl_13113.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13113 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13113 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13113.

Lemma collineation_13114 : is_collineation fp_13114 fl_13114.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13114 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13114 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13114.

Lemma collineation_13115 : is_collineation fp_13115 fl_13115.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13115 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13115 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13115.

Lemma collineation_13116 : is_collineation fp_13116 fl_13116.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13116 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13116 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13116.

Lemma collineation_13117 : is_collineation fp_13117 fl_13117.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13117 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13117 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13117.

Lemma collineation_13118 : is_collineation fp_13118 fl_13118.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13118 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13118 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13118.

Lemma collineation_13119 : is_collineation fp_13119 fl_13119.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13119 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13119 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13119.

Lemma collineation_13120 : is_collineation fp_13120 fl_13120.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13120 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13120 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13120.

Lemma collineation_13121 : is_collineation fp_13121 fl_13121.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13121 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13121 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13121.

Lemma collineation_13122 : is_collineation fp_13122 fl_13122.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13122 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13122 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13122.

Lemma collineation_13123 : is_collineation fp_13123 fl_13123.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13123 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13123 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13123.

Lemma collineation_13124 : is_collineation fp_13124 fl_13124.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13124 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13124 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13124.

Lemma collineation_13125 : is_collineation fp_13125 fl_13125.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13125 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13125 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13125.

Lemma collineation_13126 : is_collineation fp_13126 fl_13126.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13126 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13126 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13126.

Lemma collineation_13127 : is_collineation fp_13127 fl_13127.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13127 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13127 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13127.

Lemma collineation_13128 : is_collineation fp_13128 fl_13128.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13128 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13128 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13128.

Lemma collineation_13129 : is_collineation fp_13129 fl_13129.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13129 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13129 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13129.

Lemma collineation_13130 : is_collineation fp_13130 fl_13130.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13130 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13130 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13130.

Lemma collineation_13131 : is_collineation fp_13131 fl_13131.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13131 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13131 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13131.

Lemma collineation_13132 : is_collineation fp_13132 fl_13132.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13132 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13132 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13132.

Lemma collineation_13133 : is_collineation fp_13133 fl_13133.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13133 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13133 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13133.

Lemma collineation_13134 : is_collineation fp_13134 fl_13134.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13134 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13134 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13134.

Lemma collineation_13135 : is_collineation fp_13135 fl_13135.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13135 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13135 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13135.

Lemma collineation_13136 : is_collineation fp_13136 fl_13136.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13136 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13136 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13136.

Lemma collineation_13137 : is_collineation fp_13137 fl_13137.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13137 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13137 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13137.

Lemma collineation_13138 : is_collineation fp_13138 fl_13138.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13138 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13138 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13138.

Lemma collineation_13139 : is_collineation fp_13139 fl_13139.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13139 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13139 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13139.

Lemma collineation_13140 : is_collineation fp_13140 fl_13140.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13140 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13140 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13140.

Lemma collineation_13141 : is_collineation fp_13141 fl_13141.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13141 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13141 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13141.

Lemma collineation_13142 : is_collineation fp_13142 fl_13142.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13142 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13142 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13142.

Lemma collineation_13143 : is_collineation fp_13143 fl_13143.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13143 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13143 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13143.

Lemma collineation_13144 : is_collineation fp_13144 fl_13144.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13144 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13144 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13144.

Lemma collineation_13145 : is_collineation fp_13145 fl_13145.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13145 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13145 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13145.

Lemma collineation_13146 : is_collineation fp_13146 fl_13146.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13146 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13146 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13146.

Lemma collineation_13147 : is_collineation fp_13147 fl_13147.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13147 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13147 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13147.

Lemma collineation_13148 : is_collineation fp_13148 fl_13148.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13148 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13148 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13148.

Lemma collineation_13149 : is_collineation fp_13149 fl_13149.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13149 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13149 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13149.

Lemma collineation_13150 : is_collineation fp_13150 fl_13150.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13150 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13150 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13150.

Lemma collineation_13151 : is_collineation fp_13151 fl_13151.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13151 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13151 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13151.

Lemma collineation_13152 : is_collineation fp_13152 fl_13152.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13152 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13152 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13152.

Lemma collineation_13153 : is_collineation fp_13153 fl_13153.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13153 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13153 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13153.

Lemma collineation_13154 : is_collineation fp_13154 fl_13154.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13154 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13154 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13154.

Lemma collineation_13155 : is_collineation fp_13155 fl_13155.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13155 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13155 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13155.

Lemma collineation_13156 : is_collineation fp_13156 fl_13156.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13156 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13156 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13156.

Lemma collineation_13157 : is_collineation fp_13157 fl_13157.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13157 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13157 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13157.

Lemma collineation_13158 : is_collineation fp_13158 fl_13158.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13158 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13158 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13158.

Lemma collineation_13159 : is_collineation fp_13159 fl_13159.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13159 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13159 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13159.

Lemma collineation_13160 : is_collineation fp_13160 fl_13160.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13160 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13160 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13160.

Lemma collineation_13161 : is_collineation fp_13161 fl_13161.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13161 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13161 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13161.

Lemma collineation_13162 : is_collineation fp_13162 fl_13162.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13162 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13162 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13162.

Lemma collineation_13163 : is_collineation fp_13163 fl_13163.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13163 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13163 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13163.

Lemma collineation_13164 : is_collineation fp_13164 fl_13164.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13164 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13164 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13164.

Lemma collineation_13165 : is_collineation fp_13165 fl_13165.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13165 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13165 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13165.

Lemma collineation_13166 : is_collineation fp_13166 fl_13166.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13166 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13166 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13166.

Lemma collineation_13167 : is_collineation fp_13167 fl_13167.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13167 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13167 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13167.

Lemma collineation_13168 : is_collineation fp_13168 fl_13168.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13168 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13168 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13168.

Lemma collineation_13169 : is_collineation fp_13169 fl_13169.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13169 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13169 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13169.

Lemma collineation_13170 : is_collineation fp_13170 fl_13170.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13170 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13170 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13170.

Lemma collineation_13171 : is_collineation fp_13171 fl_13171.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13171 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13171 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13171.

Lemma collineation_13172 : is_collineation fp_13172 fl_13172.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13172 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13172 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13172.

Lemma collineation_13173 : is_collineation fp_13173 fl_13173.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13173 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13173 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13173.

Lemma collineation_13174 : is_collineation fp_13174 fl_13174.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13174 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13174 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13174.

Lemma collineation_13175 : is_collineation fp_13175 fl_13175.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13175 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13175 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13175.

Lemma collineation_13176 : is_collineation fp_13176 fl_13176.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13176 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13176 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13176.

Lemma collineation_13177 : is_collineation fp_13177 fl_13177.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13177 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13177 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13177.

Lemma collineation_13178 : is_collineation fp_13178 fl_13178.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13178 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13178 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13178.

Lemma collineation_13179 : is_collineation fp_13179 fl_13179.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13179 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13179 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13179.

Lemma collineation_13180 : is_collineation fp_13180 fl_13180.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13180 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13180 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13180.

Lemma collineation_13181 : is_collineation fp_13181 fl_13181.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13181 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13181 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13181.

Lemma collineation_13182 : is_collineation fp_13182 fl_13182.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13182 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13182 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13182.

Lemma collineation_13183 : is_collineation fp_13183 fl_13183.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13183 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13183 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13183.

Lemma collineation_13184 : is_collineation fp_13184 fl_13184.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13184 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13184 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13184.

Lemma collineation_13185 : is_collineation fp_13185 fl_13185.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13185 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13185 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13185.

Lemma collineation_13186 : is_collineation fp_13186 fl_13186.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13186 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13186 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13186.

Lemma collineation_13187 : is_collineation fp_13187 fl_13187.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13187 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13187 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13187.

Lemma collineation_13188 : is_collineation fp_13188 fl_13188.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13188 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13188 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13188.

Lemma collineation_13189 : is_collineation fp_13189 fl_13189.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13189 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13189 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13189.

Lemma collineation_13190 : is_collineation fp_13190 fl_13190.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13190 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13190 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13190.

Lemma collineation_13191 : is_collineation fp_13191 fl_13191.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13191 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13191 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13191.

Lemma collineation_13192 : is_collineation fp_13192 fl_13192.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13192 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13192 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13192.

Lemma collineation_13193 : is_collineation fp_13193 fl_13193.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13193 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13193 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13193.

Lemma collineation_13194 : is_collineation fp_13194 fl_13194.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13194 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13194 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13194.

Lemma collineation_13195 : is_collineation fp_13195 fl_13195.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13195 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13195 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13195.

Lemma collineation_13196 : is_collineation fp_13196 fl_13196.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13196 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13196 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13196.

Lemma collineation_13197 : is_collineation fp_13197 fl_13197.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13197 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13197 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13197.

Lemma collineation_13198 : is_collineation fp_13198 fl_13198.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13198 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13198 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13198.

Lemma collineation_13199 : is_collineation fp_13199 fl_13199.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13199 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13199 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13199.

Lemma collineation_13200 : is_collineation fp_13200 fl_13200.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13200 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13200 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13200.

Lemma collineation_13201 : is_collineation fp_13201 fl_13201.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13201 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13201 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13201.

Lemma collineation_13202 : is_collineation fp_13202 fl_13202.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13202 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13202 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13202.

Lemma collineation_13203 : is_collineation fp_13203 fl_13203.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13203 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13203 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13203.

Lemma collineation_13204 : is_collineation fp_13204 fl_13204.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13204 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13204 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13204.

Lemma collineation_13205 : is_collineation fp_13205 fl_13205.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13205 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13205 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13205.

Lemma collineation_13206 : is_collineation fp_13206 fl_13206.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13206 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13206 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13206.

Lemma collineation_13207 : is_collineation fp_13207 fl_13207.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13207 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13207 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13207.

Lemma collineation_13208 : is_collineation fp_13208 fl_13208.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13208 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13208 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13208.

Lemma collineation_13209 : is_collineation fp_13209 fl_13209.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13209 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13209 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13209.

Lemma collineation_13210 : is_collineation fp_13210 fl_13210.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13210 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13210 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13210.

Lemma collineation_13211 : is_collineation fp_13211 fl_13211.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13211 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13211 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13211.

Lemma collineation_13212 : is_collineation fp_13212 fl_13212.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13212 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13212 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13212.

Lemma collineation_13213 : is_collineation fp_13213 fl_13213.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13213 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13213 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13213.

Lemma collineation_13214 : is_collineation fp_13214 fl_13214.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13214 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13214 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13214.

Lemma collineation_13215 : is_collineation fp_13215 fl_13215.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13215 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13215 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13215.

Lemma collineation_13216 : is_collineation fp_13216 fl_13216.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13216 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13216 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13216.

Lemma collineation_13217 : is_collineation fp_13217 fl_13217.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13217 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13217 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13217.

Lemma collineation_13218 : is_collineation fp_13218 fl_13218.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13218 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13218 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13218.

Lemma collineation_13219 : is_collineation fp_13219 fl_13219.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13219 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13219 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13219.

Lemma collineation_13220 : is_collineation fp_13220 fl_13220.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13220 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13220 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13220.

Lemma collineation_13221 : is_collineation fp_13221 fl_13221.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13221 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13221 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13221.

Lemma collineation_13222 : is_collineation fp_13222 fl_13222.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13222 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13222 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13222.

Lemma collineation_13223 : is_collineation fp_13223 fl_13223.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13223 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13223 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13223.

Lemma collineation_13224 : is_collineation fp_13224 fl_13224.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13224 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13224 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13224.

Lemma collineation_13225 : is_collineation fp_13225 fl_13225.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13225 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13225 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13225.

Lemma collineation_13226 : is_collineation fp_13226 fl_13226.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13226 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13226 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13226.

Lemma collineation_13227 : is_collineation fp_13227 fl_13227.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13227 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13227 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13227.

Lemma collineation_13228 : is_collineation fp_13228 fl_13228.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13228 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13228 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13228.

Lemma collineation_13229 : is_collineation fp_13229 fl_13229.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13229 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13229 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13229.

Lemma collineation_13230 : is_collineation fp_13230 fl_13230.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13230 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13230 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13230.

Lemma collineation_13231 : is_collineation fp_13231 fl_13231.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13231 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13231 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13231.

Lemma collineation_13232 : is_collineation fp_13232 fl_13232.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13232 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13232 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13232.

Lemma collineation_13233 : is_collineation fp_13233 fl_13233.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13233 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13233 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13233.

Lemma collineation_13234 : is_collineation fp_13234 fl_13234.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13234 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13234 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13234.

Lemma collineation_13235 : is_collineation fp_13235 fl_13235.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13235 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13235 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13235.

Lemma collineation_13236 : is_collineation fp_13236 fl_13236.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13236 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13236 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13236.

Lemma collineation_13237 : is_collineation fp_13237 fl_13237.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13237 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13237 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13237.

Lemma collineation_13238 : is_collineation fp_13238 fl_13238.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13238 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13238 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13238.

Lemma collineation_13239 : is_collineation fp_13239 fl_13239.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13239 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13239 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13239.

Lemma collineation_13240 : is_collineation fp_13240 fl_13240.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13240 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13240 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13240.

Lemma collineation_13241 : is_collineation fp_13241 fl_13241.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13241 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13241 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13241.

Lemma collineation_13242 : is_collineation fp_13242 fl_13242.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13242 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13242 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13242.

Lemma collineation_13243 : is_collineation fp_13243 fl_13243.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13243 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13243 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13243.

Lemma collineation_13244 : is_collineation fp_13244 fl_13244.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13244 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13244 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13244.

Lemma collineation_13245 : is_collineation fp_13245 fl_13245.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13245 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13245 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13245.

Lemma collineation_13246 : is_collineation fp_13246 fl_13246.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13246 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13246 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13246.

Lemma collineation_13247 : is_collineation fp_13247 fl_13247.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13247 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13247 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13247.

Lemma collineation_13248 : is_collineation fp_13248 fl_13248.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13248 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13248 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13248.

Lemma collineation_13249 : is_collineation fp_13249 fl_13249.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13249 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13249 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13249.

Lemma collineation_13250 : is_collineation fp_13250 fl_13250.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13250 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13250 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13250.

Lemma collineation_13251 : is_collineation fp_13251 fl_13251.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13251 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13251 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13251.

Lemma collineation_13252 : is_collineation fp_13252 fl_13252.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13252 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13252 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13252.

Lemma collineation_13253 : is_collineation fp_13253 fl_13253.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13253 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13253 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13253.

Lemma collineation_13254 : is_collineation fp_13254 fl_13254.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13254 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13254 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13254.

Lemma collineation_13255 : is_collineation fp_13255 fl_13255.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13255 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13255 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13255.

Lemma collineation_13256 : is_collineation fp_13256 fl_13256.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13256 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13256 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13256.

Lemma collineation_13257 : is_collineation fp_13257 fl_13257.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13257 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13257 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13257.

Lemma collineation_13258 : is_collineation fp_13258 fl_13258.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13258 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13258 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13258.

Lemma collineation_13259 : is_collineation fp_13259 fl_13259.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13259 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13259 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13259.

Lemma collineation_13260 : is_collineation fp_13260 fl_13260.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13260 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13260 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13260.

Lemma collineation_13261 : is_collineation fp_13261 fl_13261.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13261 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13261 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13261.

Lemma collineation_13262 : is_collineation fp_13262 fl_13262.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13262 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13262 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13262.

Lemma collineation_13263 : is_collineation fp_13263 fl_13263.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13263 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13263 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13263.

Lemma collineation_13264 : is_collineation fp_13264 fl_13264.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13264 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13264 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13264.

Lemma collineation_13265 : is_collineation fp_13265 fl_13265.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13265 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13265 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13265.

Lemma collineation_13266 : is_collineation fp_13266 fl_13266.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13266 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13266 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13266.

Lemma collineation_13267 : is_collineation fp_13267 fl_13267.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13267 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13267 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13267.

Lemma collineation_13268 : is_collineation fp_13268 fl_13268.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13268 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13268 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13268.

Lemma collineation_13269 : is_collineation fp_13269 fl_13269.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13269 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13269 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13269.

Lemma collineation_13270 : is_collineation fp_13270 fl_13270.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13270 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13270 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13270.

Lemma collineation_13271 : is_collineation fp_13271 fl_13271.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13271 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13271 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13271.

Lemma collineation_13272 : is_collineation fp_13272 fl_13272.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13272 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13272 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13272.

Lemma collineation_13273 : is_collineation fp_13273 fl_13273.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13273 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13273 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13273.

Lemma collineation_13274 : is_collineation fp_13274 fl_13274.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13274 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13274 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13274.

Lemma collineation_13275 : is_collineation fp_13275 fl_13275.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13275 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13275 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13275.

Lemma collineation_13276 : is_collineation fp_13276 fl_13276.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13276 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13276 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13276.

Lemma collineation_13277 : is_collineation fp_13277 fl_13277.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13277 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13277 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13277.

Lemma collineation_13278 : is_collineation fp_13278 fl_13278.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13278 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13278 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13278.

Lemma collineation_13279 : is_collineation fp_13279 fl_13279.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13279 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13279 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13279.

Lemma collineation_13280 : is_collineation fp_13280 fl_13280.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13280 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13280 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13280.

Lemma collineation_13281 : is_collineation fp_13281 fl_13281.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13281 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13281 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13281.

Lemma collineation_13282 : is_collineation fp_13282 fl_13282.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13282 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13282 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13282.

Lemma collineation_13283 : is_collineation fp_13283 fl_13283.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13283 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13283 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13283.

Lemma collineation_13284 : is_collineation fp_13284 fl_13284.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13284 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13284 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13284.

Lemma collineation_13285 : is_collineation fp_13285 fl_13285.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13285 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13285 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13285.

Lemma collineation_13286 : is_collineation fp_13286 fl_13286.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13286 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13286 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13286.

Lemma collineation_13287 : is_collineation fp_13287 fl_13287.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13287 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13287 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13287.

Lemma collineation_13288 : is_collineation fp_13288 fl_13288.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13288 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13288 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13288.

Lemma collineation_13289 : is_collineation fp_13289 fl_13289.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13289 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13289 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13289.

Lemma collineation_13290 : is_collineation fp_13290 fl_13290.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13290 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13290 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13290.

Lemma collineation_13291 : is_collineation fp_13291 fl_13291.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13291 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13291 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13291.

Lemma collineation_13292 : is_collineation fp_13292 fl_13292.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13292 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13292 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13292.

Lemma collineation_13293 : is_collineation fp_13293 fl_13293.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13293 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13293 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13293.

Lemma collineation_13294 : is_collineation fp_13294 fl_13294.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13294 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13294 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13294.

Lemma collineation_13295 : is_collineation fp_13295 fl_13295.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13295 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13295 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13295.

Lemma collineation_13296 : is_collineation fp_13296 fl_13296.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13296 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13296 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13296.

Lemma collineation_13297 : is_collineation fp_13297 fl_13297.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13297 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13297 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13297.

Lemma collineation_13298 : is_collineation fp_13298 fl_13298.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13298 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13298 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13298.

Lemma collineation_13299 : is_collineation fp_13299 fl_13299.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13299 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13299 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13299.

Lemma collineation_13300 : is_collineation fp_13300 fl_13300.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13300 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13300 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13300.

Lemma collineation_13301 : is_collineation fp_13301 fl_13301.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13301 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13301 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13301.

Lemma collineation_13302 : is_collineation fp_13302 fl_13302.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13302 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13302 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13302.

Lemma collineation_13303 : is_collineation fp_13303 fl_13303.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13303 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13303 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13303.

Lemma collineation_13304 : is_collineation fp_13304 fl_13304.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13304 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13304 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13304.

Lemma collineation_13305 : is_collineation fp_13305 fl_13305.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13305 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13305 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13305.

Lemma collineation_13306 : is_collineation fp_13306 fl_13306.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13306 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13306 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13306.

Lemma collineation_13307 : is_collineation fp_13307 fl_13307.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13307 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13307 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13307.

Lemma collineation_13308 : is_collineation fp_13308 fl_13308.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13308 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13308 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13308.

Lemma collineation_13309 : is_collineation fp_13309 fl_13309.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13309 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13309 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13309.

Lemma collineation_13310 : is_collineation fp_13310 fl_13310.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13310 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13310 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13310.

Lemma collineation_13311 : is_collineation fp_13311 fl_13311.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13311 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13311 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13311.

Lemma collineation_13312 : is_collineation fp_13312 fl_13312.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13312 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13312 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13312.

Lemma collineation_13313 : is_collineation fp_13313 fl_13313.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13313 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13313 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13313.

Lemma collineation_13314 : is_collineation fp_13314 fl_13314.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13314 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13314 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13314.

Lemma collineation_13315 : is_collineation fp_13315 fl_13315.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13315 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13315 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13315.

Lemma collineation_13316 : is_collineation fp_13316 fl_13316.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13316 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13316 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13316.

Lemma collineation_13317 : is_collineation fp_13317 fl_13317.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13317 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13317 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13317.

Lemma collineation_13318 : is_collineation fp_13318 fl_13318.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13318 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13318 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13318.

Lemma collineation_13319 : is_collineation fp_13319 fl_13319.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13319 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13319 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13319.

Lemma collineation_13320 : is_collineation fp_13320 fl_13320.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13320 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13320 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13320.

Lemma collineation_13321 : is_collineation fp_13321 fl_13321.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13321 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13321 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13321.

Lemma collineation_13322 : is_collineation fp_13322 fl_13322.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13322 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13322 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13322.

Lemma collineation_13323 : is_collineation fp_13323 fl_13323.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13323 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13323 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13323.

Lemma collineation_13324 : is_collineation fp_13324 fl_13324.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13324 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13324 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13324.

Lemma collineation_13325 : is_collineation fp_13325 fl_13325.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13325 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13325 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13325.

Lemma collineation_13326 : is_collineation fp_13326 fl_13326.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13326 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13326 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13326.

Lemma collineation_13327 : is_collineation fp_13327 fl_13327.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13327 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13327 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13327.

Lemma collineation_13328 : is_collineation fp_13328 fl_13328.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13328 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13328 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13328.

Lemma collineation_13329 : is_collineation fp_13329 fl_13329.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13329 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13329 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13329.

Lemma collineation_13330 : is_collineation fp_13330 fl_13330.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13330 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13330 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13330.

Lemma collineation_13331 : is_collineation fp_13331 fl_13331.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13331 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13331 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13331.

Lemma collineation_13332 : is_collineation fp_13332 fl_13332.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13332 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13332 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13332.

Lemma collineation_13333 : is_collineation fp_13333 fl_13333.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13333 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13333 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13333.

Lemma collineation_13334 : is_collineation fp_13334 fl_13334.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13334 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13334 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13334.

Lemma collineation_13335 : is_collineation fp_13335 fl_13335.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13335 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13335 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13335.

Lemma collineation_13336 : is_collineation fp_13336 fl_13336.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13336 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13336 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13336.

Lemma collineation_13337 : is_collineation fp_13337 fl_13337.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13337 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13337 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13337.

Lemma collineation_13338 : is_collineation fp_13338 fl_13338.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13338 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13338 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13338.

Lemma collineation_13339 : is_collineation fp_13339 fl_13339.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13339 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13339 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13339.

Lemma collineation_13340 : is_collineation fp_13340 fl_13340.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13340 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13340 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13340.

Lemma collineation_13341 : is_collineation fp_13341 fl_13341.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13341 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13341 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13341.

Lemma collineation_13342 : is_collineation fp_13342 fl_13342.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13342 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13342 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13342.

Lemma collineation_13343 : is_collineation fp_13343 fl_13343.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13343 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13343 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13343.

Lemma collineation_13344 : is_collineation fp_13344 fl_13344.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13344 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13344 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13344.

Lemma collineation_13345 : is_collineation fp_13345 fl_13345.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13345 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13345 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13345.

Lemma collineation_13346 : is_collineation fp_13346 fl_13346.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13346 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13346 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13346.

Lemma collineation_13347 : is_collineation fp_13347 fl_13347.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13347 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13347 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13347.

Lemma collineation_13348 : is_collineation fp_13348 fl_13348.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13348 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13348 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13348.

Lemma collineation_13349 : is_collineation fp_13349 fl_13349.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13349 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13349 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13349.

Lemma collineation_13350 : is_collineation fp_13350 fl_13350.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13350 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13350 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13350.

Lemma collineation_13351 : is_collineation fp_13351 fl_13351.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13351 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13351 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13351.

Lemma collineation_13352 : is_collineation fp_13352 fl_13352.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13352 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13352 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13352.

Lemma collineation_13353 : is_collineation fp_13353 fl_13353.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13353 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13353 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13353.

Lemma collineation_13354 : is_collineation fp_13354 fl_13354.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13354 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13354 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13354.

Lemma collineation_13355 : is_collineation fp_13355 fl_13355.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13355 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13355 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13355.

Lemma collineation_13356 : is_collineation fp_13356 fl_13356.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13356 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13356 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13356.

Lemma collineation_13357 : is_collineation fp_13357 fl_13357.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13357 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13357 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13357.

Lemma collineation_13358 : is_collineation fp_13358 fl_13358.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13358 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13358 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13358.

Lemma collineation_13359 : is_collineation fp_13359 fl_13359.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13359 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13359 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13359.

Lemma collineation_13360 : is_collineation fp_13360 fl_13360.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13360 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13360 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13360.

Lemma collineation_13361 : is_collineation fp_13361 fl_13361.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13361 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13361 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13361.

Lemma collineation_13362 : is_collineation fp_13362 fl_13362.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13362 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13362 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13362.

Lemma collineation_13363 : is_collineation fp_13363 fl_13363.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13363 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13363 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13363.

Lemma collineation_13364 : is_collineation fp_13364 fl_13364.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13364 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13364 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13364.

Lemma collineation_13365 : is_collineation fp_13365 fl_13365.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13365 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13365 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13365.

Lemma collineation_13366 : is_collineation fp_13366 fl_13366.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13366 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13366 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13366.

Lemma collineation_13367 : is_collineation fp_13367 fl_13367.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13367 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13367 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13367.

Lemma collineation_13368 : is_collineation fp_13368 fl_13368.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13368 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13368 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13368.

Lemma collineation_13369 : is_collineation fp_13369 fl_13369.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13369 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13369 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13369.

Lemma collineation_13370 : is_collineation fp_13370 fl_13370.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13370 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13370 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13370.

Lemma collineation_13371 : is_collineation fp_13371 fl_13371.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13371 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13371 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13371.

Lemma collineation_13372 : is_collineation fp_13372 fl_13372.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13372 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13372 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13372.

Lemma collineation_13373 : is_collineation fp_13373 fl_13373.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13373 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13373 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13373.

Lemma collineation_13374 : is_collineation fp_13374 fl_13374.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13374 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13374 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13374.

Lemma collineation_13375 : is_collineation fp_13375 fl_13375.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13375 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13375 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13375.

Lemma collineation_13376 : is_collineation fp_13376 fl_13376.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13376 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13376 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13376.

Lemma collineation_13377 : is_collineation fp_13377 fl_13377.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13377 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13377 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13377.

Lemma collineation_13378 : is_collineation fp_13378 fl_13378.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13378 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13378 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13378.

Lemma collineation_13379 : is_collineation fp_13379 fl_13379.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13379 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13379 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13379.

Lemma collineation_13380 : is_collineation fp_13380 fl_13380.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13380 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13380 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13380.

Lemma collineation_13381 : is_collineation fp_13381 fl_13381.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13381 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13381 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13381.

Lemma collineation_13382 : is_collineation fp_13382 fl_13382.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13382 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13382 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13382.

Lemma collineation_13383 : is_collineation fp_13383 fl_13383.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13383 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13383 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13383.

Lemma collineation_13384 : is_collineation fp_13384 fl_13384.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13384 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13384 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13384.

Lemma collineation_13385 : is_collineation fp_13385 fl_13385.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13385 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13385 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13385.

Lemma collineation_13386 : is_collineation fp_13386 fl_13386.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13386 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13386 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13386.

Lemma collineation_13387 : is_collineation fp_13387 fl_13387.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13387 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13387 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13387.

Lemma collineation_13388 : is_collineation fp_13388 fl_13388.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13388 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13388 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13388.

Lemma collineation_13389 : is_collineation fp_13389 fl_13389.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13389 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13389 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13389.

Lemma collineation_13390 : is_collineation fp_13390 fl_13390.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13390 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13390 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13390.

Lemma collineation_13391 : is_collineation fp_13391 fl_13391.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13391 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13391 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13391.

Lemma collineation_13392 : is_collineation fp_13392 fl_13392.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13392 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13392 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13392.

Lemma collineation_13393 : is_collineation fp_13393 fl_13393.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13393 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13393 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13393.

Lemma collineation_13394 : is_collineation fp_13394 fl_13394.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13394 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13394 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13394.

Lemma collineation_13395 : is_collineation fp_13395 fl_13395.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13395 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13395 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13395.

Lemma collineation_13396 : is_collineation fp_13396 fl_13396.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13396 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13396 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13396.

Lemma collineation_13397 : is_collineation fp_13397 fl_13397.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13397 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13397 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13397.

Lemma collineation_13398 : is_collineation fp_13398 fl_13398.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13398 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13398 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13398.

Lemma collineation_13399 : is_collineation fp_13399 fl_13399.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13399 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13399 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13399.

Lemma collineation_13400 : is_collineation fp_13400 fl_13400.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13400 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13400 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13400.

Lemma collineation_13401 : is_collineation fp_13401 fl_13401.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13401 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13401 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13401.

Lemma collineation_13402 : is_collineation fp_13402 fl_13402.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13402 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13402 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13402.

Lemma collineation_13403 : is_collineation fp_13403 fl_13403.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13403 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13403 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13403.

Lemma collineation_13404 : is_collineation fp_13404 fl_13404.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13404 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13404 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13404.

Lemma collineation_13405 : is_collineation fp_13405 fl_13405.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13405 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13405 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13405.

Lemma collineation_13406 : is_collineation fp_13406 fl_13406.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13406 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13406 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13406.

Lemma collineation_13407 : is_collineation fp_13407 fl_13407.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13407 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13407 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13407.

Lemma collineation_13408 : is_collineation fp_13408 fl_13408.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13408 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13408 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13408.

Lemma collineation_13409 : is_collineation fp_13409 fl_13409.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13409 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13409 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13409.

Lemma collineation_13410 : is_collineation fp_13410 fl_13410.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13410 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13410 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13410.

Lemma collineation_13411 : is_collineation fp_13411 fl_13411.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13411 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13411 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13411.

Lemma collineation_13412 : is_collineation fp_13412 fl_13412.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13412 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13412 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13412.

Lemma collineation_13413 : is_collineation fp_13413 fl_13413.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13413 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13413 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13413.

Lemma collineation_13414 : is_collineation fp_13414 fl_13414.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13414 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13414 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13414.

Lemma collineation_13415 : is_collineation fp_13415 fl_13415.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13415 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13415 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13415.

Lemma collineation_13416 : is_collineation fp_13416 fl_13416.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13416 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13416 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13416.

Lemma collineation_13417 : is_collineation fp_13417 fl_13417.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13417 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13417 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13417.

Lemma collineation_13418 : is_collineation fp_13418 fl_13418.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13418 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13418 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13418.

Lemma collineation_13419 : is_collineation fp_13419 fl_13419.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13419 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13419 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13419.

Lemma collineation_13420 : is_collineation fp_13420 fl_13420.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13420 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13420 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13420.

Lemma collineation_13421 : is_collineation fp_13421 fl_13421.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13421 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13421 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13421.

Lemma collineation_13422 : is_collineation fp_13422 fl_13422.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13422 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13422 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13422.

Lemma collineation_13423 : is_collineation fp_13423 fl_13423.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13423 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13423 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13423.

Lemma collineation_13424 : is_collineation fp_13424 fl_13424.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13424 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13424 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13424.

Lemma collineation_13425 : is_collineation fp_13425 fl_13425.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13425 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13425 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13425.

Lemma collineation_13426 : is_collineation fp_13426 fl_13426.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13426 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13426 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13426.

Lemma collineation_13427 : is_collineation fp_13427 fl_13427.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13427 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13427 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13427.

Lemma collineation_13428 : is_collineation fp_13428 fl_13428.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13428 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13428 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13428.

Lemma collineation_13429 : is_collineation fp_13429 fl_13429.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13429 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13429 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13429.

Lemma collineation_13430 : is_collineation fp_13430 fl_13430.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13430 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13430 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13430.

Lemma collineation_13431 : is_collineation fp_13431 fl_13431.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13431 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13431 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13431.

Lemma collineation_13432 : is_collineation fp_13432 fl_13432.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13432 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13432 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13432.

Lemma collineation_13433 : is_collineation fp_13433 fl_13433.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13433 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13433 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13433.

Lemma collineation_13434 : is_collineation fp_13434 fl_13434.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13434 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13434 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13434.

Lemma collineation_13435 : is_collineation fp_13435 fl_13435.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13435 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13435 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13435.

Lemma collineation_13436 : is_collineation fp_13436 fl_13436.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13436 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13436 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13436.

Lemma collineation_13437 : is_collineation fp_13437 fl_13437.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13437 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13437 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13437.

Lemma collineation_13438 : is_collineation fp_13438 fl_13438.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13438 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13438 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13438.

Lemma collineation_13439 : is_collineation fp_13439 fl_13439.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_13439 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_13439 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_13439.

Lemma is_col_all_c126 : forall fp fl, In (fp,fl) (all_c126++all_c127++all_c128++all_c129++all_c130++all_c131++all_c132++all_c133++all_c134++all_c135++all_c136++all_c137++all_c138++all_c139) -> is_collineation fp fl.
Proof.
 intros fp fl HIn_S.
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12096 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12097 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12098 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12099 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12100 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12101 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12102 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12103 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12104 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12105 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12106 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12107 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12108 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12109 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12110 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12111 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12112 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12113 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12114 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12115 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12116 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12117 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12118 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12119 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12120 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12121 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12122 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12123 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12124 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12125 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12126 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12127 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12128 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12129 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12130 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12131 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12132 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12133 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12134 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12135 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12136 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12137 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12138 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12139 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12140 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12141 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12142 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12143 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12144 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12145 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12146 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12147 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12148 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12149 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12150 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12151 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12152 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12153 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12154 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12155 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12156 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12157 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12158 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12159 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12160 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12161 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12162 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12163 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12164 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12165 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12166 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12167 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12168 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12169 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12170 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12171 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12172 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12173 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12174 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12175 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12176 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12177 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12178 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12179 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12180 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12181 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12182 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12183 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12184 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12185 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12186 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12187 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12188 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12189 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12190 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12191 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12192 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12193 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12194 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12195 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12196 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12197 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12198 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12199 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12200 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12201 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12202 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12203 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12204 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12205 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12206 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12207 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12208 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12209 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12210 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12211 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12212 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12213 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12214 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12215 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12216 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12217 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12218 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12219 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12220 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12221 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12222 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12223 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12224 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12225 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12226 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12227 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12228 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12229 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12230 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12231 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12232 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12233 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12234 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12235 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12236 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12237 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12238 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12239 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12240 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12241 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12242 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12243 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12244 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12245 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12246 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12247 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12248 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12249 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12250 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12251 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12252 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12253 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12254 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12255 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12256 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12257 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12258 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12259 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12260 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12261 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12262 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12263 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12264 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12265 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12266 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12267 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12268 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12269 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12270 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12271 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12272 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12273 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12274 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12275 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12276 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12277 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12278 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12279 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12280 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12281 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12282 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12283 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12284 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12285 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12286 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12287 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12288 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12289 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12290 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12291 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12292 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12293 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12294 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12295 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12296 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12297 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12298 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12299 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12300 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12301 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12302 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12303 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12304 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12305 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12306 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12307 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12308 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12309 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12310 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12311 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12312 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12313 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12314 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12315 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12316 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12317 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12318 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12319 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12320 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12321 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12322 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12323 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12324 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12325 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12326 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12327 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12328 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12329 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12330 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12331 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12332 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12333 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12334 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12335 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12336 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12337 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12338 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12339 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12340 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12341 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12342 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12343 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12344 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12345 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12346 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12347 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12348 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12349 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12350 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12351 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12352 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12353 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12354 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12355 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12356 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12357 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12358 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12359 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12360 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12361 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12362 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12363 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12364 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12365 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12366 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12367 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12368 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12369 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12370 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12371 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12372 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12373 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12374 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12375 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12376 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12377 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12378 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12379 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12380 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12381 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12382 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12383 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12384 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12385 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12386 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12387 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12388 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12389 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12390 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12391 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12392 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12393 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12394 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12395 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12396 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12397 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12398 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12399 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12400 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12401 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12402 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12403 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12404 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12405 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12406 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12407 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12408 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12409 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12410 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12411 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12412 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12413 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12414 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12415 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12416 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12417 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12418 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12419 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12420 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12421 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12422 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12423 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12424 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12425 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12426 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12427 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12428 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12429 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12430 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12431 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12432 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12433 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12434 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12435 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12436 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12437 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12438 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12439 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12440 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12441 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12442 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12443 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12444 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12445 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12446 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12447 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12448 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12449 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12450 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12451 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12452 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12453 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12454 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12455 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12456 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12457 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12458 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12459 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12460 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12461 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12462 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12463 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12464 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12465 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12466 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12467 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12468 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12469 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12470 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12471 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12472 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12473 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12474 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12475 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12476 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12477 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12478 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12479 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12480 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12481 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12482 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12483 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12484 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12485 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12486 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12487 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12488 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12489 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12490 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12491 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12492 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12493 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12494 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12495 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12496 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12497 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12498 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12499 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12500 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12501 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12502 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12503 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12504 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12505 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12506 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12507 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12508 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12509 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12510 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12511 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12512 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12513 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12514 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12515 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12516 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12517 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12518 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12519 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12520 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12521 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12522 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12523 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12524 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12525 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12526 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12527 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12528 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12529 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12530 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12531 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12532 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12533 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12534 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12535 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12536 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12537 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12538 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12539 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12540 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12541 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12542 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12543 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12544 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12545 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12546 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12547 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12548 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12549 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12550 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12551 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12552 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12553 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12554 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12555 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12556 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12557 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12558 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12559 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12560 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12561 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12562 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12563 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12564 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12565 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12566 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12567 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12568 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12569 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12570 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12571 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12572 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12573 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12574 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12575 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12576 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12577 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12578 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12579 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12580 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12581 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12582 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12583 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12584 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12585 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12586 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12587 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12588 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12589 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12590 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12591 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12592 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12593 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12594 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12595 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12596 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12597 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12598 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12599 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12600 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12601 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12602 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12603 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12604 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12605 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12606 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12607 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12608 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12609 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12610 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12611 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12612 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12613 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12614 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12615 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12616 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12617 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12618 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12619 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12620 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12621 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12622 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12623 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12624 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12625 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12626 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12627 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12628 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12629 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12630 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12631 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12632 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12633 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12634 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12635 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12636 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12637 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12638 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12639 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12640 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12641 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12642 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12643 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12644 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12645 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12646 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12647 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12648 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12649 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12650 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12651 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12652 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12653 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12654 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12655 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12656 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12657 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12658 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12659 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12660 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12661 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12662 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12663 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12664 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12665 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12666 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12667 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12668 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12669 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12670 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12671 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12672 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12673 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12674 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12675 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12676 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12677 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12678 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12679 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12680 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12681 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12682 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12683 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12684 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12685 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12686 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12687 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12688 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12689 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12690 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12691 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12692 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12693 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12694 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12695 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12696 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12697 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12698 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12699 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12700 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12701 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12702 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12703 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12704 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12705 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12706 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12707 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12708 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12709 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12710 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12711 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12712 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12713 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12714 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12715 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12716 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12717 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12718 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12719 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12720 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12721 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12722 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12723 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12724 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12725 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12726 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12727 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12728 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12729 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12730 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12731 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12732 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12733 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12734 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12735 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12736 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12737 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12738 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12739 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12740 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12741 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12742 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12743 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12744 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12745 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12746 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12747 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12748 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12749 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12750 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12751 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12752 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12753 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12754 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12755 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12756 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12757 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12758 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12759 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12760 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12761 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12762 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12763 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12764 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12765 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12766 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12767 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12768 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12769 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12770 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12771 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12772 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12773 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12774 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12775 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12776 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12777 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12778 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12779 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12780 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12781 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12782 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12783 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12784 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12785 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12786 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12787 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12788 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12789 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12790 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12791 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12792 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12793 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12794 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12795 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12796 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12797 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12798 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12799 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12800 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12801 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12802 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12803 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12804 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12805 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12806 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12807 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12808 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12809 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12810 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12811 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12812 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12813 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12814 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12815 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12816 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12817 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12818 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12819 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12820 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12821 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12822 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12823 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12824 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12825 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12826 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12827 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12828 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12829 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12830 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12831 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12832 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12833 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12834 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12835 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12836 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12837 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12838 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12839 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12840 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12841 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12842 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12843 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12844 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12845 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12846 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12847 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12848 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12849 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12850 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12851 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12852 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12853 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12854 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12855 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12856 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12857 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12858 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12859 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12860 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12861 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12862 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12863 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12864 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12865 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12866 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12867 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12868 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12869 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12870 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12871 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12872 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12873 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12874 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12875 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12876 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12877 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12878 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12879 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12880 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12881 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12882 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12883 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12884 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12885 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12886 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12887 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12888 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12889 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12890 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12891 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12892 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12893 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12894 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12895 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12896 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12897 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12898 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12899 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12900 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12901 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12902 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12903 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12904 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12905 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12906 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12907 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12908 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12909 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12910 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12911 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12912 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12913 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12914 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12915 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12916 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12917 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12918 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12919 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12920 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12921 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12922 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12923 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12924 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12925 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12926 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12927 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12928 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12929 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12930 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12931 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12932 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12933 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12934 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12935 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12936 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12937 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12938 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12939 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12940 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12941 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12942 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12943 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12944 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12945 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12946 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12947 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12948 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12949 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12950 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12951 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12952 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12953 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12954 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12955 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12956 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12957 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12958 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12959 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12960 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12961 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12962 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12963 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12964 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12965 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12966 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12967 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12968 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12969 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12970 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12971 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12972 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12973 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12974 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12975 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12976 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12977 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12978 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12979 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12980 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12981 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12982 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12983 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12984 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12985 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12986 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12987 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12988 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12989 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12990 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12991 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12992 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12993 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12994 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12995 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12996 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12997 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12998 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_12999 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13000 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13001 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13002 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13003 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13004 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13005 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13006 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13007 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13008 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13009 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13010 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13011 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13012 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13013 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13014 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13015 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13016 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13017 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13018 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13019 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13020 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13021 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13022 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13023 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13024 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13025 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13026 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13027 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13028 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13029 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13030 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13031 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13032 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13033 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13034 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13035 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13036 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13037 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13038 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13039 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13040 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13041 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13042 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13043 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13044 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13045 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13046 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13047 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13048 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13049 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13050 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13051 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13052 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13053 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13054 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13055 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13056 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13057 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13058 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13059 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13060 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13061 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13062 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13063 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13064 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13065 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13066 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13067 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13068 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13069 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13070 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13071 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13072 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13073 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13074 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13075 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13076 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13077 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13078 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13079 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13080 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13081 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13082 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13083 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13084 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13085 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13086 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13087 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13088 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13089 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13090 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13091 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13092 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13093 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13094 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13095 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13096 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13097 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13098 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13099 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13100 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13101 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13102 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13103 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13104 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13105 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13106 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13107 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13108 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13109 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13110 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13111 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13112 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13113 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13114 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13115 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13116 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13117 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13118 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13119 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13120 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13121 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13122 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13123 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13124 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13125 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13126 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13127 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13128 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13129 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13130 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13131 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13132 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13133 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13134 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13135 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13136 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13137 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13138 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13139 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13140 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13141 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13142 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13143 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13144 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13145 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13146 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13147 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13148 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13149 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13150 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13151 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13152 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13153 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13154 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13155 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13156 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13157 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13158 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13159 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13160 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13161 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13162 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13163 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13164 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13165 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13166 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13167 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13168 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13169 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13170 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13171 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13172 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13173 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13174 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13175 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13176 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13177 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13178 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13179 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13180 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13181 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13182 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13183 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13184 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13185 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13186 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13187 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13188 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13189 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13190 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13191 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13192 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13193 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13194 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13195 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13196 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13197 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13198 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13199 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13200 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13201 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13202 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13203 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13204 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13205 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13206 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13207 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13208 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13209 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13210 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13211 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13212 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13213 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13214 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13215 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13216 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13217 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13218 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13219 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13220 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13221 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13222 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13223 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13224 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13225 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13226 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13227 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13228 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13229 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13230 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13231 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13232 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13233 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13234 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13235 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13236 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13237 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13238 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13239 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13240 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13241 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13242 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13243 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13244 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13245 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13246 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13247 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13248 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13249 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13250 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13251 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13252 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13253 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13254 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13255 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13256 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13257 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13258 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13259 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13260 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13261 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13262 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13263 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13264 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13265 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13266 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13267 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13268 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13269 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13270 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13271 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13272 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13273 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13274 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13275 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13276 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13277 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13278 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13279 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13280 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13281 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13282 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13283 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13284 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13285 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13286 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13287 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13288 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13289 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13290 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13291 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13292 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13293 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13294 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13295 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13296 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13297 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13298 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13299 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13300 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13301 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13302 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13303 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13304 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13305 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13306 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13307 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13308 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13309 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13310 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13311 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13312 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13313 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13314 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13315 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13316 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13317 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13318 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13319 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13320 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13321 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13322 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13323 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13324 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13325 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13326 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13327 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13328 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13329 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13330 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13331 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13332 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13333 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13334 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13335 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13336 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13337 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13338 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13339 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13340 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13341 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13342 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13343 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13344 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13345 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13346 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13347 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13348 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13349 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13350 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13351 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13352 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13353 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13354 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13355 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13356 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13357 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13358 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13359 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13360 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13361 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13362 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13363 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13364 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13365 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13366 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13367 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13368 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13369 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13370 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13371 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13372 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13373 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13374 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13375 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13376 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13377 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13378 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13379 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13380 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13381 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13382 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13383 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13384 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13385 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13386 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13387 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13388 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13389 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13390 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13391 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13392 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13393 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13394 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13395 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13396 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13397 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13398 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13399 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13400 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13401 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13402 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13403 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13404 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13405 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13406 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13407 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13408 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13409 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13410 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13411 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13412 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13413 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13414 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13415 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13416 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13417 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13418 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13419 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13420 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13421 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13422 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13423 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13424 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13425 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13426 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13427 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13428 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13429 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13430 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13431 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13432 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13433 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13434 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13435 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13436 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13437 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13438 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_13439 | idtac].
 destruct (in_nil HIn_S).
Qed.

