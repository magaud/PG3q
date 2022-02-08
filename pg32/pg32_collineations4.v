Require Import ssreflect ssrfun ssrbool.
Require Import Generic.lemmas.
Require Import PG32.pg32_inductive PG32.pg32_spreads_collineations.
Require Import PG32.pg32_automorphisms.
Require Import PG32.pg32_automorphisms_inv.
Require Import Lists.List.
Import ListNotations.
Require Import Arith.

Lemma collineation_5376 : is_collineation fp_5376 fl_5376.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5376 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5376 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5376.

Lemma collineation_5377 : is_collineation fp_5377 fl_5377.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5377 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5377 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5377.

Lemma collineation_5378 : is_collineation fp_5378 fl_5378.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5378 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5378 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5378.

Lemma collineation_5379 : is_collineation fp_5379 fl_5379.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5379 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5379 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5379.

Lemma collineation_5380 : is_collineation fp_5380 fl_5380.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5380 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5380 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5380.

Lemma collineation_5381 : is_collineation fp_5381 fl_5381.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5381 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5381 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5381.

Lemma collineation_5382 : is_collineation fp_5382 fl_5382.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5382 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5382 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5382.

Lemma collineation_5383 : is_collineation fp_5383 fl_5383.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5383 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5383 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5383.

Lemma collineation_5384 : is_collineation fp_5384 fl_5384.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5384 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5384 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5384.

Lemma collineation_5385 : is_collineation fp_5385 fl_5385.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5385 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5385 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5385.

Lemma collineation_5386 : is_collineation fp_5386 fl_5386.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5386 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5386 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5386.

Lemma collineation_5387 : is_collineation fp_5387 fl_5387.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5387 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5387 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5387.

Lemma collineation_5388 : is_collineation fp_5388 fl_5388.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5388 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5388 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5388.

Lemma collineation_5389 : is_collineation fp_5389 fl_5389.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5389 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5389 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5389.

Lemma collineation_5390 : is_collineation fp_5390 fl_5390.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5390 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5390 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5390.

Lemma collineation_5391 : is_collineation fp_5391 fl_5391.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5391 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5391 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5391.

Lemma collineation_5392 : is_collineation fp_5392 fl_5392.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5392 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5392 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5392.

Lemma collineation_5393 : is_collineation fp_5393 fl_5393.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5393 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5393 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5393.

Lemma collineation_5394 : is_collineation fp_5394 fl_5394.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5394 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5394 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5394.

Lemma collineation_5395 : is_collineation fp_5395 fl_5395.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5395 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5395 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5395.

Lemma collineation_5396 : is_collineation fp_5396 fl_5396.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5396 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5396 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5396.

Lemma collineation_5397 : is_collineation fp_5397 fl_5397.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5397 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5397 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5397.

Lemma collineation_5398 : is_collineation fp_5398 fl_5398.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5398 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5398 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5398.

Lemma collineation_5399 : is_collineation fp_5399 fl_5399.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5399 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5399 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5399.

Lemma collineation_5400 : is_collineation fp_5400 fl_5400.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5400 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5400 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5400.

Lemma collineation_5401 : is_collineation fp_5401 fl_5401.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5401 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5401 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5401.

Lemma collineation_5402 : is_collineation fp_5402 fl_5402.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5402 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5402 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5402.

Lemma collineation_5403 : is_collineation fp_5403 fl_5403.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5403 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5403 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5403.

Lemma collineation_5404 : is_collineation fp_5404 fl_5404.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5404 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5404 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5404.

Lemma collineation_5405 : is_collineation fp_5405 fl_5405.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5405 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5405 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5405.

Lemma collineation_5406 : is_collineation fp_5406 fl_5406.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5406 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5406 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5406.

Lemma collineation_5407 : is_collineation fp_5407 fl_5407.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5407 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5407 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5407.

Lemma collineation_5408 : is_collineation fp_5408 fl_5408.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5408 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5408 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5408.

Lemma collineation_5409 : is_collineation fp_5409 fl_5409.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5409 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5409 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5409.

Lemma collineation_5410 : is_collineation fp_5410 fl_5410.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5410 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5410 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5410.

Lemma collineation_5411 : is_collineation fp_5411 fl_5411.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5411 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5411 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5411.

Lemma collineation_5412 : is_collineation fp_5412 fl_5412.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5412 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5412 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5412.

Lemma collineation_5413 : is_collineation fp_5413 fl_5413.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5413 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5413 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5413.

Lemma collineation_5414 : is_collineation fp_5414 fl_5414.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5414 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5414 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5414.

Lemma collineation_5415 : is_collineation fp_5415 fl_5415.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5415 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5415 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5415.

Lemma collineation_5416 : is_collineation fp_5416 fl_5416.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5416 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5416 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5416.

Lemma collineation_5417 : is_collineation fp_5417 fl_5417.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5417 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5417 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5417.

Lemma collineation_5418 : is_collineation fp_5418 fl_5418.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5418 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5418 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5418.

Lemma collineation_5419 : is_collineation fp_5419 fl_5419.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5419 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5419 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5419.

Lemma collineation_5420 : is_collineation fp_5420 fl_5420.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5420 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5420 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5420.

Lemma collineation_5421 : is_collineation fp_5421 fl_5421.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5421 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5421 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5421.

Lemma collineation_5422 : is_collineation fp_5422 fl_5422.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5422 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5422 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5422.

Lemma collineation_5423 : is_collineation fp_5423 fl_5423.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5423 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5423 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5423.

Lemma collineation_5424 : is_collineation fp_5424 fl_5424.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5424 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5424 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5424.

Lemma collineation_5425 : is_collineation fp_5425 fl_5425.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5425 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5425 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5425.

Lemma collineation_5426 : is_collineation fp_5426 fl_5426.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5426 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5426 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5426.

Lemma collineation_5427 : is_collineation fp_5427 fl_5427.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5427 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5427 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5427.

Lemma collineation_5428 : is_collineation fp_5428 fl_5428.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5428 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5428 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5428.

Lemma collineation_5429 : is_collineation fp_5429 fl_5429.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5429 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5429 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5429.

Lemma collineation_5430 : is_collineation fp_5430 fl_5430.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5430 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5430 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5430.

Lemma collineation_5431 : is_collineation fp_5431 fl_5431.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5431 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5431 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5431.

Lemma collineation_5432 : is_collineation fp_5432 fl_5432.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5432 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5432 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5432.

Lemma collineation_5433 : is_collineation fp_5433 fl_5433.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5433 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5433 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5433.

Lemma collineation_5434 : is_collineation fp_5434 fl_5434.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5434 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5434 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5434.

Lemma collineation_5435 : is_collineation fp_5435 fl_5435.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5435 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5435 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5435.

Lemma collineation_5436 : is_collineation fp_5436 fl_5436.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5436 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5436 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5436.

Lemma collineation_5437 : is_collineation fp_5437 fl_5437.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5437 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5437 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5437.

Lemma collineation_5438 : is_collineation fp_5438 fl_5438.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5438 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5438 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5438.

Lemma collineation_5439 : is_collineation fp_5439 fl_5439.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5439 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5439 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5439.

Lemma collineation_5440 : is_collineation fp_5440 fl_5440.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5440 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5440 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5440.

Lemma collineation_5441 : is_collineation fp_5441 fl_5441.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5441 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5441 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5441.

Lemma collineation_5442 : is_collineation fp_5442 fl_5442.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5442 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5442 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5442.

Lemma collineation_5443 : is_collineation fp_5443 fl_5443.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5443 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5443 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5443.

Lemma collineation_5444 : is_collineation fp_5444 fl_5444.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5444 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5444 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5444.

Lemma collineation_5445 : is_collineation fp_5445 fl_5445.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5445 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5445 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5445.

Lemma collineation_5446 : is_collineation fp_5446 fl_5446.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5446 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5446 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5446.

Lemma collineation_5447 : is_collineation fp_5447 fl_5447.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5447 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5447 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5447.

Lemma collineation_5448 : is_collineation fp_5448 fl_5448.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5448 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5448 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5448.

Lemma collineation_5449 : is_collineation fp_5449 fl_5449.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5449 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5449 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5449.

Lemma collineation_5450 : is_collineation fp_5450 fl_5450.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5450 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5450 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5450.

Lemma collineation_5451 : is_collineation fp_5451 fl_5451.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5451 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5451 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5451.

Lemma collineation_5452 : is_collineation fp_5452 fl_5452.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5452 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5452 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5452.

Lemma collineation_5453 : is_collineation fp_5453 fl_5453.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5453 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5453 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5453.

Lemma collineation_5454 : is_collineation fp_5454 fl_5454.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5454 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5454 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5454.

Lemma collineation_5455 : is_collineation fp_5455 fl_5455.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5455 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5455 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5455.

Lemma collineation_5456 : is_collineation fp_5456 fl_5456.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5456 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5456 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5456.

Lemma collineation_5457 : is_collineation fp_5457 fl_5457.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5457 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5457 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5457.

Lemma collineation_5458 : is_collineation fp_5458 fl_5458.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5458 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5458 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5458.

Lemma collineation_5459 : is_collineation fp_5459 fl_5459.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5459 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5459 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5459.

Lemma collineation_5460 : is_collineation fp_5460 fl_5460.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5460 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5460 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5460.

Lemma collineation_5461 : is_collineation fp_5461 fl_5461.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5461 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5461 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5461.

Lemma collineation_5462 : is_collineation fp_5462 fl_5462.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5462 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5462 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5462.

Lemma collineation_5463 : is_collineation fp_5463 fl_5463.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5463 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5463 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5463.

Lemma collineation_5464 : is_collineation fp_5464 fl_5464.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5464 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5464 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5464.

Lemma collineation_5465 : is_collineation fp_5465 fl_5465.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5465 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5465 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5465.

Lemma collineation_5466 : is_collineation fp_5466 fl_5466.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5466 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5466 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5466.

Lemma collineation_5467 : is_collineation fp_5467 fl_5467.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5467 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5467 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5467.

Lemma collineation_5468 : is_collineation fp_5468 fl_5468.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5468 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5468 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5468.

Lemma collineation_5469 : is_collineation fp_5469 fl_5469.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5469 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5469 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5469.

Lemma collineation_5470 : is_collineation fp_5470 fl_5470.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5470 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5470 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5470.

Lemma collineation_5471 : is_collineation fp_5471 fl_5471.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5471 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5471 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5471.

Lemma collineation_5472 : is_collineation fp_5472 fl_5472.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5472 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5472 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5472.

Lemma collineation_5473 : is_collineation fp_5473 fl_5473.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5473 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5473 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5473.

Lemma collineation_5474 : is_collineation fp_5474 fl_5474.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5474 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5474 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5474.

Lemma collineation_5475 : is_collineation fp_5475 fl_5475.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5475 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5475 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5475.

Lemma collineation_5476 : is_collineation fp_5476 fl_5476.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5476 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5476 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5476.

Lemma collineation_5477 : is_collineation fp_5477 fl_5477.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5477 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5477 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5477.

Lemma collineation_5478 : is_collineation fp_5478 fl_5478.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5478 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5478 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5478.

Lemma collineation_5479 : is_collineation fp_5479 fl_5479.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5479 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5479 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5479.

Lemma collineation_5480 : is_collineation fp_5480 fl_5480.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5480 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5480 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5480.

Lemma collineation_5481 : is_collineation fp_5481 fl_5481.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5481 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5481 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5481.

Lemma collineation_5482 : is_collineation fp_5482 fl_5482.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5482 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5482 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5482.

Lemma collineation_5483 : is_collineation fp_5483 fl_5483.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5483 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5483 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5483.

Lemma collineation_5484 : is_collineation fp_5484 fl_5484.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5484 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5484 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5484.

Lemma collineation_5485 : is_collineation fp_5485 fl_5485.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5485 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5485 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5485.

Lemma collineation_5486 : is_collineation fp_5486 fl_5486.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5486 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5486 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5486.

Lemma collineation_5487 : is_collineation fp_5487 fl_5487.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5487 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5487 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5487.

Lemma collineation_5488 : is_collineation fp_5488 fl_5488.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5488 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5488 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5488.

Lemma collineation_5489 : is_collineation fp_5489 fl_5489.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5489 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5489 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5489.

Lemma collineation_5490 : is_collineation fp_5490 fl_5490.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5490 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5490 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5490.

Lemma collineation_5491 : is_collineation fp_5491 fl_5491.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5491 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5491 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5491.

Lemma collineation_5492 : is_collineation fp_5492 fl_5492.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5492 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5492 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5492.

Lemma collineation_5493 : is_collineation fp_5493 fl_5493.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5493 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5493 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5493.

Lemma collineation_5494 : is_collineation fp_5494 fl_5494.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5494 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5494 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5494.

Lemma collineation_5495 : is_collineation fp_5495 fl_5495.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5495 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5495 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5495.

Lemma collineation_5496 : is_collineation fp_5496 fl_5496.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5496 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5496 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5496.

Lemma collineation_5497 : is_collineation fp_5497 fl_5497.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5497 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5497 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5497.

Lemma collineation_5498 : is_collineation fp_5498 fl_5498.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5498 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5498 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5498.

Lemma collineation_5499 : is_collineation fp_5499 fl_5499.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5499 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5499 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5499.

Lemma collineation_5500 : is_collineation fp_5500 fl_5500.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5500 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5500 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5500.

Lemma collineation_5501 : is_collineation fp_5501 fl_5501.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5501 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5501 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5501.

Lemma collineation_5502 : is_collineation fp_5502 fl_5502.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5502 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5502 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5502.

Lemma collineation_5503 : is_collineation fp_5503 fl_5503.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5503 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5503 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5503.

Lemma collineation_5504 : is_collineation fp_5504 fl_5504.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5504 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5504 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5504.

Lemma collineation_5505 : is_collineation fp_5505 fl_5505.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5505 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5505 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5505.

Lemma collineation_5506 : is_collineation fp_5506 fl_5506.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5506 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5506 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5506.

Lemma collineation_5507 : is_collineation fp_5507 fl_5507.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5507 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5507 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5507.

Lemma collineation_5508 : is_collineation fp_5508 fl_5508.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5508 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5508 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5508.

Lemma collineation_5509 : is_collineation fp_5509 fl_5509.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5509 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5509 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5509.

Lemma collineation_5510 : is_collineation fp_5510 fl_5510.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5510 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5510 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5510.

Lemma collineation_5511 : is_collineation fp_5511 fl_5511.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5511 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5511 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5511.

Lemma collineation_5512 : is_collineation fp_5512 fl_5512.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5512 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5512 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5512.

Lemma collineation_5513 : is_collineation fp_5513 fl_5513.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5513 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5513 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5513.

Lemma collineation_5514 : is_collineation fp_5514 fl_5514.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5514 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5514 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5514.

Lemma collineation_5515 : is_collineation fp_5515 fl_5515.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5515 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5515 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5515.

Lemma collineation_5516 : is_collineation fp_5516 fl_5516.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5516 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5516 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5516.

Lemma collineation_5517 : is_collineation fp_5517 fl_5517.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5517 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5517 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5517.

Lemma collineation_5518 : is_collineation fp_5518 fl_5518.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5518 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5518 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5518.

Lemma collineation_5519 : is_collineation fp_5519 fl_5519.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5519 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5519 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5519.

Lemma collineation_5520 : is_collineation fp_5520 fl_5520.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5520 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5520 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5520.

Lemma collineation_5521 : is_collineation fp_5521 fl_5521.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5521 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5521 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5521.

Lemma collineation_5522 : is_collineation fp_5522 fl_5522.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5522 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5522 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5522.

Lemma collineation_5523 : is_collineation fp_5523 fl_5523.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5523 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5523 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5523.

Lemma collineation_5524 : is_collineation fp_5524 fl_5524.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5524 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5524 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5524.

Lemma collineation_5525 : is_collineation fp_5525 fl_5525.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5525 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5525 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5525.

Lemma collineation_5526 : is_collineation fp_5526 fl_5526.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5526 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5526 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5526.

Lemma collineation_5527 : is_collineation fp_5527 fl_5527.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5527 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5527 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5527.

Lemma collineation_5528 : is_collineation fp_5528 fl_5528.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5528 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5528 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5528.

Lemma collineation_5529 : is_collineation fp_5529 fl_5529.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5529 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5529 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5529.

Lemma collineation_5530 : is_collineation fp_5530 fl_5530.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5530 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5530 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5530.

Lemma collineation_5531 : is_collineation fp_5531 fl_5531.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5531 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5531 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5531.

Lemma collineation_5532 : is_collineation fp_5532 fl_5532.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5532 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5532 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5532.

Lemma collineation_5533 : is_collineation fp_5533 fl_5533.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5533 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5533 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5533.

Lemma collineation_5534 : is_collineation fp_5534 fl_5534.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5534 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5534 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5534.

Lemma collineation_5535 : is_collineation fp_5535 fl_5535.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5535 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5535 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5535.

Lemma collineation_5536 : is_collineation fp_5536 fl_5536.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5536 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5536 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5536.

Lemma collineation_5537 : is_collineation fp_5537 fl_5537.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5537 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5537 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5537.

Lemma collineation_5538 : is_collineation fp_5538 fl_5538.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5538 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5538 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5538.

Lemma collineation_5539 : is_collineation fp_5539 fl_5539.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5539 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5539 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5539.

Lemma collineation_5540 : is_collineation fp_5540 fl_5540.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5540 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5540 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5540.

Lemma collineation_5541 : is_collineation fp_5541 fl_5541.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5541 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5541 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5541.

Lemma collineation_5542 : is_collineation fp_5542 fl_5542.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5542 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5542 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5542.

Lemma collineation_5543 : is_collineation fp_5543 fl_5543.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5543 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5543 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5543.

Lemma collineation_5544 : is_collineation fp_5544 fl_5544.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5544 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5544 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5544.

Lemma collineation_5545 : is_collineation fp_5545 fl_5545.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5545 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5545 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5545.

Lemma collineation_5546 : is_collineation fp_5546 fl_5546.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5546 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5546 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5546.

Lemma collineation_5547 : is_collineation fp_5547 fl_5547.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5547 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5547 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5547.

Lemma collineation_5548 : is_collineation fp_5548 fl_5548.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5548 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5548 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5548.

Lemma collineation_5549 : is_collineation fp_5549 fl_5549.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5549 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5549 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5549.

Lemma collineation_5550 : is_collineation fp_5550 fl_5550.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5550 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5550 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5550.

Lemma collineation_5551 : is_collineation fp_5551 fl_5551.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5551 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5551 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5551.

Lemma collineation_5552 : is_collineation fp_5552 fl_5552.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5552 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5552 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5552.

Lemma collineation_5553 : is_collineation fp_5553 fl_5553.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5553 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5553 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5553.

Lemma collineation_5554 : is_collineation fp_5554 fl_5554.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5554 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5554 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5554.

Lemma collineation_5555 : is_collineation fp_5555 fl_5555.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5555 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5555 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5555.

Lemma collineation_5556 : is_collineation fp_5556 fl_5556.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5556 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5556 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5556.

Lemma collineation_5557 : is_collineation fp_5557 fl_5557.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5557 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5557 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5557.

Lemma collineation_5558 : is_collineation fp_5558 fl_5558.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5558 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5558 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5558.

Lemma collineation_5559 : is_collineation fp_5559 fl_5559.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5559 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5559 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5559.

Lemma collineation_5560 : is_collineation fp_5560 fl_5560.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5560 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5560 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5560.

Lemma collineation_5561 : is_collineation fp_5561 fl_5561.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5561 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5561 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5561.

Lemma collineation_5562 : is_collineation fp_5562 fl_5562.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5562 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5562 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5562.

Lemma collineation_5563 : is_collineation fp_5563 fl_5563.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5563 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5563 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5563.

Lemma collineation_5564 : is_collineation fp_5564 fl_5564.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5564 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5564 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5564.

Lemma collineation_5565 : is_collineation fp_5565 fl_5565.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5565 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5565 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5565.

Lemma collineation_5566 : is_collineation fp_5566 fl_5566.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5566 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5566 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5566.

Lemma collineation_5567 : is_collineation fp_5567 fl_5567.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5567 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5567 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5567.

Lemma collineation_5568 : is_collineation fp_5568 fl_5568.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5568 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5568 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5568.

Lemma collineation_5569 : is_collineation fp_5569 fl_5569.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5569 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5569 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5569.

Lemma collineation_5570 : is_collineation fp_5570 fl_5570.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5570 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5570 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5570.

Lemma collineation_5571 : is_collineation fp_5571 fl_5571.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5571 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5571 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5571.

Lemma collineation_5572 : is_collineation fp_5572 fl_5572.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5572 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5572 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5572.

Lemma collineation_5573 : is_collineation fp_5573 fl_5573.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5573 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5573 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5573.

Lemma collineation_5574 : is_collineation fp_5574 fl_5574.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5574 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5574 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5574.

Lemma collineation_5575 : is_collineation fp_5575 fl_5575.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5575 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5575 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5575.

Lemma collineation_5576 : is_collineation fp_5576 fl_5576.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5576 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5576 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5576.

Lemma collineation_5577 : is_collineation fp_5577 fl_5577.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5577 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5577 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5577.

Lemma collineation_5578 : is_collineation fp_5578 fl_5578.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5578 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5578 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5578.

Lemma collineation_5579 : is_collineation fp_5579 fl_5579.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5579 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5579 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5579.

Lemma collineation_5580 : is_collineation fp_5580 fl_5580.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5580 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5580 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5580.

Lemma collineation_5581 : is_collineation fp_5581 fl_5581.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5581 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5581 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5581.

Lemma collineation_5582 : is_collineation fp_5582 fl_5582.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5582 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5582 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5582.

Lemma collineation_5583 : is_collineation fp_5583 fl_5583.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5583 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5583 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5583.

Lemma collineation_5584 : is_collineation fp_5584 fl_5584.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5584 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5584 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5584.

Lemma collineation_5585 : is_collineation fp_5585 fl_5585.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5585 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5585 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5585.

Lemma collineation_5586 : is_collineation fp_5586 fl_5586.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5586 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5586 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5586.

Lemma collineation_5587 : is_collineation fp_5587 fl_5587.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5587 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5587 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5587.

Lemma collineation_5588 : is_collineation fp_5588 fl_5588.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5588 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5588 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5588.

Lemma collineation_5589 : is_collineation fp_5589 fl_5589.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5589 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5589 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5589.

Lemma collineation_5590 : is_collineation fp_5590 fl_5590.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5590 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5590 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5590.

Lemma collineation_5591 : is_collineation fp_5591 fl_5591.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5591 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5591 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5591.

Lemma collineation_5592 : is_collineation fp_5592 fl_5592.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5592 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5592 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5592.

Lemma collineation_5593 : is_collineation fp_5593 fl_5593.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5593 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5593 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5593.

Lemma collineation_5594 : is_collineation fp_5594 fl_5594.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5594 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5594 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5594.

Lemma collineation_5595 : is_collineation fp_5595 fl_5595.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5595 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5595 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5595.

Lemma collineation_5596 : is_collineation fp_5596 fl_5596.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5596 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5596 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5596.

Lemma collineation_5597 : is_collineation fp_5597 fl_5597.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5597 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5597 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5597.

Lemma collineation_5598 : is_collineation fp_5598 fl_5598.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5598 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5598 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5598.

Lemma collineation_5599 : is_collineation fp_5599 fl_5599.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5599 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5599 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5599.

Lemma collineation_5600 : is_collineation fp_5600 fl_5600.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5600 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5600 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5600.

Lemma collineation_5601 : is_collineation fp_5601 fl_5601.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5601 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5601 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5601.

Lemma collineation_5602 : is_collineation fp_5602 fl_5602.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5602 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5602 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5602.

Lemma collineation_5603 : is_collineation fp_5603 fl_5603.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5603 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5603 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5603.

Lemma collineation_5604 : is_collineation fp_5604 fl_5604.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5604 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5604 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5604.

Lemma collineation_5605 : is_collineation fp_5605 fl_5605.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5605 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5605 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5605.

Lemma collineation_5606 : is_collineation fp_5606 fl_5606.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5606 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5606 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5606.

Lemma collineation_5607 : is_collineation fp_5607 fl_5607.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5607 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5607 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5607.

Lemma collineation_5608 : is_collineation fp_5608 fl_5608.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5608 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5608 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5608.

Lemma collineation_5609 : is_collineation fp_5609 fl_5609.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5609 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5609 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5609.

Lemma collineation_5610 : is_collineation fp_5610 fl_5610.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5610 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5610 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5610.

Lemma collineation_5611 : is_collineation fp_5611 fl_5611.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5611 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5611 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5611.

Lemma collineation_5612 : is_collineation fp_5612 fl_5612.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5612 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5612 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5612.

Lemma collineation_5613 : is_collineation fp_5613 fl_5613.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5613 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5613 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5613.

Lemma collineation_5614 : is_collineation fp_5614 fl_5614.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5614 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5614 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5614.

Lemma collineation_5615 : is_collineation fp_5615 fl_5615.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5615 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5615 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5615.

Lemma collineation_5616 : is_collineation fp_5616 fl_5616.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5616 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5616 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5616.

Lemma collineation_5617 : is_collineation fp_5617 fl_5617.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5617 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5617 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5617.

Lemma collineation_5618 : is_collineation fp_5618 fl_5618.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5618 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5618 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5618.

Lemma collineation_5619 : is_collineation fp_5619 fl_5619.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5619 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5619 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5619.

Lemma collineation_5620 : is_collineation fp_5620 fl_5620.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5620 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5620 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5620.

Lemma collineation_5621 : is_collineation fp_5621 fl_5621.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5621 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5621 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5621.

Lemma collineation_5622 : is_collineation fp_5622 fl_5622.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5622 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5622 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5622.

Lemma collineation_5623 : is_collineation fp_5623 fl_5623.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5623 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5623 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5623.

Lemma collineation_5624 : is_collineation fp_5624 fl_5624.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5624 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5624 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5624.

Lemma collineation_5625 : is_collineation fp_5625 fl_5625.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5625 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5625 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5625.

Lemma collineation_5626 : is_collineation fp_5626 fl_5626.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5626 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5626 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5626.

Lemma collineation_5627 : is_collineation fp_5627 fl_5627.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5627 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5627 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5627.

Lemma collineation_5628 : is_collineation fp_5628 fl_5628.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5628 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5628 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5628.

Lemma collineation_5629 : is_collineation fp_5629 fl_5629.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5629 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5629 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5629.

Lemma collineation_5630 : is_collineation fp_5630 fl_5630.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5630 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5630 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5630.

Lemma collineation_5631 : is_collineation fp_5631 fl_5631.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5631 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5631 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5631.

Lemma collineation_5632 : is_collineation fp_5632 fl_5632.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5632 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5632 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5632.

Lemma collineation_5633 : is_collineation fp_5633 fl_5633.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5633 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5633 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5633.

Lemma collineation_5634 : is_collineation fp_5634 fl_5634.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5634 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5634 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5634.

Lemma collineation_5635 : is_collineation fp_5635 fl_5635.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5635 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5635 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5635.

Lemma collineation_5636 : is_collineation fp_5636 fl_5636.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5636 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5636 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5636.

Lemma collineation_5637 : is_collineation fp_5637 fl_5637.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5637 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5637 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5637.

Lemma collineation_5638 : is_collineation fp_5638 fl_5638.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5638 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5638 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5638.

Lemma collineation_5639 : is_collineation fp_5639 fl_5639.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5639 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5639 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5639.

Lemma collineation_5640 : is_collineation fp_5640 fl_5640.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5640 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5640 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5640.

Lemma collineation_5641 : is_collineation fp_5641 fl_5641.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5641 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5641 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5641.

Lemma collineation_5642 : is_collineation fp_5642 fl_5642.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5642 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5642 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5642.

Lemma collineation_5643 : is_collineation fp_5643 fl_5643.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5643 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5643 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5643.

Lemma collineation_5644 : is_collineation fp_5644 fl_5644.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5644 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5644 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5644.

Lemma collineation_5645 : is_collineation fp_5645 fl_5645.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5645 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5645 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5645.

Lemma collineation_5646 : is_collineation fp_5646 fl_5646.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5646 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5646 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5646.

Lemma collineation_5647 : is_collineation fp_5647 fl_5647.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5647 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5647 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5647.

Lemma collineation_5648 : is_collineation fp_5648 fl_5648.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5648 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5648 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5648.

Lemma collineation_5649 : is_collineation fp_5649 fl_5649.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5649 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5649 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5649.

Lemma collineation_5650 : is_collineation fp_5650 fl_5650.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5650 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5650 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5650.

Lemma collineation_5651 : is_collineation fp_5651 fl_5651.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5651 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5651 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5651.

Lemma collineation_5652 : is_collineation fp_5652 fl_5652.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5652 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5652 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5652.

Lemma collineation_5653 : is_collineation fp_5653 fl_5653.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5653 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5653 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5653.

Lemma collineation_5654 : is_collineation fp_5654 fl_5654.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5654 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5654 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5654.

Lemma collineation_5655 : is_collineation fp_5655 fl_5655.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5655 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5655 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5655.

Lemma collineation_5656 : is_collineation fp_5656 fl_5656.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5656 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5656 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5656.

Lemma collineation_5657 : is_collineation fp_5657 fl_5657.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5657 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5657 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5657.

Lemma collineation_5658 : is_collineation fp_5658 fl_5658.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5658 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5658 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5658.

Lemma collineation_5659 : is_collineation fp_5659 fl_5659.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5659 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5659 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5659.

Lemma collineation_5660 : is_collineation fp_5660 fl_5660.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5660 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5660 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5660.

Lemma collineation_5661 : is_collineation fp_5661 fl_5661.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5661 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5661 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5661.

Lemma collineation_5662 : is_collineation fp_5662 fl_5662.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5662 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5662 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5662.

Lemma collineation_5663 : is_collineation fp_5663 fl_5663.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5663 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5663 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5663.

Lemma collineation_5664 : is_collineation fp_5664 fl_5664.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5664 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5664 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5664.

Lemma collineation_5665 : is_collineation fp_5665 fl_5665.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5665 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5665 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5665.

Lemma collineation_5666 : is_collineation fp_5666 fl_5666.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5666 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5666 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5666.

Lemma collineation_5667 : is_collineation fp_5667 fl_5667.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5667 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5667 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5667.

Lemma collineation_5668 : is_collineation fp_5668 fl_5668.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5668 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5668 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5668.

Lemma collineation_5669 : is_collineation fp_5669 fl_5669.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5669 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5669 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5669.

Lemma collineation_5670 : is_collineation fp_5670 fl_5670.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5670 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5670 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5670.

Lemma collineation_5671 : is_collineation fp_5671 fl_5671.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5671 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5671 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5671.

Lemma collineation_5672 : is_collineation fp_5672 fl_5672.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5672 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5672 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5672.

Lemma collineation_5673 : is_collineation fp_5673 fl_5673.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5673 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5673 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5673.

Lemma collineation_5674 : is_collineation fp_5674 fl_5674.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5674 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5674 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5674.

Lemma collineation_5675 : is_collineation fp_5675 fl_5675.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5675 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5675 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5675.

Lemma collineation_5676 : is_collineation fp_5676 fl_5676.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5676 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5676 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5676.

Lemma collineation_5677 : is_collineation fp_5677 fl_5677.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5677 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5677 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5677.

Lemma collineation_5678 : is_collineation fp_5678 fl_5678.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5678 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5678 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5678.

Lemma collineation_5679 : is_collineation fp_5679 fl_5679.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5679 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5679 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5679.

Lemma collineation_5680 : is_collineation fp_5680 fl_5680.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5680 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5680 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5680.

Lemma collineation_5681 : is_collineation fp_5681 fl_5681.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5681 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5681 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5681.

Lemma collineation_5682 : is_collineation fp_5682 fl_5682.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5682 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5682 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5682.

Lemma collineation_5683 : is_collineation fp_5683 fl_5683.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5683 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5683 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5683.

Lemma collineation_5684 : is_collineation fp_5684 fl_5684.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5684 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5684 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5684.

Lemma collineation_5685 : is_collineation fp_5685 fl_5685.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5685 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5685 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5685.

Lemma collineation_5686 : is_collineation fp_5686 fl_5686.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5686 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5686 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5686.

Lemma collineation_5687 : is_collineation fp_5687 fl_5687.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5687 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5687 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5687.

Lemma collineation_5688 : is_collineation fp_5688 fl_5688.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5688 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5688 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5688.

Lemma collineation_5689 : is_collineation fp_5689 fl_5689.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5689 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5689 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5689.

Lemma collineation_5690 : is_collineation fp_5690 fl_5690.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5690 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5690 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5690.

Lemma collineation_5691 : is_collineation fp_5691 fl_5691.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5691 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5691 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5691.

Lemma collineation_5692 : is_collineation fp_5692 fl_5692.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5692 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5692 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5692.

Lemma collineation_5693 : is_collineation fp_5693 fl_5693.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5693 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5693 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5693.

Lemma collineation_5694 : is_collineation fp_5694 fl_5694.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5694 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5694 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5694.

Lemma collineation_5695 : is_collineation fp_5695 fl_5695.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5695 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5695 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5695.

Lemma collineation_5696 : is_collineation fp_5696 fl_5696.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5696 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5696 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5696.

Lemma collineation_5697 : is_collineation fp_5697 fl_5697.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5697 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5697 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5697.

Lemma collineation_5698 : is_collineation fp_5698 fl_5698.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5698 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5698 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5698.

Lemma collineation_5699 : is_collineation fp_5699 fl_5699.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5699 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5699 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5699.

Lemma collineation_5700 : is_collineation fp_5700 fl_5700.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5700 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5700 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5700.

Lemma collineation_5701 : is_collineation fp_5701 fl_5701.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5701 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5701 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5701.

Lemma collineation_5702 : is_collineation fp_5702 fl_5702.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5702 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5702 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5702.

Lemma collineation_5703 : is_collineation fp_5703 fl_5703.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5703 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5703 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5703.

Lemma collineation_5704 : is_collineation fp_5704 fl_5704.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5704 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5704 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5704.

Lemma collineation_5705 : is_collineation fp_5705 fl_5705.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5705 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5705 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5705.

Lemma collineation_5706 : is_collineation fp_5706 fl_5706.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5706 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5706 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5706.

Lemma collineation_5707 : is_collineation fp_5707 fl_5707.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5707 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5707 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5707.

Lemma collineation_5708 : is_collineation fp_5708 fl_5708.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5708 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5708 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5708.

Lemma collineation_5709 : is_collineation fp_5709 fl_5709.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5709 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5709 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5709.

Lemma collineation_5710 : is_collineation fp_5710 fl_5710.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5710 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5710 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5710.

Lemma collineation_5711 : is_collineation fp_5711 fl_5711.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5711 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5711 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5711.

Lemma collineation_5712 : is_collineation fp_5712 fl_5712.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5712 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5712 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5712.

Lemma collineation_5713 : is_collineation fp_5713 fl_5713.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5713 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5713 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5713.

Lemma collineation_5714 : is_collineation fp_5714 fl_5714.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5714 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5714 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5714.

Lemma collineation_5715 : is_collineation fp_5715 fl_5715.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5715 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5715 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5715.

Lemma collineation_5716 : is_collineation fp_5716 fl_5716.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5716 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5716 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5716.

Lemma collineation_5717 : is_collineation fp_5717 fl_5717.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5717 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5717 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5717.

Lemma collineation_5718 : is_collineation fp_5718 fl_5718.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5718 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5718 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5718.

Lemma collineation_5719 : is_collineation fp_5719 fl_5719.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5719 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5719 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5719.

Lemma collineation_5720 : is_collineation fp_5720 fl_5720.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5720 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5720 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5720.

Lemma collineation_5721 : is_collineation fp_5721 fl_5721.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5721 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5721 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5721.

Lemma collineation_5722 : is_collineation fp_5722 fl_5722.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5722 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5722 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5722.

Lemma collineation_5723 : is_collineation fp_5723 fl_5723.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5723 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5723 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5723.

Lemma collineation_5724 : is_collineation fp_5724 fl_5724.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5724 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5724 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5724.

Lemma collineation_5725 : is_collineation fp_5725 fl_5725.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5725 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5725 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5725.

Lemma collineation_5726 : is_collineation fp_5726 fl_5726.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5726 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5726 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5726.

Lemma collineation_5727 : is_collineation fp_5727 fl_5727.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5727 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5727 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5727.

Lemma collineation_5728 : is_collineation fp_5728 fl_5728.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5728 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5728 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5728.

Lemma collineation_5729 : is_collineation fp_5729 fl_5729.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5729 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5729 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5729.

Lemma collineation_5730 : is_collineation fp_5730 fl_5730.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5730 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5730 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5730.

Lemma collineation_5731 : is_collineation fp_5731 fl_5731.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5731 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5731 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5731.

Lemma collineation_5732 : is_collineation fp_5732 fl_5732.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5732 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5732 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5732.

Lemma collineation_5733 : is_collineation fp_5733 fl_5733.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5733 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5733 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5733.

Lemma collineation_5734 : is_collineation fp_5734 fl_5734.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5734 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5734 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5734.

Lemma collineation_5735 : is_collineation fp_5735 fl_5735.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5735 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5735 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5735.

Lemma collineation_5736 : is_collineation fp_5736 fl_5736.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5736 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5736 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5736.

Lemma collineation_5737 : is_collineation fp_5737 fl_5737.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5737 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5737 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5737.

Lemma collineation_5738 : is_collineation fp_5738 fl_5738.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5738 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5738 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5738.

Lemma collineation_5739 : is_collineation fp_5739 fl_5739.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5739 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5739 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5739.

Lemma collineation_5740 : is_collineation fp_5740 fl_5740.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5740 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5740 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5740.

Lemma collineation_5741 : is_collineation fp_5741 fl_5741.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5741 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5741 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5741.

Lemma collineation_5742 : is_collineation fp_5742 fl_5742.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5742 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5742 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5742.

Lemma collineation_5743 : is_collineation fp_5743 fl_5743.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5743 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5743 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5743.

Lemma collineation_5744 : is_collineation fp_5744 fl_5744.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5744 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5744 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5744.

Lemma collineation_5745 : is_collineation fp_5745 fl_5745.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5745 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5745 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5745.

Lemma collineation_5746 : is_collineation fp_5746 fl_5746.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5746 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5746 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5746.

Lemma collineation_5747 : is_collineation fp_5747 fl_5747.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5747 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5747 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5747.

Lemma collineation_5748 : is_collineation fp_5748 fl_5748.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5748 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5748 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5748.

Lemma collineation_5749 : is_collineation fp_5749 fl_5749.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5749 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5749 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5749.

Lemma collineation_5750 : is_collineation fp_5750 fl_5750.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5750 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5750 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5750.

Lemma collineation_5751 : is_collineation fp_5751 fl_5751.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5751 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5751 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5751.

Lemma collineation_5752 : is_collineation fp_5752 fl_5752.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5752 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5752 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5752.

Lemma collineation_5753 : is_collineation fp_5753 fl_5753.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5753 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5753 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5753.

Lemma collineation_5754 : is_collineation fp_5754 fl_5754.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5754 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5754 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5754.

Lemma collineation_5755 : is_collineation fp_5755 fl_5755.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5755 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5755 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5755.

Lemma collineation_5756 : is_collineation fp_5756 fl_5756.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5756 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5756 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5756.

Lemma collineation_5757 : is_collineation fp_5757 fl_5757.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5757 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5757 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5757.

Lemma collineation_5758 : is_collineation fp_5758 fl_5758.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5758 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5758 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5758.

Lemma collineation_5759 : is_collineation fp_5759 fl_5759.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5759 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5759 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5759.

Lemma collineation_5760 : is_collineation fp_5760 fl_5760.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5760 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5760 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5760.

Lemma collineation_5761 : is_collineation fp_5761 fl_5761.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5761 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5761 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5761.

Lemma collineation_5762 : is_collineation fp_5762 fl_5762.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5762 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5762 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5762.

Lemma collineation_5763 : is_collineation fp_5763 fl_5763.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5763 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5763 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5763.

Lemma collineation_5764 : is_collineation fp_5764 fl_5764.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5764 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5764 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5764.

Lemma collineation_5765 : is_collineation fp_5765 fl_5765.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5765 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5765 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5765.

Lemma collineation_5766 : is_collineation fp_5766 fl_5766.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5766 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5766 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5766.

Lemma collineation_5767 : is_collineation fp_5767 fl_5767.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5767 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5767 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5767.

Lemma collineation_5768 : is_collineation fp_5768 fl_5768.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5768 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5768 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5768.

Lemma collineation_5769 : is_collineation fp_5769 fl_5769.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5769 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5769 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5769.

Lemma collineation_5770 : is_collineation fp_5770 fl_5770.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5770 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5770 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5770.

Lemma collineation_5771 : is_collineation fp_5771 fl_5771.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5771 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5771 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5771.

Lemma collineation_5772 : is_collineation fp_5772 fl_5772.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5772 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5772 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5772.

Lemma collineation_5773 : is_collineation fp_5773 fl_5773.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5773 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5773 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5773.

Lemma collineation_5774 : is_collineation fp_5774 fl_5774.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5774 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5774 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5774.

Lemma collineation_5775 : is_collineation fp_5775 fl_5775.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5775 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5775 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5775.

Lemma collineation_5776 : is_collineation fp_5776 fl_5776.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5776 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5776 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5776.

Lemma collineation_5777 : is_collineation fp_5777 fl_5777.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5777 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5777 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5777.

Lemma collineation_5778 : is_collineation fp_5778 fl_5778.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5778 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5778 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5778.

Lemma collineation_5779 : is_collineation fp_5779 fl_5779.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5779 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5779 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5779.

Lemma collineation_5780 : is_collineation fp_5780 fl_5780.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5780 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5780 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5780.

Lemma collineation_5781 : is_collineation fp_5781 fl_5781.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5781 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5781 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5781.

Lemma collineation_5782 : is_collineation fp_5782 fl_5782.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5782 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5782 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5782.

Lemma collineation_5783 : is_collineation fp_5783 fl_5783.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5783 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5783 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5783.

Lemma collineation_5784 : is_collineation fp_5784 fl_5784.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5784 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5784 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5784.

Lemma collineation_5785 : is_collineation fp_5785 fl_5785.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5785 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5785 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5785.

Lemma collineation_5786 : is_collineation fp_5786 fl_5786.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5786 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5786 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5786.

Lemma collineation_5787 : is_collineation fp_5787 fl_5787.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5787 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5787 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5787.

Lemma collineation_5788 : is_collineation fp_5788 fl_5788.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5788 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5788 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5788.

Lemma collineation_5789 : is_collineation fp_5789 fl_5789.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5789 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5789 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5789.

Lemma collineation_5790 : is_collineation fp_5790 fl_5790.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5790 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5790 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5790.

Lemma collineation_5791 : is_collineation fp_5791 fl_5791.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5791 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5791 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5791.

Lemma collineation_5792 : is_collineation fp_5792 fl_5792.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5792 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5792 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5792.

Lemma collineation_5793 : is_collineation fp_5793 fl_5793.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5793 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5793 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5793.

Lemma collineation_5794 : is_collineation fp_5794 fl_5794.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5794 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5794 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5794.

Lemma collineation_5795 : is_collineation fp_5795 fl_5795.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5795 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5795 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5795.

Lemma collineation_5796 : is_collineation fp_5796 fl_5796.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5796 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5796 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5796.

Lemma collineation_5797 : is_collineation fp_5797 fl_5797.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5797 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5797 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5797.

Lemma collineation_5798 : is_collineation fp_5798 fl_5798.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5798 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5798 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5798.

Lemma collineation_5799 : is_collineation fp_5799 fl_5799.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5799 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5799 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5799.

Lemma collineation_5800 : is_collineation fp_5800 fl_5800.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5800 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5800 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5800.

Lemma collineation_5801 : is_collineation fp_5801 fl_5801.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5801 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5801 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5801.

Lemma collineation_5802 : is_collineation fp_5802 fl_5802.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5802 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5802 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5802.

Lemma collineation_5803 : is_collineation fp_5803 fl_5803.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5803 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5803 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5803.

Lemma collineation_5804 : is_collineation fp_5804 fl_5804.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5804 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5804 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5804.

Lemma collineation_5805 : is_collineation fp_5805 fl_5805.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5805 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5805 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5805.

Lemma collineation_5806 : is_collineation fp_5806 fl_5806.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5806 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5806 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5806.

Lemma collineation_5807 : is_collineation fp_5807 fl_5807.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5807 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5807 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5807.

Lemma collineation_5808 : is_collineation fp_5808 fl_5808.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5808 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5808 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5808.

Lemma collineation_5809 : is_collineation fp_5809 fl_5809.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5809 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5809 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5809.

Lemma collineation_5810 : is_collineation fp_5810 fl_5810.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5810 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5810 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5810.

Lemma collineation_5811 : is_collineation fp_5811 fl_5811.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5811 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5811 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5811.

Lemma collineation_5812 : is_collineation fp_5812 fl_5812.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5812 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5812 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5812.

Lemma collineation_5813 : is_collineation fp_5813 fl_5813.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5813 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5813 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5813.

Lemma collineation_5814 : is_collineation fp_5814 fl_5814.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5814 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5814 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5814.

Lemma collineation_5815 : is_collineation fp_5815 fl_5815.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5815 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5815 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5815.

Lemma collineation_5816 : is_collineation fp_5816 fl_5816.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5816 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5816 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5816.

Lemma collineation_5817 : is_collineation fp_5817 fl_5817.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5817 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5817 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5817.

Lemma collineation_5818 : is_collineation fp_5818 fl_5818.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5818 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5818 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5818.

Lemma collineation_5819 : is_collineation fp_5819 fl_5819.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5819 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5819 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5819.

Lemma collineation_5820 : is_collineation fp_5820 fl_5820.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5820 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5820 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5820.

Lemma collineation_5821 : is_collineation fp_5821 fl_5821.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5821 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5821 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5821.

Lemma collineation_5822 : is_collineation fp_5822 fl_5822.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5822 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5822 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5822.

Lemma collineation_5823 : is_collineation fp_5823 fl_5823.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5823 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5823 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5823.

Lemma collineation_5824 : is_collineation fp_5824 fl_5824.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5824 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5824 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5824.

Lemma collineation_5825 : is_collineation fp_5825 fl_5825.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5825 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5825 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5825.

Lemma collineation_5826 : is_collineation fp_5826 fl_5826.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5826 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5826 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5826.

Lemma collineation_5827 : is_collineation fp_5827 fl_5827.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5827 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5827 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5827.

Lemma collineation_5828 : is_collineation fp_5828 fl_5828.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5828 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5828 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5828.

Lemma collineation_5829 : is_collineation fp_5829 fl_5829.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5829 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5829 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5829.

Lemma collineation_5830 : is_collineation fp_5830 fl_5830.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5830 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5830 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5830.

Lemma collineation_5831 : is_collineation fp_5831 fl_5831.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5831 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5831 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5831.

Lemma collineation_5832 : is_collineation fp_5832 fl_5832.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5832 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5832 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5832.

Lemma collineation_5833 : is_collineation fp_5833 fl_5833.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5833 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5833 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5833.

Lemma collineation_5834 : is_collineation fp_5834 fl_5834.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5834 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5834 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5834.

Lemma collineation_5835 : is_collineation fp_5835 fl_5835.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5835 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5835 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5835.

Lemma collineation_5836 : is_collineation fp_5836 fl_5836.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5836 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5836 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5836.

Lemma collineation_5837 : is_collineation fp_5837 fl_5837.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5837 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5837 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5837.

Lemma collineation_5838 : is_collineation fp_5838 fl_5838.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5838 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5838 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5838.

Lemma collineation_5839 : is_collineation fp_5839 fl_5839.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5839 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5839 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5839.

Lemma collineation_5840 : is_collineation fp_5840 fl_5840.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5840 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5840 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5840.

Lemma collineation_5841 : is_collineation fp_5841 fl_5841.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5841 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5841 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5841.

Lemma collineation_5842 : is_collineation fp_5842 fl_5842.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5842 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5842 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5842.

Lemma collineation_5843 : is_collineation fp_5843 fl_5843.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5843 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5843 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5843.

Lemma collineation_5844 : is_collineation fp_5844 fl_5844.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5844 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5844 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5844.

Lemma collineation_5845 : is_collineation fp_5845 fl_5845.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5845 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5845 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5845.

Lemma collineation_5846 : is_collineation fp_5846 fl_5846.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5846 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5846 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5846.

Lemma collineation_5847 : is_collineation fp_5847 fl_5847.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5847 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5847 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5847.

Lemma collineation_5848 : is_collineation fp_5848 fl_5848.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5848 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5848 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5848.

Lemma collineation_5849 : is_collineation fp_5849 fl_5849.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5849 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5849 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5849.

Lemma collineation_5850 : is_collineation fp_5850 fl_5850.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5850 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5850 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5850.

Lemma collineation_5851 : is_collineation fp_5851 fl_5851.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5851 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5851 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5851.

Lemma collineation_5852 : is_collineation fp_5852 fl_5852.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5852 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5852 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5852.

Lemma collineation_5853 : is_collineation fp_5853 fl_5853.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5853 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5853 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5853.

Lemma collineation_5854 : is_collineation fp_5854 fl_5854.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5854 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5854 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5854.

Lemma collineation_5855 : is_collineation fp_5855 fl_5855.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5855 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5855 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5855.

Lemma collineation_5856 : is_collineation fp_5856 fl_5856.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5856 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5856 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5856.

Lemma collineation_5857 : is_collineation fp_5857 fl_5857.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5857 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5857 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5857.

Lemma collineation_5858 : is_collineation fp_5858 fl_5858.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5858 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5858 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5858.

Lemma collineation_5859 : is_collineation fp_5859 fl_5859.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5859 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5859 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5859.

Lemma collineation_5860 : is_collineation fp_5860 fl_5860.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5860 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5860 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5860.

Lemma collineation_5861 : is_collineation fp_5861 fl_5861.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5861 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5861 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5861.

Lemma collineation_5862 : is_collineation fp_5862 fl_5862.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5862 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5862 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5862.

Lemma collineation_5863 : is_collineation fp_5863 fl_5863.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5863 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5863 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5863.

Lemma collineation_5864 : is_collineation fp_5864 fl_5864.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5864 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5864 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5864.

Lemma collineation_5865 : is_collineation fp_5865 fl_5865.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5865 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5865 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5865.

Lemma collineation_5866 : is_collineation fp_5866 fl_5866.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5866 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5866 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5866.

Lemma collineation_5867 : is_collineation fp_5867 fl_5867.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5867 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5867 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5867.

Lemma collineation_5868 : is_collineation fp_5868 fl_5868.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5868 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5868 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5868.

Lemma collineation_5869 : is_collineation fp_5869 fl_5869.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5869 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5869 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5869.

Lemma collineation_5870 : is_collineation fp_5870 fl_5870.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5870 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5870 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5870.

Lemma collineation_5871 : is_collineation fp_5871 fl_5871.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5871 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5871 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5871.

Lemma collineation_5872 : is_collineation fp_5872 fl_5872.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5872 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5872 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5872.

Lemma collineation_5873 : is_collineation fp_5873 fl_5873.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5873 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5873 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5873.

Lemma collineation_5874 : is_collineation fp_5874 fl_5874.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5874 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5874 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5874.

Lemma collineation_5875 : is_collineation fp_5875 fl_5875.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5875 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5875 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5875.

Lemma collineation_5876 : is_collineation fp_5876 fl_5876.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5876 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5876 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5876.

Lemma collineation_5877 : is_collineation fp_5877 fl_5877.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5877 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5877 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5877.

Lemma collineation_5878 : is_collineation fp_5878 fl_5878.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5878 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5878 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5878.

Lemma collineation_5879 : is_collineation fp_5879 fl_5879.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5879 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5879 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5879.

Lemma collineation_5880 : is_collineation fp_5880 fl_5880.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5880 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5880 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5880.

Lemma collineation_5881 : is_collineation fp_5881 fl_5881.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5881 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5881 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5881.

Lemma collineation_5882 : is_collineation fp_5882 fl_5882.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5882 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5882 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5882.

Lemma collineation_5883 : is_collineation fp_5883 fl_5883.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5883 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5883 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5883.

Lemma collineation_5884 : is_collineation fp_5884 fl_5884.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5884 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5884 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5884.

Lemma collineation_5885 : is_collineation fp_5885 fl_5885.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5885 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5885 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5885.

Lemma collineation_5886 : is_collineation fp_5886 fl_5886.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5886 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5886 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5886.

Lemma collineation_5887 : is_collineation fp_5887 fl_5887.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5887 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5887 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5887.

Lemma collineation_5888 : is_collineation fp_5888 fl_5888.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5888 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5888 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5888.

Lemma collineation_5889 : is_collineation fp_5889 fl_5889.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5889 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5889 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5889.

Lemma collineation_5890 : is_collineation fp_5890 fl_5890.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5890 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5890 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5890.

Lemma collineation_5891 : is_collineation fp_5891 fl_5891.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5891 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5891 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5891.

Lemma collineation_5892 : is_collineation fp_5892 fl_5892.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5892 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5892 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5892.

Lemma collineation_5893 : is_collineation fp_5893 fl_5893.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5893 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5893 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5893.

Lemma collineation_5894 : is_collineation fp_5894 fl_5894.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5894 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5894 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5894.

Lemma collineation_5895 : is_collineation fp_5895 fl_5895.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5895 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5895 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5895.

Lemma collineation_5896 : is_collineation fp_5896 fl_5896.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5896 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5896 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5896.

Lemma collineation_5897 : is_collineation fp_5897 fl_5897.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5897 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5897 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5897.

Lemma collineation_5898 : is_collineation fp_5898 fl_5898.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5898 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5898 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5898.

Lemma collineation_5899 : is_collineation fp_5899 fl_5899.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5899 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5899 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5899.

Lemma collineation_5900 : is_collineation fp_5900 fl_5900.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5900 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5900 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5900.

Lemma collineation_5901 : is_collineation fp_5901 fl_5901.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5901 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5901 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5901.

Lemma collineation_5902 : is_collineation fp_5902 fl_5902.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5902 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5902 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5902.

Lemma collineation_5903 : is_collineation fp_5903 fl_5903.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5903 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5903 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5903.

Lemma collineation_5904 : is_collineation fp_5904 fl_5904.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5904 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5904 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5904.

Lemma collineation_5905 : is_collineation fp_5905 fl_5905.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5905 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5905 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5905.

Lemma collineation_5906 : is_collineation fp_5906 fl_5906.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5906 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5906 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5906.

Lemma collineation_5907 : is_collineation fp_5907 fl_5907.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5907 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5907 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5907.

Lemma collineation_5908 : is_collineation fp_5908 fl_5908.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5908 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5908 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5908.

Lemma collineation_5909 : is_collineation fp_5909 fl_5909.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5909 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5909 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5909.

Lemma collineation_5910 : is_collineation fp_5910 fl_5910.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5910 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5910 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5910.

Lemma collineation_5911 : is_collineation fp_5911 fl_5911.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5911 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5911 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5911.

Lemma collineation_5912 : is_collineation fp_5912 fl_5912.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5912 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5912 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5912.

Lemma collineation_5913 : is_collineation fp_5913 fl_5913.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5913 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5913 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5913.

Lemma collineation_5914 : is_collineation fp_5914 fl_5914.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5914 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5914 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5914.

Lemma collineation_5915 : is_collineation fp_5915 fl_5915.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5915 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5915 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5915.

Lemma collineation_5916 : is_collineation fp_5916 fl_5916.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5916 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5916 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5916.

Lemma collineation_5917 : is_collineation fp_5917 fl_5917.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5917 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5917 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5917.

Lemma collineation_5918 : is_collineation fp_5918 fl_5918.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5918 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5918 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5918.

Lemma collineation_5919 : is_collineation fp_5919 fl_5919.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5919 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5919 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5919.

Lemma collineation_5920 : is_collineation fp_5920 fl_5920.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5920 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5920 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5920.

Lemma collineation_5921 : is_collineation fp_5921 fl_5921.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5921 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5921 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5921.

Lemma collineation_5922 : is_collineation fp_5922 fl_5922.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5922 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5922 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5922.

Lemma collineation_5923 : is_collineation fp_5923 fl_5923.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5923 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5923 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5923.

Lemma collineation_5924 : is_collineation fp_5924 fl_5924.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5924 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5924 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5924.

Lemma collineation_5925 : is_collineation fp_5925 fl_5925.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5925 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5925 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5925.

Lemma collineation_5926 : is_collineation fp_5926 fl_5926.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5926 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5926 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5926.

Lemma collineation_5927 : is_collineation fp_5927 fl_5927.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5927 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5927 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5927.

Lemma collineation_5928 : is_collineation fp_5928 fl_5928.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5928 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5928 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5928.

Lemma collineation_5929 : is_collineation fp_5929 fl_5929.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5929 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5929 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5929.

Lemma collineation_5930 : is_collineation fp_5930 fl_5930.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5930 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5930 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5930.

Lemma collineation_5931 : is_collineation fp_5931 fl_5931.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5931 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5931 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5931.

Lemma collineation_5932 : is_collineation fp_5932 fl_5932.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5932 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5932 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5932.

Lemma collineation_5933 : is_collineation fp_5933 fl_5933.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5933 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5933 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5933.

Lemma collineation_5934 : is_collineation fp_5934 fl_5934.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5934 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5934 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5934.

Lemma collineation_5935 : is_collineation fp_5935 fl_5935.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5935 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5935 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5935.

Lemma collineation_5936 : is_collineation fp_5936 fl_5936.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5936 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5936 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5936.

Lemma collineation_5937 : is_collineation fp_5937 fl_5937.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5937 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5937 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5937.

Lemma collineation_5938 : is_collineation fp_5938 fl_5938.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5938 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5938 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5938.

Lemma collineation_5939 : is_collineation fp_5939 fl_5939.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5939 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5939 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5939.

Lemma collineation_5940 : is_collineation fp_5940 fl_5940.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5940 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5940 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5940.

Lemma collineation_5941 : is_collineation fp_5941 fl_5941.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5941 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5941 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5941.

Lemma collineation_5942 : is_collineation fp_5942 fl_5942.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5942 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5942 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5942.

Lemma collineation_5943 : is_collineation fp_5943 fl_5943.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5943 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5943 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5943.

Lemma collineation_5944 : is_collineation fp_5944 fl_5944.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5944 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5944 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5944.

Lemma collineation_5945 : is_collineation fp_5945 fl_5945.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5945 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5945 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5945.

Lemma collineation_5946 : is_collineation fp_5946 fl_5946.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5946 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5946 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5946.

Lemma collineation_5947 : is_collineation fp_5947 fl_5947.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5947 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5947 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5947.

Lemma collineation_5948 : is_collineation fp_5948 fl_5948.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5948 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5948 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5948.

Lemma collineation_5949 : is_collineation fp_5949 fl_5949.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5949 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5949 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5949.

Lemma collineation_5950 : is_collineation fp_5950 fl_5950.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5950 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5950 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5950.

Lemma collineation_5951 : is_collineation fp_5951 fl_5951.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5951 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5951 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5951.

Lemma collineation_5952 : is_collineation fp_5952 fl_5952.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5952 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5952 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5952.

Lemma collineation_5953 : is_collineation fp_5953 fl_5953.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5953 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5953 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5953.

Lemma collineation_5954 : is_collineation fp_5954 fl_5954.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5954 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5954 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5954.

Lemma collineation_5955 : is_collineation fp_5955 fl_5955.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5955 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5955 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5955.

Lemma collineation_5956 : is_collineation fp_5956 fl_5956.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5956 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5956 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5956.

Lemma collineation_5957 : is_collineation fp_5957 fl_5957.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5957 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5957 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5957.

Lemma collineation_5958 : is_collineation fp_5958 fl_5958.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5958 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5958 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5958.

Lemma collineation_5959 : is_collineation fp_5959 fl_5959.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5959 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5959 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5959.

Lemma collineation_5960 : is_collineation fp_5960 fl_5960.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5960 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5960 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5960.

Lemma collineation_5961 : is_collineation fp_5961 fl_5961.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5961 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5961 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5961.

Lemma collineation_5962 : is_collineation fp_5962 fl_5962.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5962 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5962 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5962.

Lemma collineation_5963 : is_collineation fp_5963 fl_5963.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5963 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5963 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5963.

Lemma collineation_5964 : is_collineation fp_5964 fl_5964.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5964 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5964 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5964.

Lemma collineation_5965 : is_collineation fp_5965 fl_5965.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5965 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5965 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5965.

Lemma collineation_5966 : is_collineation fp_5966 fl_5966.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5966 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5966 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5966.

Lemma collineation_5967 : is_collineation fp_5967 fl_5967.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5967 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5967 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5967.

Lemma collineation_5968 : is_collineation fp_5968 fl_5968.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5968 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5968 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5968.

Lemma collineation_5969 : is_collineation fp_5969 fl_5969.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5969 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5969 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5969.

Lemma collineation_5970 : is_collineation fp_5970 fl_5970.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5970 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5970 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5970.

Lemma collineation_5971 : is_collineation fp_5971 fl_5971.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5971 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5971 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5971.

Lemma collineation_5972 : is_collineation fp_5972 fl_5972.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5972 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5972 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5972.

Lemma collineation_5973 : is_collineation fp_5973 fl_5973.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5973 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5973 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5973.

Lemma collineation_5974 : is_collineation fp_5974 fl_5974.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5974 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5974 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5974.

Lemma collineation_5975 : is_collineation fp_5975 fl_5975.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5975 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5975 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5975.

Lemma collineation_5976 : is_collineation fp_5976 fl_5976.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5976 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5976 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5976.

Lemma collineation_5977 : is_collineation fp_5977 fl_5977.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5977 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5977 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5977.

Lemma collineation_5978 : is_collineation fp_5978 fl_5978.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5978 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5978 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5978.

Lemma collineation_5979 : is_collineation fp_5979 fl_5979.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5979 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5979 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5979.

Lemma collineation_5980 : is_collineation fp_5980 fl_5980.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5980 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5980 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5980.

Lemma collineation_5981 : is_collineation fp_5981 fl_5981.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5981 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5981 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5981.

Lemma collineation_5982 : is_collineation fp_5982 fl_5982.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5982 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5982 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5982.

Lemma collineation_5983 : is_collineation fp_5983 fl_5983.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5983 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5983 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5983.

Lemma collineation_5984 : is_collineation fp_5984 fl_5984.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5984 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5984 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5984.

Lemma collineation_5985 : is_collineation fp_5985 fl_5985.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5985 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5985 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5985.

Lemma collineation_5986 : is_collineation fp_5986 fl_5986.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5986 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5986 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5986.

Lemma collineation_5987 : is_collineation fp_5987 fl_5987.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5987 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5987 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5987.

Lemma collineation_5988 : is_collineation fp_5988 fl_5988.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5988 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5988 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5988.

Lemma collineation_5989 : is_collineation fp_5989 fl_5989.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5989 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5989 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5989.

Lemma collineation_5990 : is_collineation fp_5990 fl_5990.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5990 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5990 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5990.

Lemma collineation_5991 : is_collineation fp_5991 fl_5991.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5991 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5991 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5991.

Lemma collineation_5992 : is_collineation fp_5992 fl_5992.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5992 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5992 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5992.

Lemma collineation_5993 : is_collineation fp_5993 fl_5993.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5993 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5993 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5993.

Lemma collineation_5994 : is_collineation fp_5994 fl_5994.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5994 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5994 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5994.

Lemma collineation_5995 : is_collineation fp_5995 fl_5995.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5995 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5995 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5995.

Lemma collineation_5996 : is_collineation fp_5996 fl_5996.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5996 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5996 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5996.

Lemma collineation_5997 : is_collineation fp_5997 fl_5997.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5997 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5997 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5997.

Lemma collineation_5998 : is_collineation fp_5998 fl_5998.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5998 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5998 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5998.

Lemma collineation_5999 : is_collineation fp_5999 fl_5999.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_5999 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_5999 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_5999.

Lemma collineation_6000 : is_collineation fp_6000 fl_6000.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6000 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6000 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6000.

Lemma collineation_6001 : is_collineation fp_6001 fl_6001.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6001 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6001 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6001.

Lemma collineation_6002 : is_collineation fp_6002 fl_6002.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6002 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6002 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6002.

Lemma collineation_6003 : is_collineation fp_6003 fl_6003.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6003 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6003 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6003.

Lemma collineation_6004 : is_collineation fp_6004 fl_6004.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6004 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6004 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6004.

Lemma collineation_6005 : is_collineation fp_6005 fl_6005.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6005 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6005 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6005.

Lemma collineation_6006 : is_collineation fp_6006 fl_6006.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6006 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6006 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6006.

Lemma collineation_6007 : is_collineation fp_6007 fl_6007.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6007 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6007 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6007.

Lemma collineation_6008 : is_collineation fp_6008 fl_6008.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6008 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6008 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6008.

Lemma collineation_6009 : is_collineation fp_6009 fl_6009.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6009 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6009 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6009.

Lemma collineation_6010 : is_collineation fp_6010 fl_6010.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6010 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6010 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6010.

Lemma collineation_6011 : is_collineation fp_6011 fl_6011.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6011 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6011 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6011.

Lemma collineation_6012 : is_collineation fp_6012 fl_6012.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6012 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6012 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6012.

Lemma collineation_6013 : is_collineation fp_6013 fl_6013.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6013 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6013 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6013.

Lemma collineation_6014 : is_collineation fp_6014 fl_6014.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6014 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6014 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6014.

Lemma collineation_6015 : is_collineation fp_6015 fl_6015.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6015 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6015 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6015.

Lemma collineation_6016 : is_collineation fp_6016 fl_6016.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6016 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6016 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6016.

Lemma collineation_6017 : is_collineation fp_6017 fl_6017.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6017 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6017 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6017.

Lemma collineation_6018 : is_collineation fp_6018 fl_6018.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6018 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6018 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6018.

Lemma collineation_6019 : is_collineation fp_6019 fl_6019.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6019 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6019 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6019.

Lemma collineation_6020 : is_collineation fp_6020 fl_6020.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6020 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6020 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6020.

Lemma collineation_6021 : is_collineation fp_6021 fl_6021.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6021 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6021 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6021.

Lemma collineation_6022 : is_collineation fp_6022 fl_6022.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6022 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6022 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6022.

Lemma collineation_6023 : is_collineation fp_6023 fl_6023.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6023 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6023 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6023.

Lemma collineation_6024 : is_collineation fp_6024 fl_6024.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6024 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6024 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6024.

Lemma collineation_6025 : is_collineation fp_6025 fl_6025.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6025 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6025 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6025.

Lemma collineation_6026 : is_collineation fp_6026 fl_6026.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6026 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6026 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6026.

Lemma collineation_6027 : is_collineation fp_6027 fl_6027.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6027 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6027 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6027.

Lemma collineation_6028 : is_collineation fp_6028 fl_6028.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6028 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6028 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6028.

Lemma collineation_6029 : is_collineation fp_6029 fl_6029.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6029 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6029 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6029.

Lemma collineation_6030 : is_collineation fp_6030 fl_6030.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6030 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6030 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6030.

Lemma collineation_6031 : is_collineation fp_6031 fl_6031.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6031 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6031 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6031.

Lemma collineation_6032 : is_collineation fp_6032 fl_6032.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6032 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6032 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6032.

Lemma collineation_6033 : is_collineation fp_6033 fl_6033.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6033 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6033 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6033.

Lemma collineation_6034 : is_collineation fp_6034 fl_6034.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6034 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6034 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6034.

Lemma collineation_6035 : is_collineation fp_6035 fl_6035.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6035 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6035 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6035.

Lemma collineation_6036 : is_collineation fp_6036 fl_6036.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6036 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6036 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6036.

Lemma collineation_6037 : is_collineation fp_6037 fl_6037.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6037 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6037 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6037.

Lemma collineation_6038 : is_collineation fp_6038 fl_6038.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6038 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6038 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6038.

Lemma collineation_6039 : is_collineation fp_6039 fl_6039.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6039 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6039 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6039.

Lemma collineation_6040 : is_collineation fp_6040 fl_6040.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6040 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6040 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6040.

Lemma collineation_6041 : is_collineation fp_6041 fl_6041.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6041 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6041 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6041.

Lemma collineation_6042 : is_collineation fp_6042 fl_6042.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6042 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6042 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6042.

Lemma collineation_6043 : is_collineation fp_6043 fl_6043.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6043 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6043 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6043.

Lemma collineation_6044 : is_collineation fp_6044 fl_6044.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6044 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6044 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6044.

Lemma collineation_6045 : is_collineation fp_6045 fl_6045.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6045 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6045 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6045.

Lemma collineation_6046 : is_collineation fp_6046 fl_6046.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6046 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6046 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6046.

Lemma collineation_6047 : is_collineation fp_6047 fl_6047.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6047 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6047 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6047.

Lemma collineation_6048 : is_collineation fp_6048 fl_6048.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6048 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6048 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6048.

Lemma collineation_6049 : is_collineation fp_6049 fl_6049.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6049 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6049 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6049.

Lemma collineation_6050 : is_collineation fp_6050 fl_6050.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6050 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6050 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6050.

Lemma collineation_6051 : is_collineation fp_6051 fl_6051.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6051 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6051 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6051.

Lemma collineation_6052 : is_collineation fp_6052 fl_6052.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6052 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6052 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6052.

Lemma collineation_6053 : is_collineation fp_6053 fl_6053.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6053 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6053 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6053.

Lemma collineation_6054 : is_collineation fp_6054 fl_6054.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6054 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6054 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6054.

Lemma collineation_6055 : is_collineation fp_6055 fl_6055.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6055 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6055 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6055.

Lemma collineation_6056 : is_collineation fp_6056 fl_6056.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6056 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6056 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6056.

Lemma collineation_6057 : is_collineation fp_6057 fl_6057.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6057 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6057 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6057.

Lemma collineation_6058 : is_collineation fp_6058 fl_6058.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6058 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6058 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6058.

Lemma collineation_6059 : is_collineation fp_6059 fl_6059.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6059 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6059 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6059.

Lemma collineation_6060 : is_collineation fp_6060 fl_6060.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6060 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6060 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6060.

Lemma collineation_6061 : is_collineation fp_6061 fl_6061.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6061 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6061 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6061.

Lemma collineation_6062 : is_collineation fp_6062 fl_6062.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6062 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6062 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6062.

Lemma collineation_6063 : is_collineation fp_6063 fl_6063.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6063 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6063 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6063.

Lemma collineation_6064 : is_collineation fp_6064 fl_6064.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6064 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6064 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6064.

Lemma collineation_6065 : is_collineation fp_6065 fl_6065.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6065 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6065 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6065.

Lemma collineation_6066 : is_collineation fp_6066 fl_6066.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6066 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6066 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6066.

Lemma collineation_6067 : is_collineation fp_6067 fl_6067.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6067 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6067 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6067.

Lemma collineation_6068 : is_collineation fp_6068 fl_6068.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6068 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6068 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6068.

Lemma collineation_6069 : is_collineation fp_6069 fl_6069.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6069 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6069 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6069.

Lemma collineation_6070 : is_collineation fp_6070 fl_6070.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6070 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6070 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6070.

Lemma collineation_6071 : is_collineation fp_6071 fl_6071.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6071 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6071 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6071.

Lemma collineation_6072 : is_collineation fp_6072 fl_6072.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6072 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6072 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6072.

Lemma collineation_6073 : is_collineation fp_6073 fl_6073.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6073 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6073 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6073.

Lemma collineation_6074 : is_collineation fp_6074 fl_6074.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6074 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6074 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6074.

Lemma collineation_6075 : is_collineation fp_6075 fl_6075.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6075 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6075 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6075.

Lemma collineation_6076 : is_collineation fp_6076 fl_6076.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6076 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6076 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6076.

Lemma collineation_6077 : is_collineation fp_6077 fl_6077.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6077 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6077 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6077.

Lemma collineation_6078 : is_collineation fp_6078 fl_6078.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6078 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6078 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6078.

Lemma collineation_6079 : is_collineation fp_6079 fl_6079.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6079 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6079 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6079.

Lemma collineation_6080 : is_collineation fp_6080 fl_6080.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6080 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6080 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6080.

Lemma collineation_6081 : is_collineation fp_6081 fl_6081.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6081 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6081 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6081.

Lemma collineation_6082 : is_collineation fp_6082 fl_6082.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6082 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6082 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6082.

Lemma collineation_6083 : is_collineation fp_6083 fl_6083.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6083 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6083 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6083.

Lemma collineation_6084 : is_collineation fp_6084 fl_6084.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6084 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6084 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6084.

Lemma collineation_6085 : is_collineation fp_6085 fl_6085.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6085 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6085 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6085.

Lemma collineation_6086 : is_collineation fp_6086 fl_6086.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6086 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6086 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6086.

Lemma collineation_6087 : is_collineation fp_6087 fl_6087.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6087 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6087 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6087.

Lemma collineation_6088 : is_collineation fp_6088 fl_6088.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6088 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6088 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6088.

Lemma collineation_6089 : is_collineation fp_6089 fl_6089.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6089 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6089 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6089.

Lemma collineation_6090 : is_collineation fp_6090 fl_6090.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6090 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6090 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6090.

Lemma collineation_6091 : is_collineation fp_6091 fl_6091.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6091 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6091 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6091.

Lemma collineation_6092 : is_collineation fp_6092 fl_6092.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6092 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6092 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6092.

Lemma collineation_6093 : is_collineation fp_6093 fl_6093.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6093 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6093 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6093.

Lemma collineation_6094 : is_collineation fp_6094 fl_6094.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6094 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6094 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6094.

Lemma collineation_6095 : is_collineation fp_6095 fl_6095.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6095 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6095 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6095.

Lemma collineation_6096 : is_collineation fp_6096 fl_6096.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6096 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6096 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6096.

Lemma collineation_6097 : is_collineation fp_6097 fl_6097.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6097 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6097 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6097.

Lemma collineation_6098 : is_collineation fp_6098 fl_6098.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6098 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6098 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6098.

Lemma collineation_6099 : is_collineation fp_6099 fl_6099.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6099 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6099 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6099.

Lemma collineation_6100 : is_collineation fp_6100 fl_6100.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6100 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6100 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6100.

Lemma collineation_6101 : is_collineation fp_6101 fl_6101.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6101 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6101 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6101.

Lemma collineation_6102 : is_collineation fp_6102 fl_6102.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6102 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6102 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6102.

Lemma collineation_6103 : is_collineation fp_6103 fl_6103.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6103 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6103 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6103.

Lemma collineation_6104 : is_collineation fp_6104 fl_6104.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6104 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6104 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6104.

Lemma collineation_6105 : is_collineation fp_6105 fl_6105.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6105 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6105 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6105.

Lemma collineation_6106 : is_collineation fp_6106 fl_6106.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6106 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6106 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6106.

Lemma collineation_6107 : is_collineation fp_6107 fl_6107.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6107 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6107 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6107.

Lemma collineation_6108 : is_collineation fp_6108 fl_6108.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6108 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6108 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6108.

Lemma collineation_6109 : is_collineation fp_6109 fl_6109.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6109 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6109 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6109.

Lemma collineation_6110 : is_collineation fp_6110 fl_6110.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6110 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6110 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6110.

Lemma collineation_6111 : is_collineation fp_6111 fl_6111.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6111 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6111 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6111.

Lemma collineation_6112 : is_collineation fp_6112 fl_6112.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6112 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6112 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6112.

Lemma collineation_6113 : is_collineation fp_6113 fl_6113.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6113 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6113 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6113.

Lemma collineation_6114 : is_collineation fp_6114 fl_6114.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6114 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6114 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6114.

Lemma collineation_6115 : is_collineation fp_6115 fl_6115.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6115 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6115 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6115.

Lemma collineation_6116 : is_collineation fp_6116 fl_6116.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6116 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6116 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6116.

Lemma collineation_6117 : is_collineation fp_6117 fl_6117.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6117 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6117 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6117.

Lemma collineation_6118 : is_collineation fp_6118 fl_6118.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6118 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6118 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6118.

Lemma collineation_6119 : is_collineation fp_6119 fl_6119.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6119 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6119 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6119.

Lemma collineation_6120 : is_collineation fp_6120 fl_6120.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6120 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6120 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6120.

Lemma collineation_6121 : is_collineation fp_6121 fl_6121.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6121 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6121 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6121.

Lemma collineation_6122 : is_collineation fp_6122 fl_6122.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6122 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6122 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6122.

Lemma collineation_6123 : is_collineation fp_6123 fl_6123.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6123 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6123 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6123.

Lemma collineation_6124 : is_collineation fp_6124 fl_6124.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6124 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6124 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6124.

Lemma collineation_6125 : is_collineation fp_6125 fl_6125.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6125 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6125 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6125.

Lemma collineation_6126 : is_collineation fp_6126 fl_6126.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6126 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6126 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6126.

Lemma collineation_6127 : is_collineation fp_6127 fl_6127.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6127 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6127 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6127.

Lemma collineation_6128 : is_collineation fp_6128 fl_6128.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6128 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6128 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6128.

Lemma collineation_6129 : is_collineation fp_6129 fl_6129.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6129 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6129 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6129.

Lemma collineation_6130 : is_collineation fp_6130 fl_6130.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6130 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6130 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6130.

Lemma collineation_6131 : is_collineation fp_6131 fl_6131.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6131 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6131 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6131.

Lemma collineation_6132 : is_collineation fp_6132 fl_6132.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6132 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6132 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6132.

Lemma collineation_6133 : is_collineation fp_6133 fl_6133.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6133 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6133 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6133.

Lemma collineation_6134 : is_collineation fp_6134 fl_6134.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6134 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6134 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6134.

Lemma collineation_6135 : is_collineation fp_6135 fl_6135.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6135 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6135 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6135.

Lemma collineation_6136 : is_collineation fp_6136 fl_6136.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6136 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6136 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6136.

Lemma collineation_6137 : is_collineation fp_6137 fl_6137.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6137 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6137 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6137.

Lemma collineation_6138 : is_collineation fp_6138 fl_6138.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6138 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6138 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6138.

Lemma collineation_6139 : is_collineation fp_6139 fl_6139.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6139 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6139 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6139.

Lemma collineation_6140 : is_collineation fp_6140 fl_6140.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6140 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6140 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6140.

Lemma collineation_6141 : is_collineation fp_6141 fl_6141.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6141 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6141 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6141.

Lemma collineation_6142 : is_collineation fp_6142 fl_6142.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6142 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6142 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6142.

Lemma collineation_6143 : is_collineation fp_6143 fl_6143.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6143 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6143 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6143.

Lemma collineation_6144 : is_collineation fp_6144 fl_6144.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6144 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6144 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6144.

Lemma collineation_6145 : is_collineation fp_6145 fl_6145.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6145 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6145 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6145.

Lemma collineation_6146 : is_collineation fp_6146 fl_6146.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6146 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6146 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6146.

Lemma collineation_6147 : is_collineation fp_6147 fl_6147.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6147 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6147 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6147.

Lemma collineation_6148 : is_collineation fp_6148 fl_6148.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6148 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6148 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6148.

Lemma collineation_6149 : is_collineation fp_6149 fl_6149.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6149 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6149 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6149.

Lemma collineation_6150 : is_collineation fp_6150 fl_6150.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6150 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6150 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6150.

Lemma collineation_6151 : is_collineation fp_6151 fl_6151.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6151 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6151 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6151.

Lemma collineation_6152 : is_collineation fp_6152 fl_6152.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6152 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6152 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6152.

Lemma collineation_6153 : is_collineation fp_6153 fl_6153.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6153 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6153 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6153.

Lemma collineation_6154 : is_collineation fp_6154 fl_6154.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6154 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6154 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6154.

Lemma collineation_6155 : is_collineation fp_6155 fl_6155.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6155 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6155 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6155.

Lemma collineation_6156 : is_collineation fp_6156 fl_6156.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6156 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6156 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6156.

Lemma collineation_6157 : is_collineation fp_6157 fl_6157.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6157 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6157 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6157.

Lemma collineation_6158 : is_collineation fp_6158 fl_6158.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6158 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6158 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6158.

Lemma collineation_6159 : is_collineation fp_6159 fl_6159.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6159 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6159 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6159.

Lemma collineation_6160 : is_collineation fp_6160 fl_6160.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6160 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6160 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6160.

Lemma collineation_6161 : is_collineation fp_6161 fl_6161.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6161 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6161 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6161.

Lemma collineation_6162 : is_collineation fp_6162 fl_6162.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6162 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6162 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6162.

Lemma collineation_6163 : is_collineation fp_6163 fl_6163.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6163 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6163 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6163.

Lemma collineation_6164 : is_collineation fp_6164 fl_6164.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6164 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6164 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6164.

Lemma collineation_6165 : is_collineation fp_6165 fl_6165.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6165 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6165 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6165.

Lemma collineation_6166 : is_collineation fp_6166 fl_6166.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6166 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6166 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6166.

Lemma collineation_6167 : is_collineation fp_6167 fl_6167.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6167 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6167 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6167.

Lemma collineation_6168 : is_collineation fp_6168 fl_6168.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6168 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6168 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6168.

Lemma collineation_6169 : is_collineation fp_6169 fl_6169.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6169 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6169 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6169.

Lemma collineation_6170 : is_collineation fp_6170 fl_6170.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6170 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6170 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6170.

Lemma collineation_6171 : is_collineation fp_6171 fl_6171.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6171 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6171 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6171.

Lemma collineation_6172 : is_collineation fp_6172 fl_6172.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6172 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6172 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6172.

Lemma collineation_6173 : is_collineation fp_6173 fl_6173.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6173 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6173 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6173.

Lemma collineation_6174 : is_collineation fp_6174 fl_6174.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6174 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6174 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6174.

Lemma collineation_6175 : is_collineation fp_6175 fl_6175.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6175 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6175 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6175.

Lemma collineation_6176 : is_collineation fp_6176 fl_6176.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6176 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6176 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6176.

Lemma collineation_6177 : is_collineation fp_6177 fl_6177.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6177 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6177 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6177.

Lemma collineation_6178 : is_collineation fp_6178 fl_6178.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6178 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6178 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6178.

Lemma collineation_6179 : is_collineation fp_6179 fl_6179.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6179 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6179 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6179.

Lemma collineation_6180 : is_collineation fp_6180 fl_6180.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6180 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6180 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6180.

Lemma collineation_6181 : is_collineation fp_6181 fl_6181.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6181 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6181 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6181.

Lemma collineation_6182 : is_collineation fp_6182 fl_6182.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6182 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6182 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6182.

Lemma collineation_6183 : is_collineation fp_6183 fl_6183.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6183 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6183 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6183.

Lemma collineation_6184 : is_collineation fp_6184 fl_6184.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6184 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6184 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6184.

Lemma collineation_6185 : is_collineation fp_6185 fl_6185.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6185 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6185 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6185.

Lemma collineation_6186 : is_collineation fp_6186 fl_6186.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6186 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6186 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6186.

Lemma collineation_6187 : is_collineation fp_6187 fl_6187.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6187 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6187 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6187.

Lemma collineation_6188 : is_collineation fp_6188 fl_6188.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6188 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6188 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6188.

Lemma collineation_6189 : is_collineation fp_6189 fl_6189.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6189 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6189 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6189.

Lemma collineation_6190 : is_collineation fp_6190 fl_6190.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6190 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6190 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6190.

Lemma collineation_6191 : is_collineation fp_6191 fl_6191.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6191 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6191 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6191.

Lemma collineation_6192 : is_collineation fp_6192 fl_6192.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6192 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6192 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6192.

Lemma collineation_6193 : is_collineation fp_6193 fl_6193.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6193 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6193 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6193.

Lemma collineation_6194 : is_collineation fp_6194 fl_6194.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6194 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6194 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6194.

Lemma collineation_6195 : is_collineation fp_6195 fl_6195.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6195 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6195 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6195.

Lemma collineation_6196 : is_collineation fp_6196 fl_6196.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6196 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6196 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6196.

Lemma collineation_6197 : is_collineation fp_6197 fl_6197.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6197 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6197 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6197.

Lemma collineation_6198 : is_collineation fp_6198 fl_6198.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6198 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6198 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6198.

Lemma collineation_6199 : is_collineation fp_6199 fl_6199.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6199 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6199 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6199.

Lemma collineation_6200 : is_collineation fp_6200 fl_6200.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6200 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6200 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6200.

Lemma collineation_6201 : is_collineation fp_6201 fl_6201.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6201 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6201 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6201.

Lemma collineation_6202 : is_collineation fp_6202 fl_6202.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6202 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6202 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6202.

Lemma collineation_6203 : is_collineation fp_6203 fl_6203.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6203 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6203 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6203.

Lemma collineation_6204 : is_collineation fp_6204 fl_6204.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6204 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6204 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6204.

Lemma collineation_6205 : is_collineation fp_6205 fl_6205.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6205 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6205 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6205.

Lemma collineation_6206 : is_collineation fp_6206 fl_6206.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6206 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6206 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6206.

Lemma collineation_6207 : is_collineation fp_6207 fl_6207.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6207 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6207 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6207.

Lemma collineation_6208 : is_collineation fp_6208 fl_6208.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6208 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6208 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6208.

Lemma collineation_6209 : is_collineation fp_6209 fl_6209.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6209 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6209 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6209.

Lemma collineation_6210 : is_collineation fp_6210 fl_6210.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6210 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6210 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6210.

Lemma collineation_6211 : is_collineation fp_6211 fl_6211.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6211 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6211 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6211.

Lemma collineation_6212 : is_collineation fp_6212 fl_6212.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6212 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6212 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6212.

Lemma collineation_6213 : is_collineation fp_6213 fl_6213.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6213 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6213 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6213.

Lemma collineation_6214 : is_collineation fp_6214 fl_6214.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6214 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6214 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6214.

Lemma collineation_6215 : is_collineation fp_6215 fl_6215.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6215 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6215 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6215.

Lemma collineation_6216 : is_collineation fp_6216 fl_6216.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6216 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6216 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6216.

Lemma collineation_6217 : is_collineation fp_6217 fl_6217.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6217 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6217 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6217.

Lemma collineation_6218 : is_collineation fp_6218 fl_6218.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6218 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6218 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6218.

Lemma collineation_6219 : is_collineation fp_6219 fl_6219.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6219 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6219 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6219.

Lemma collineation_6220 : is_collineation fp_6220 fl_6220.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6220 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6220 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6220.

Lemma collineation_6221 : is_collineation fp_6221 fl_6221.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6221 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6221 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6221.

Lemma collineation_6222 : is_collineation fp_6222 fl_6222.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6222 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6222 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6222.

Lemma collineation_6223 : is_collineation fp_6223 fl_6223.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6223 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6223 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6223.

Lemma collineation_6224 : is_collineation fp_6224 fl_6224.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6224 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6224 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6224.

Lemma collineation_6225 : is_collineation fp_6225 fl_6225.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6225 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6225 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6225.

Lemma collineation_6226 : is_collineation fp_6226 fl_6226.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6226 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6226 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6226.

Lemma collineation_6227 : is_collineation fp_6227 fl_6227.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6227 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6227 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6227.

Lemma collineation_6228 : is_collineation fp_6228 fl_6228.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6228 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6228 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6228.

Lemma collineation_6229 : is_collineation fp_6229 fl_6229.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6229 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6229 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6229.

Lemma collineation_6230 : is_collineation fp_6230 fl_6230.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6230 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6230 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6230.

Lemma collineation_6231 : is_collineation fp_6231 fl_6231.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6231 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6231 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6231.

Lemma collineation_6232 : is_collineation fp_6232 fl_6232.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6232 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6232 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6232.

Lemma collineation_6233 : is_collineation fp_6233 fl_6233.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6233 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6233 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6233.

Lemma collineation_6234 : is_collineation fp_6234 fl_6234.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6234 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6234 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6234.

Lemma collineation_6235 : is_collineation fp_6235 fl_6235.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6235 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6235 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6235.

Lemma collineation_6236 : is_collineation fp_6236 fl_6236.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6236 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6236 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6236.

Lemma collineation_6237 : is_collineation fp_6237 fl_6237.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6237 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6237 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6237.

Lemma collineation_6238 : is_collineation fp_6238 fl_6238.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6238 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6238 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6238.

Lemma collineation_6239 : is_collineation fp_6239 fl_6239.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6239 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6239 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6239.

Lemma collineation_6240 : is_collineation fp_6240 fl_6240.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6240 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6240 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6240.

Lemma collineation_6241 : is_collineation fp_6241 fl_6241.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6241 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6241 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6241.

Lemma collineation_6242 : is_collineation fp_6242 fl_6242.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6242 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6242 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6242.

Lemma collineation_6243 : is_collineation fp_6243 fl_6243.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6243 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6243 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6243.

Lemma collineation_6244 : is_collineation fp_6244 fl_6244.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6244 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6244 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6244.

Lemma collineation_6245 : is_collineation fp_6245 fl_6245.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6245 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6245 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6245.

Lemma collineation_6246 : is_collineation fp_6246 fl_6246.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6246 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6246 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6246.

Lemma collineation_6247 : is_collineation fp_6247 fl_6247.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6247 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6247 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6247.

Lemma collineation_6248 : is_collineation fp_6248 fl_6248.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6248 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6248 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6248.

Lemma collineation_6249 : is_collineation fp_6249 fl_6249.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6249 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6249 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6249.

Lemma collineation_6250 : is_collineation fp_6250 fl_6250.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6250 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6250 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6250.

Lemma collineation_6251 : is_collineation fp_6251 fl_6251.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6251 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6251 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6251.

Lemma collineation_6252 : is_collineation fp_6252 fl_6252.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6252 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6252 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6252.

Lemma collineation_6253 : is_collineation fp_6253 fl_6253.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6253 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6253 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6253.

Lemma collineation_6254 : is_collineation fp_6254 fl_6254.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6254 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6254 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6254.

Lemma collineation_6255 : is_collineation fp_6255 fl_6255.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6255 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6255 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6255.

Lemma collineation_6256 : is_collineation fp_6256 fl_6256.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6256 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6256 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6256.

Lemma collineation_6257 : is_collineation fp_6257 fl_6257.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6257 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6257 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6257.

Lemma collineation_6258 : is_collineation fp_6258 fl_6258.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6258 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6258 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6258.

Lemma collineation_6259 : is_collineation fp_6259 fl_6259.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6259 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6259 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6259.

Lemma collineation_6260 : is_collineation fp_6260 fl_6260.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6260 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6260 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6260.

Lemma collineation_6261 : is_collineation fp_6261 fl_6261.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6261 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6261 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6261.

Lemma collineation_6262 : is_collineation fp_6262 fl_6262.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6262 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6262 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6262.

Lemma collineation_6263 : is_collineation fp_6263 fl_6263.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6263 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6263 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6263.

Lemma collineation_6264 : is_collineation fp_6264 fl_6264.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6264 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6264 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6264.

Lemma collineation_6265 : is_collineation fp_6265 fl_6265.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6265 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6265 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6265.

Lemma collineation_6266 : is_collineation fp_6266 fl_6266.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6266 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6266 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6266.

Lemma collineation_6267 : is_collineation fp_6267 fl_6267.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6267 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6267 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6267.

Lemma collineation_6268 : is_collineation fp_6268 fl_6268.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6268 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6268 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6268.

Lemma collineation_6269 : is_collineation fp_6269 fl_6269.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6269 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6269 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6269.

Lemma collineation_6270 : is_collineation fp_6270 fl_6270.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6270 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6270 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6270.

Lemma collineation_6271 : is_collineation fp_6271 fl_6271.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6271 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6271 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6271.

Lemma collineation_6272 : is_collineation fp_6272 fl_6272.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6272 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6272 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6272.

Lemma collineation_6273 : is_collineation fp_6273 fl_6273.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6273 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6273 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6273.

Lemma collineation_6274 : is_collineation fp_6274 fl_6274.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6274 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6274 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6274.

Lemma collineation_6275 : is_collineation fp_6275 fl_6275.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6275 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6275 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6275.

Lemma collineation_6276 : is_collineation fp_6276 fl_6276.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6276 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6276 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6276.

Lemma collineation_6277 : is_collineation fp_6277 fl_6277.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6277 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6277 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6277.

Lemma collineation_6278 : is_collineation fp_6278 fl_6278.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6278 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6278 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6278.

Lemma collineation_6279 : is_collineation fp_6279 fl_6279.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6279 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6279 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6279.

Lemma collineation_6280 : is_collineation fp_6280 fl_6280.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6280 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6280 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6280.

Lemma collineation_6281 : is_collineation fp_6281 fl_6281.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6281 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6281 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6281.

Lemma collineation_6282 : is_collineation fp_6282 fl_6282.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6282 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6282 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6282.

Lemma collineation_6283 : is_collineation fp_6283 fl_6283.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6283 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6283 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6283.

Lemma collineation_6284 : is_collineation fp_6284 fl_6284.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6284 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6284 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6284.

Lemma collineation_6285 : is_collineation fp_6285 fl_6285.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6285 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6285 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6285.

Lemma collineation_6286 : is_collineation fp_6286 fl_6286.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6286 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6286 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6286.

Lemma collineation_6287 : is_collineation fp_6287 fl_6287.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6287 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6287 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6287.

Lemma collineation_6288 : is_collineation fp_6288 fl_6288.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6288 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6288 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6288.

Lemma collineation_6289 : is_collineation fp_6289 fl_6289.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6289 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6289 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6289.

Lemma collineation_6290 : is_collineation fp_6290 fl_6290.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6290 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6290 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6290.

Lemma collineation_6291 : is_collineation fp_6291 fl_6291.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6291 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6291 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6291.

Lemma collineation_6292 : is_collineation fp_6292 fl_6292.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6292 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6292 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6292.

Lemma collineation_6293 : is_collineation fp_6293 fl_6293.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6293 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6293 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6293.

Lemma collineation_6294 : is_collineation fp_6294 fl_6294.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6294 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6294 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6294.

Lemma collineation_6295 : is_collineation fp_6295 fl_6295.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6295 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6295 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6295.

Lemma collineation_6296 : is_collineation fp_6296 fl_6296.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6296 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6296 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6296.

Lemma collineation_6297 : is_collineation fp_6297 fl_6297.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6297 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6297 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6297.

Lemma collineation_6298 : is_collineation fp_6298 fl_6298.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6298 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6298 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6298.

Lemma collineation_6299 : is_collineation fp_6299 fl_6299.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6299 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6299 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6299.

Lemma collineation_6300 : is_collineation fp_6300 fl_6300.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6300 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6300 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6300.

Lemma collineation_6301 : is_collineation fp_6301 fl_6301.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6301 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6301 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6301.

Lemma collineation_6302 : is_collineation fp_6302 fl_6302.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6302 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6302 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6302.

Lemma collineation_6303 : is_collineation fp_6303 fl_6303.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6303 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6303 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6303.

Lemma collineation_6304 : is_collineation fp_6304 fl_6304.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6304 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6304 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6304.

Lemma collineation_6305 : is_collineation fp_6305 fl_6305.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6305 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6305 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6305.

Lemma collineation_6306 : is_collineation fp_6306 fl_6306.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6306 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6306 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6306.

Lemma collineation_6307 : is_collineation fp_6307 fl_6307.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6307 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6307 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6307.

Lemma collineation_6308 : is_collineation fp_6308 fl_6308.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6308 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6308 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6308.

Lemma collineation_6309 : is_collineation fp_6309 fl_6309.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6309 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6309 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6309.

Lemma collineation_6310 : is_collineation fp_6310 fl_6310.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6310 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6310 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6310.

Lemma collineation_6311 : is_collineation fp_6311 fl_6311.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6311 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6311 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6311.

Lemma collineation_6312 : is_collineation fp_6312 fl_6312.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6312 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6312 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6312.

Lemma collineation_6313 : is_collineation fp_6313 fl_6313.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6313 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6313 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6313.

Lemma collineation_6314 : is_collineation fp_6314 fl_6314.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6314 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6314 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6314.

Lemma collineation_6315 : is_collineation fp_6315 fl_6315.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6315 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6315 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6315.

Lemma collineation_6316 : is_collineation fp_6316 fl_6316.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6316 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6316 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6316.

Lemma collineation_6317 : is_collineation fp_6317 fl_6317.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6317 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6317 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6317.

Lemma collineation_6318 : is_collineation fp_6318 fl_6318.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6318 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6318 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6318.

Lemma collineation_6319 : is_collineation fp_6319 fl_6319.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6319 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6319 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6319.

Lemma collineation_6320 : is_collineation fp_6320 fl_6320.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6320 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6320 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6320.

Lemma collineation_6321 : is_collineation fp_6321 fl_6321.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6321 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6321 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6321.

Lemma collineation_6322 : is_collineation fp_6322 fl_6322.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6322 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6322 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6322.

Lemma collineation_6323 : is_collineation fp_6323 fl_6323.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6323 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6323 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6323.

Lemma collineation_6324 : is_collineation fp_6324 fl_6324.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6324 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6324 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6324.

Lemma collineation_6325 : is_collineation fp_6325 fl_6325.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6325 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6325 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6325.

Lemma collineation_6326 : is_collineation fp_6326 fl_6326.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6326 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6326 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6326.

Lemma collineation_6327 : is_collineation fp_6327 fl_6327.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6327 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6327 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6327.

Lemma collineation_6328 : is_collineation fp_6328 fl_6328.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6328 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6328 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6328.

Lemma collineation_6329 : is_collineation fp_6329 fl_6329.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6329 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6329 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6329.

Lemma collineation_6330 : is_collineation fp_6330 fl_6330.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6330 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6330 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6330.

Lemma collineation_6331 : is_collineation fp_6331 fl_6331.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6331 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6331 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6331.

Lemma collineation_6332 : is_collineation fp_6332 fl_6332.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6332 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6332 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6332.

Lemma collineation_6333 : is_collineation fp_6333 fl_6333.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6333 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6333 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6333.

Lemma collineation_6334 : is_collineation fp_6334 fl_6334.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6334 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6334 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6334.

Lemma collineation_6335 : is_collineation fp_6335 fl_6335.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6335 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6335 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6335.

Lemma collineation_6336 : is_collineation fp_6336 fl_6336.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6336 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6336 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6336.

Lemma collineation_6337 : is_collineation fp_6337 fl_6337.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6337 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6337 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6337.

Lemma collineation_6338 : is_collineation fp_6338 fl_6338.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6338 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6338 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6338.

Lemma collineation_6339 : is_collineation fp_6339 fl_6339.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6339 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6339 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6339.

Lemma collineation_6340 : is_collineation fp_6340 fl_6340.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6340 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6340 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6340.

Lemma collineation_6341 : is_collineation fp_6341 fl_6341.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6341 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6341 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6341.

Lemma collineation_6342 : is_collineation fp_6342 fl_6342.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6342 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6342 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6342.

Lemma collineation_6343 : is_collineation fp_6343 fl_6343.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6343 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6343 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6343.

Lemma collineation_6344 : is_collineation fp_6344 fl_6344.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6344 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6344 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6344.

Lemma collineation_6345 : is_collineation fp_6345 fl_6345.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6345 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6345 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6345.

Lemma collineation_6346 : is_collineation fp_6346 fl_6346.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6346 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6346 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6346.

Lemma collineation_6347 : is_collineation fp_6347 fl_6347.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6347 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6347 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6347.

Lemma collineation_6348 : is_collineation fp_6348 fl_6348.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6348 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6348 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6348.

Lemma collineation_6349 : is_collineation fp_6349 fl_6349.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6349 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6349 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6349.

Lemma collineation_6350 : is_collineation fp_6350 fl_6350.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6350 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6350 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6350.

Lemma collineation_6351 : is_collineation fp_6351 fl_6351.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6351 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6351 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6351.

Lemma collineation_6352 : is_collineation fp_6352 fl_6352.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6352 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6352 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6352.

Lemma collineation_6353 : is_collineation fp_6353 fl_6353.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6353 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6353 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6353.

Lemma collineation_6354 : is_collineation fp_6354 fl_6354.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6354 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6354 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6354.

Lemma collineation_6355 : is_collineation fp_6355 fl_6355.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6355 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6355 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6355.

Lemma collineation_6356 : is_collineation fp_6356 fl_6356.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6356 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6356 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6356.

Lemma collineation_6357 : is_collineation fp_6357 fl_6357.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6357 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6357 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6357.

Lemma collineation_6358 : is_collineation fp_6358 fl_6358.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6358 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6358 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6358.

Lemma collineation_6359 : is_collineation fp_6359 fl_6359.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6359 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6359 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6359.

Lemma collineation_6360 : is_collineation fp_6360 fl_6360.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6360 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6360 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6360.

Lemma collineation_6361 : is_collineation fp_6361 fl_6361.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6361 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6361 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6361.

Lemma collineation_6362 : is_collineation fp_6362 fl_6362.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6362 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6362 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6362.

Lemma collineation_6363 : is_collineation fp_6363 fl_6363.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6363 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6363 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6363.

Lemma collineation_6364 : is_collineation fp_6364 fl_6364.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6364 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6364 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6364.

Lemma collineation_6365 : is_collineation fp_6365 fl_6365.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6365 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6365 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6365.

Lemma collineation_6366 : is_collineation fp_6366 fl_6366.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6366 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6366 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6366.

Lemma collineation_6367 : is_collineation fp_6367 fl_6367.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6367 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6367 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6367.

Lemma collineation_6368 : is_collineation fp_6368 fl_6368.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6368 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6368 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6368.

Lemma collineation_6369 : is_collineation fp_6369 fl_6369.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6369 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6369 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6369.

Lemma collineation_6370 : is_collineation fp_6370 fl_6370.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6370 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6370 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6370.

Lemma collineation_6371 : is_collineation fp_6371 fl_6371.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6371 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6371 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6371.

Lemma collineation_6372 : is_collineation fp_6372 fl_6372.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6372 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6372 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6372.

Lemma collineation_6373 : is_collineation fp_6373 fl_6373.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6373 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6373 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6373.

Lemma collineation_6374 : is_collineation fp_6374 fl_6374.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6374 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6374 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6374.

Lemma collineation_6375 : is_collineation fp_6375 fl_6375.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6375 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6375 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6375.

Lemma collineation_6376 : is_collineation fp_6376 fl_6376.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6376 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6376 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6376.

Lemma collineation_6377 : is_collineation fp_6377 fl_6377.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6377 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6377 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6377.

Lemma collineation_6378 : is_collineation fp_6378 fl_6378.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6378 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6378 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6378.

Lemma collineation_6379 : is_collineation fp_6379 fl_6379.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6379 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6379 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6379.

Lemma collineation_6380 : is_collineation fp_6380 fl_6380.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6380 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6380 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6380.

Lemma collineation_6381 : is_collineation fp_6381 fl_6381.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6381 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6381 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6381.

Lemma collineation_6382 : is_collineation fp_6382 fl_6382.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6382 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6382 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6382.

Lemma collineation_6383 : is_collineation fp_6383 fl_6383.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6383 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6383 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6383.

Lemma collineation_6384 : is_collineation fp_6384 fl_6384.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6384 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6384 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6384.

Lemma collineation_6385 : is_collineation fp_6385 fl_6385.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6385 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6385 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6385.

Lemma collineation_6386 : is_collineation fp_6386 fl_6386.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6386 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6386 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6386.

Lemma collineation_6387 : is_collineation fp_6387 fl_6387.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6387 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6387 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6387.

Lemma collineation_6388 : is_collineation fp_6388 fl_6388.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6388 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6388 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6388.

Lemma collineation_6389 : is_collineation fp_6389 fl_6389.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6389 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6389 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6389.

Lemma collineation_6390 : is_collineation fp_6390 fl_6390.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6390 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6390 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6390.

Lemma collineation_6391 : is_collineation fp_6391 fl_6391.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6391 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6391 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6391.

Lemma collineation_6392 : is_collineation fp_6392 fl_6392.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6392 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6392 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6392.

Lemma collineation_6393 : is_collineation fp_6393 fl_6393.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6393 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6393 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6393.

Lemma collineation_6394 : is_collineation fp_6394 fl_6394.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6394 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6394 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6394.

Lemma collineation_6395 : is_collineation fp_6395 fl_6395.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6395 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6395 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6395.

Lemma collineation_6396 : is_collineation fp_6396 fl_6396.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6396 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6396 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6396.

Lemma collineation_6397 : is_collineation fp_6397 fl_6397.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6397 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6397 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6397.

Lemma collineation_6398 : is_collineation fp_6398 fl_6398.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6398 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6398 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6398.

Lemma collineation_6399 : is_collineation fp_6399 fl_6399.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6399 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6399 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6399.

Lemma collineation_6400 : is_collineation fp_6400 fl_6400.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6400 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6400 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6400.

Lemma collineation_6401 : is_collineation fp_6401 fl_6401.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6401 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6401 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6401.

Lemma collineation_6402 : is_collineation fp_6402 fl_6402.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6402 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6402 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6402.

Lemma collineation_6403 : is_collineation fp_6403 fl_6403.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6403 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6403 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6403.

Lemma collineation_6404 : is_collineation fp_6404 fl_6404.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6404 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6404 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6404.

Lemma collineation_6405 : is_collineation fp_6405 fl_6405.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6405 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6405 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6405.

Lemma collineation_6406 : is_collineation fp_6406 fl_6406.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6406 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6406 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6406.

Lemma collineation_6407 : is_collineation fp_6407 fl_6407.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6407 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6407 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6407.

Lemma collineation_6408 : is_collineation fp_6408 fl_6408.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6408 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6408 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6408.

Lemma collineation_6409 : is_collineation fp_6409 fl_6409.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6409 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6409 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6409.

Lemma collineation_6410 : is_collineation fp_6410 fl_6410.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6410 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6410 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6410.

Lemma collineation_6411 : is_collineation fp_6411 fl_6411.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6411 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6411 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6411.

Lemma collineation_6412 : is_collineation fp_6412 fl_6412.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6412 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6412 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6412.

Lemma collineation_6413 : is_collineation fp_6413 fl_6413.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6413 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6413 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6413.

Lemma collineation_6414 : is_collineation fp_6414 fl_6414.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6414 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6414 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6414.

Lemma collineation_6415 : is_collineation fp_6415 fl_6415.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6415 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6415 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6415.

Lemma collineation_6416 : is_collineation fp_6416 fl_6416.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6416 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6416 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6416.

Lemma collineation_6417 : is_collineation fp_6417 fl_6417.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6417 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6417 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6417.

Lemma collineation_6418 : is_collineation fp_6418 fl_6418.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6418 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6418 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6418.

Lemma collineation_6419 : is_collineation fp_6419 fl_6419.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6419 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6419 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6419.

Lemma collineation_6420 : is_collineation fp_6420 fl_6420.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6420 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6420 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6420.

Lemma collineation_6421 : is_collineation fp_6421 fl_6421.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6421 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6421 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6421.

Lemma collineation_6422 : is_collineation fp_6422 fl_6422.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6422 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6422 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6422.

Lemma collineation_6423 : is_collineation fp_6423 fl_6423.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6423 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6423 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6423.

Lemma collineation_6424 : is_collineation fp_6424 fl_6424.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6424 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6424 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6424.

Lemma collineation_6425 : is_collineation fp_6425 fl_6425.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6425 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6425 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6425.

Lemma collineation_6426 : is_collineation fp_6426 fl_6426.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6426 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6426 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6426.

Lemma collineation_6427 : is_collineation fp_6427 fl_6427.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6427 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6427 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6427.

Lemma collineation_6428 : is_collineation fp_6428 fl_6428.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6428 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6428 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6428.

Lemma collineation_6429 : is_collineation fp_6429 fl_6429.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6429 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6429 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6429.

Lemma collineation_6430 : is_collineation fp_6430 fl_6430.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6430 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6430 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6430.

Lemma collineation_6431 : is_collineation fp_6431 fl_6431.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6431 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6431 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6431.

Lemma collineation_6432 : is_collineation fp_6432 fl_6432.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6432 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6432 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6432.

Lemma collineation_6433 : is_collineation fp_6433 fl_6433.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6433 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6433 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6433.

Lemma collineation_6434 : is_collineation fp_6434 fl_6434.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6434 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6434 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6434.

Lemma collineation_6435 : is_collineation fp_6435 fl_6435.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6435 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6435 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6435.

Lemma collineation_6436 : is_collineation fp_6436 fl_6436.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6436 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6436 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6436.

Lemma collineation_6437 : is_collineation fp_6437 fl_6437.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6437 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6437 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6437.

Lemma collineation_6438 : is_collineation fp_6438 fl_6438.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6438 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6438 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6438.

Lemma collineation_6439 : is_collineation fp_6439 fl_6439.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6439 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6439 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6439.

Lemma collineation_6440 : is_collineation fp_6440 fl_6440.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6440 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6440 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6440.

Lemma collineation_6441 : is_collineation fp_6441 fl_6441.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6441 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6441 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6441.

Lemma collineation_6442 : is_collineation fp_6442 fl_6442.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6442 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6442 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6442.

Lemma collineation_6443 : is_collineation fp_6443 fl_6443.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6443 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6443 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6443.

Lemma collineation_6444 : is_collineation fp_6444 fl_6444.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6444 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6444 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6444.

Lemma collineation_6445 : is_collineation fp_6445 fl_6445.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6445 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6445 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6445.

Lemma collineation_6446 : is_collineation fp_6446 fl_6446.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6446 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6446 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6446.

Lemma collineation_6447 : is_collineation fp_6447 fl_6447.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6447 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6447 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6447.

Lemma collineation_6448 : is_collineation fp_6448 fl_6448.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6448 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6448 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6448.

Lemma collineation_6449 : is_collineation fp_6449 fl_6449.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6449 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6449 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6449.

Lemma collineation_6450 : is_collineation fp_6450 fl_6450.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6450 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6450 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6450.

Lemma collineation_6451 : is_collineation fp_6451 fl_6451.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6451 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6451 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6451.

Lemma collineation_6452 : is_collineation fp_6452 fl_6452.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6452 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6452 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6452.

Lemma collineation_6453 : is_collineation fp_6453 fl_6453.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6453 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6453 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6453.

Lemma collineation_6454 : is_collineation fp_6454 fl_6454.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6454 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6454 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6454.

Lemma collineation_6455 : is_collineation fp_6455 fl_6455.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6455 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6455 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6455.

Lemma collineation_6456 : is_collineation fp_6456 fl_6456.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6456 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6456 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6456.

Lemma collineation_6457 : is_collineation fp_6457 fl_6457.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6457 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6457 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6457.

Lemma collineation_6458 : is_collineation fp_6458 fl_6458.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6458 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6458 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6458.

Lemma collineation_6459 : is_collineation fp_6459 fl_6459.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6459 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6459 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6459.

Lemma collineation_6460 : is_collineation fp_6460 fl_6460.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6460 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6460 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6460.

Lemma collineation_6461 : is_collineation fp_6461 fl_6461.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6461 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6461 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6461.

Lemma collineation_6462 : is_collineation fp_6462 fl_6462.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6462 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6462 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6462.

Lemma collineation_6463 : is_collineation fp_6463 fl_6463.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6463 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6463 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6463.

Lemma collineation_6464 : is_collineation fp_6464 fl_6464.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6464 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6464 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6464.

Lemma collineation_6465 : is_collineation fp_6465 fl_6465.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6465 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6465 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6465.

Lemma collineation_6466 : is_collineation fp_6466 fl_6466.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6466 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6466 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6466.

Lemma collineation_6467 : is_collineation fp_6467 fl_6467.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6467 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6467 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6467.

Lemma collineation_6468 : is_collineation fp_6468 fl_6468.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6468 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6468 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6468.

Lemma collineation_6469 : is_collineation fp_6469 fl_6469.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6469 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6469 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6469.

Lemma collineation_6470 : is_collineation fp_6470 fl_6470.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6470 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6470 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6470.

Lemma collineation_6471 : is_collineation fp_6471 fl_6471.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6471 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6471 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6471.

Lemma collineation_6472 : is_collineation fp_6472 fl_6472.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6472 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6472 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6472.

Lemma collineation_6473 : is_collineation fp_6473 fl_6473.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6473 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6473 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6473.

Lemma collineation_6474 : is_collineation fp_6474 fl_6474.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6474 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6474 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6474.

Lemma collineation_6475 : is_collineation fp_6475 fl_6475.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6475 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6475 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6475.

Lemma collineation_6476 : is_collineation fp_6476 fl_6476.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6476 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6476 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6476.

Lemma collineation_6477 : is_collineation fp_6477 fl_6477.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6477 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6477 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6477.

Lemma collineation_6478 : is_collineation fp_6478 fl_6478.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6478 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6478 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6478.

Lemma collineation_6479 : is_collineation fp_6479 fl_6479.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6479 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6479 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6479.

Lemma collineation_6480 : is_collineation fp_6480 fl_6480.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6480 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6480 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6480.

Lemma collineation_6481 : is_collineation fp_6481 fl_6481.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6481 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6481 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6481.

Lemma collineation_6482 : is_collineation fp_6482 fl_6482.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6482 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6482 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6482.

Lemma collineation_6483 : is_collineation fp_6483 fl_6483.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6483 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6483 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6483.

Lemma collineation_6484 : is_collineation fp_6484 fl_6484.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6484 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6484 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6484.

Lemma collineation_6485 : is_collineation fp_6485 fl_6485.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6485 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6485 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6485.

Lemma collineation_6486 : is_collineation fp_6486 fl_6486.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6486 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6486 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6486.

Lemma collineation_6487 : is_collineation fp_6487 fl_6487.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6487 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6487 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6487.

Lemma collineation_6488 : is_collineation fp_6488 fl_6488.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6488 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6488 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6488.

Lemma collineation_6489 : is_collineation fp_6489 fl_6489.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6489 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6489 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6489.

Lemma collineation_6490 : is_collineation fp_6490 fl_6490.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6490 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6490 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6490.

Lemma collineation_6491 : is_collineation fp_6491 fl_6491.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6491 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6491 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6491.

Lemma collineation_6492 : is_collineation fp_6492 fl_6492.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6492 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6492 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6492.

Lemma collineation_6493 : is_collineation fp_6493 fl_6493.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6493 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6493 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6493.

Lemma collineation_6494 : is_collineation fp_6494 fl_6494.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6494 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6494 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6494.

Lemma collineation_6495 : is_collineation fp_6495 fl_6495.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6495 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6495 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6495.

Lemma collineation_6496 : is_collineation fp_6496 fl_6496.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6496 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6496 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6496.

Lemma collineation_6497 : is_collineation fp_6497 fl_6497.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6497 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6497 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6497.

Lemma collineation_6498 : is_collineation fp_6498 fl_6498.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6498 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6498 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6498.

Lemma collineation_6499 : is_collineation fp_6499 fl_6499.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6499 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6499 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6499.

Lemma collineation_6500 : is_collineation fp_6500 fl_6500.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6500 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6500 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6500.

Lemma collineation_6501 : is_collineation fp_6501 fl_6501.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6501 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6501 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6501.

Lemma collineation_6502 : is_collineation fp_6502 fl_6502.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6502 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6502 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6502.

Lemma collineation_6503 : is_collineation fp_6503 fl_6503.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6503 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6503 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6503.

Lemma collineation_6504 : is_collineation fp_6504 fl_6504.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6504 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6504 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6504.

Lemma collineation_6505 : is_collineation fp_6505 fl_6505.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6505 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6505 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6505.

Lemma collineation_6506 : is_collineation fp_6506 fl_6506.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6506 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6506 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6506.

Lemma collineation_6507 : is_collineation fp_6507 fl_6507.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6507 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6507 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6507.

Lemma collineation_6508 : is_collineation fp_6508 fl_6508.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6508 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6508 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6508.

Lemma collineation_6509 : is_collineation fp_6509 fl_6509.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6509 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6509 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6509.

Lemma collineation_6510 : is_collineation fp_6510 fl_6510.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6510 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6510 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6510.

Lemma collineation_6511 : is_collineation fp_6511 fl_6511.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6511 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6511 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6511.

Lemma collineation_6512 : is_collineation fp_6512 fl_6512.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6512 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6512 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6512.

Lemma collineation_6513 : is_collineation fp_6513 fl_6513.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6513 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6513 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6513.

Lemma collineation_6514 : is_collineation fp_6514 fl_6514.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6514 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6514 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6514.

Lemma collineation_6515 : is_collineation fp_6515 fl_6515.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6515 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6515 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6515.

Lemma collineation_6516 : is_collineation fp_6516 fl_6516.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6516 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6516 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6516.

Lemma collineation_6517 : is_collineation fp_6517 fl_6517.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6517 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6517 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6517.

Lemma collineation_6518 : is_collineation fp_6518 fl_6518.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6518 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6518 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6518.

Lemma collineation_6519 : is_collineation fp_6519 fl_6519.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6519 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6519 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6519.

Lemma collineation_6520 : is_collineation fp_6520 fl_6520.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6520 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6520 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6520.

Lemma collineation_6521 : is_collineation fp_6521 fl_6521.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6521 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6521 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6521.

Lemma collineation_6522 : is_collineation fp_6522 fl_6522.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6522 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6522 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6522.

Lemma collineation_6523 : is_collineation fp_6523 fl_6523.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6523 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6523 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6523.

Lemma collineation_6524 : is_collineation fp_6524 fl_6524.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6524 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6524 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6524.

Lemma collineation_6525 : is_collineation fp_6525 fl_6525.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6525 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6525 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6525.

Lemma collineation_6526 : is_collineation fp_6526 fl_6526.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6526 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6526 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6526.

Lemma collineation_6527 : is_collineation fp_6527 fl_6527.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6527 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6527 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6527.

Lemma collineation_6528 : is_collineation fp_6528 fl_6528.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6528 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6528 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6528.

Lemma collineation_6529 : is_collineation fp_6529 fl_6529.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6529 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6529 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6529.

Lemma collineation_6530 : is_collineation fp_6530 fl_6530.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6530 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6530 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6530.

Lemma collineation_6531 : is_collineation fp_6531 fl_6531.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6531 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6531 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6531.

Lemma collineation_6532 : is_collineation fp_6532 fl_6532.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6532 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6532 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6532.

Lemma collineation_6533 : is_collineation fp_6533 fl_6533.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6533 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6533 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6533.

Lemma collineation_6534 : is_collineation fp_6534 fl_6534.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6534 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6534 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6534.

Lemma collineation_6535 : is_collineation fp_6535 fl_6535.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6535 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6535 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6535.

Lemma collineation_6536 : is_collineation fp_6536 fl_6536.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6536 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6536 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6536.

Lemma collineation_6537 : is_collineation fp_6537 fl_6537.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6537 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6537 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6537.

Lemma collineation_6538 : is_collineation fp_6538 fl_6538.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6538 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6538 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6538.

Lemma collineation_6539 : is_collineation fp_6539 fl_6539.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6539 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6539 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6539.

Lemma collineation_6540 : is_collineation fp_6540 fl_6540.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6540 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6540 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6540.

Lemma collineation_6541 : is_collineation fp_6541 fl_6541.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6541 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6541 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6541.

Lemma collineation_6542 : is_collineation fp_6542 fl_6542.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6542 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6542 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6542.

Lemma collineation_6543 : is_collineation fp_6543 fl_6543.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6543 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6543 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6543.

Lemma collineation_6544 : is_collineation fp_6544 fl_6544.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6544 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6544 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6544.

Lemma collineation_6545 : is_collineation fp_6545 fl_6545.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6545 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6545 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6545.

Lemma collineation_6546 : is_collineation fp_6546 fl_6546.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6546 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6546 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6546.

Lemma collineation_6547 : is_collineation fp_6547 fl_6547.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6547 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6547 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6547.

Lemma collineation_6548 : is_collineation fp_6548 fl_6548.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6548 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6548 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6548.

Lemma collineation_6549 : is_collineation fp_6549 fl_6549.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6549 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6549 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6549.

Lemma collineation_6550 : is_collineation fp_6550 fl_6550.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6550 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6550 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6550.

Lemma collineation_6551 : is_collineation fp_6551 fl_6551.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6551 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6551 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6551.

Lemma collineation_6552 : is_collineation fp_6552 fl_6552.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6552 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6552 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6552.

Lemma collineation_6553 : is_collineation fp_6553 fl_6553.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6553 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6553 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6553.

Lemma collineation_6554 : is_collineation fp_6554 fl_6554.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6554 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6554 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6554.

Lemma collineation_6555 : is_collineation fp_6555 fl_6555.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6555 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6555 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6555.

Lemma collineation_6556 : is_collineation fp_6556 fl_6556.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6556 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6556 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6556.

Lemma collineation_6557 : is_collineation fp_6557 fl_6557.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6557 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6557 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6557.

Lemma collineation_6558 : is_collineation fp_6558 fl_6558.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6558 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6558 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6558.

Lemma collineation_6559 : is_collineation fp_6559 fl_6559.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6559 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6559 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6559.

Lemma collineation_6560 : is_collineation fp_6560 fl_6560.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6560 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6560 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6560.

Lemma collineation_6561 : is_collineation fp_6561 fl_6561.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6561 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6561 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6561.

Lemma collineation_6562 : is_collineation fp_6562 fl_6562.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6562 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6562 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6562.

Lemma collineation_6563 : is_collineation fp_6563 fl_6563.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6563 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6563 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6563.

Lemma collineation_6564 : is_collineation fp_6564 fl_6564.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6564 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6564 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6564.

Lemma collineation_6565 : is_collineation fp_6565 fl_6565.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6565 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6565 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6565.

Lemma collineation_6566 : is_collineation fp_6566 fl_6566.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6566 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6566 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6566.

Lemma collineation_6567 : is_collineation fp_6567 fl_6567.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6567 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6567 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6567.

Lemma collineation_6568 : is_collineation fp_6568 fl_6568.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6568 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6568 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6568.

Lemma collineation_6569 : is_collineation fp_6569 fl_6569.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6569 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6569 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6569.

Lemma collineation_6570 : is_collineation fp_6570 fl_6570.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6570 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6570 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6570.

Lemma collineation_6571 : is_collineation fp_6571 fl_6571.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6571 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6571 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6571.

Lemma collineation_6572 : is_collineation fp_6572 fl_6572.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6572 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6572 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6572.

Lemma collineation_6573 : is_collineation fp_6573 fl_6573.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6573 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6573 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6573.

Lemma collineation_6574 : is_collineation fp_6574 fl_6574.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6574 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6574 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6574.

Lemma collineation_6575 : is_collineation fp_6575 fl_6575.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6575 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6575 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6575.

Lemma collineation_6576 : is_collineation fp_6576 fl_6576.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6576 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6576 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6576.

Lemma collineation_6577 : is_collineation fp_6577 fl_6577.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6577 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6577 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6577.

Lemma collineation_6578 : is_collineation fp_6578 fl_6578.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6578 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6578 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6578.

Lemma collineation_6579 : is_collineation fp_6579 fl_6579.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6579 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6579 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6579.

Lemma collineation_6580 : is_collineation fp_6580 fl_6580.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6580 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6580 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6580.

Lemma collineation_6581 : is_collineation fp_6581 fl_6581.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6581 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6581 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6581.

Lemma collineation_6582 : is_collineation fp_6582 fl_6582.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6582 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6582 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6582.

Lemma collineation_6583 : is_collineation fp_6583 fl_6583.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6583 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6583 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6583.

Lemma collineation_6584 : is_collineation fp_6584 fl_6584.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6584 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6584 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6584.

Lemma collineation_6585 : is_collineation fp_6585 fl_6585.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6585 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6585 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6585.

Lemma collineation_6586 : is_collineation fp_6586 fl_6586.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6586 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6586 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6586.

Lemma collineation_6587 : is_collineation fp_6587 fl_6587.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6587 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6587 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6587.

Lemma collineation_6588 : is_collineation fp_6588 fl_6588.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6588 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6588 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6588.

Lemma collineation_6589 : is_collineation fp_6589 fl_6589.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6589 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6589 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6589.

Lemma collineation_6590 : is_collineation fp_6590 fl_6590.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6590 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6590 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6590.

Lemma collineation_6591 : is_collineation fp_6591 fl_6591.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6591 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6591 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6591.

Lemma collineation_6592 : is_collineation fp_6592 fl_6592.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6592 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6592 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6592.

Lemma collineation_6593 : is_collineation fp_6593 fl_6593.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6593 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6593 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6593.

Lemma collineation_6594 : is_collineation fp_6594 fl_6594.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6594 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6594 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6594.

Lemma collineation_6595 : is_collineation fp_6595 fl_6595.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6595 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6595 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6595.

Lemma collineation_6596 : is_collineation fp_6596 fl_6596.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6596 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6596 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6596.

Lemma collineation_6597 : is_collineation fp_6597 fl_6597.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6597 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6597 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6597.

Lemma collineation_6598 : is_collineation fp_6598 fl_6598.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6598 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6598 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6598.

Lemma collineation_6599 : is_collineation fp_6599 fl_6599.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6599 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6599 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6599.

Lemma collineation_6600 : is_collineation fp_6600 fl_6600.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6600 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6600 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6600.

Lemma collineation_6601 : is_collineation fp_6601 fl_6601.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6601 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6601 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6601.

Lemma collineation_6602 : is_collineation fp_6602 fl_6602.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6602 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6602 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6602.

Lemma collineation_6603 : is_collineation fp_6603 fl_6603.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6603 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6603 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6603.

Lemma collineation_6604 : is_collineation fp_6604 fl_6604.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6604 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6604 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6604.

Lemma collineation_6605 : is_collineation fp_6605 fl_6605.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6605 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6605 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6605.

Lemma collineation_6606 : is_collineation fp_6606 fl_6606.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6606 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6606 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6606.

Lemma collineation_6607 : is_collineation fp_6607 fl_6607.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6607 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6607 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6607.

Lemma collineation_6608 : is_collineation fp_6608 fl_6608.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6608 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6608 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6608.

Lemma collineation_6609 : is_collineation fp_6609 fl_6609.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6609 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6609 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6609.

Lemma collineation_6610 : is_collineation fp_6610 fl_6610.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6610 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6610 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6610.

Lemma collineation_6611 : is_collineation fp_6611 fl_6611.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6611 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6611 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6611.

Lemma collineation_6612 : is_collineation fp_6612 fl_6612.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6612 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6612 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6612.

Lemma collineation_6613 : is_collineation fp_6613 fl_6613.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6613 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6613 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6613.

Lemma collineation_6614 : is_collineation fp_6614 fl_6614.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6614 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6614 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6614.

Lemma collineation_6615 : is_collineation fp_6615 fl_6615.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6615 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6615 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6615.

Lemma collineation_6616 : is_collineation fp_6616 fl_6616.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6616 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6616 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6616.

Lemma collineation_6617 : is_collineation fp_6617 fl_6617.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6617 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6617 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6617.

Lemma collineation_6618 : is_collineation fp_6618 fl_6618.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6618 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6618 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6618.

Lemma collineation_6619 : is_collineation fp_6619 fl_6619.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6619 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6619 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6619.

Lemma collineation_6620 : is_collineation fp_6620 fl_6620.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6620 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6620 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6620.

Lemma collineation_6621 : is_collineation fp_6621 fl_6621.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6621 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6621 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6621.

Lemma collineation_6622 : is_collineation fp_6622 fl_6622.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6622 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6622 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6622.

Lemma collineation_6623 : is_collineation fp_6623 fl_6623.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6623 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6623 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6623.

Lemma collineation_6624 : is_collineation fp_6624 fl_6624.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6624 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6624 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6624.

Lemma collineation_6625 : is_collineation fp_6625 fl_6625.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6625 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6625 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6625.

Lemma collineation_6626 : is_collineation fp_6626 fl_6626.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6626 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6626 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6626.

Lemma collineation_6627 : is_collineation fp_6627 fl_6627.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6627 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6627 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6627.

Lemma collineation_6628 : is_collineation fp_6628 fl_6628.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6628 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6628 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6628.

Lemma collineation_6629 : is_collineation fp_6629 fl_6629.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6629 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6629 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6629.

Lemma collineation_6630 : is_collineation fp_6630 fl_6630.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6630 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6630 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6630.

Lemma collineation_6631 : is_collineation fp_6631 fl_6631.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6631 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6631 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6631.

Lemma collineation_6632 : is_collineation fp_6632 fl_6632.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6632 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6632 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6632.

Lemma collineation_6633 : is_collineation fp_6633 fl_6633.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6633 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6633 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6633.

Lemma collineation_6634 : is_collineation fp_6634 fl_6634.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6634 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6634 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6634.

Lemma collineation_6635 : is_collineation fp_6635 fl_6635.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6635 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6635 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6635.

Lemma collineation_6636 : is_collineation fp_6636 fl_6636.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6636 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6636 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6636.

Lemma collineation_6637 : is_collineation fp_6637 fl_6637.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6637 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6637 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6637.

Lemma collineation_6638 : is_collineation fp_6638 fl_6638.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6638 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6638 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6638.

Lemma collineation_6639 : is_collineation fp_6639 fl_6639.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6639 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6639 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6639.

Lemma collineation_6640 : is_collineation fp_6640 fl_6640.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6640 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6640 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6640.

Lemma collineation_6641 : is_collineation fp_6641 fl_6641.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6641 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6641 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6641.

Lemma collineation_6642 : is_collineation fp_6642 fl_6642.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6642 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6642 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6642.

Lemma collineation_6643 : is_collineation fp_6643 fl_6643.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6643 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6643 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6643.

Lemma collineation_6644 : is_collineation fp_6644 fl_6644.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6644 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6644 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6644.

Lemma collineation_6645 : is_collineation fp_6645 fl_6645.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6645 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6645 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6645.

Lemma collineation_6646 : is_collineation fp_6646 fl_6646.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6646 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6646 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6646.

Lemma collineation_6647 : is_collineation fp_6647 fl_6647.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6647 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6647 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6647.

Lemma collineation_6648 : is_collineation fp_6648 fl_6648.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6648 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6648 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6648.

Lemma collineation_6649 : is_collineation fp_6649 fl_6649.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6649 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6649 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6649.

Lemma collineation_6650 : is_collineation fp_6650 fl_6650.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6650 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6650 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6650.

Lemma collineation_6651 : is_collineation fp_6651 fl_6651.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6651 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6651 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6651.

Lemma collineation_6652 : is_collineation fp_6652 fl_6652.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6652 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6652 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6652.

Lemma collineation_6653 : is_collineation fp_6653 fl_6653.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6653 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6653 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6653.

Lemma collineation_6654 : is_collineation fp_6654 fl_6654.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6654 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6654 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6654.

Lemma collineation_6655 : is_collineation fp_6655 fl_6655.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6655 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6655 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6655.

Lemma collineation_6656 : is_collineation fp_6656 fl_6656.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6656 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6656 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6656.

Lemma collineation_6657 : is_collineation fp_6657 fl_6657.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6657 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6657 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6657.

Lemma collineation_6658 : is_collineation fp_6658 fl_6658.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6658 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6658 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6658.

Lemma collineation_6659 : is_collineation fp_6659 fl_6659.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6659 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6659 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6659.

Lemma collineation_6660 : is_collineation fp_6660 fl_6660.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6660 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6660 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6660.

Lemma collineation_6661 : is_collineation fp_6661 fl_6661.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6661 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6661 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6661.

Lemma collineation_6662 : is_collineation fp_6662 fl_6662.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6662 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6662 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6662.

Lemma collineation_6663 : is_collineation fp_6663 fl_6663.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6663 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6663 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6663.

Lemma collineation_6664 : is_collineation fp_6664 fl_6664.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6664 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6664 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6664.

Lemma collineation_6665 : is_collineation fp_6665 fl_6665.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6665 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6665 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6665.

Lemma collineation_6666 : is_collineation fp_6666 fl_6666.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6666 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6666 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6666.

Lemma collineation_6667 : is_collineation fp_6667 fl_6667.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6667 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6667 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6667.

Lemma collineation_6668 : is_collineation fp_6668 fl_6668.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6668 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6668 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6668.

Lemma collineation_6669 : is_collineation fp_6669 fl_6669.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6669 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6669 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6669.

Lemma collineation_6670 : is_collineation fp_6670 fl_6670.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6670 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6670 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6670.

Lemma collineation_6671 : is_collineation fp_6671 fl_6671.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6671 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6671 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6671.

Lemma collineation_6672 : is_collineation fp_6672 fl_6672.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6672 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6672 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6672.

Lemma collineation_6673 : is_collineation fp_6673 fl_6673.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6673 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6673 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6673.

Lemma collineation_6674 : is_collineation fp_6674 fl_6674.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6674 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6674 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6674.

Lemma collineation_6675 : is_collineation fp_6675 fl_6675.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6675 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6675 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6675.

Lemma collineation_6676 : is_collineation fp_6676 fl_6676.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6676 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6676 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6676.

Lemma collineation_6677 : is_collineation fp_6677 fl_6677.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6677 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6677 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6677.

Lemma collineation_6678 : is_collineation fp_6678 fl_6678.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6678 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6678 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6678.

Lemma collineation_6679 : is_collineation fp_6679 fl_6679.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6679 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6679 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6679.

Lemma collineation_6680 : is_collineation fp_6680 fl_6680.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6680 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6680 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6680.

Lemma collineation_6681 : is_collineation fp_6681 fl_6681.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6681 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6681 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6681.

Lemma collineation_6682 : is_collineation fp_6682 fl_6682.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6682 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6682 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6682.

Lemma collineation_6683 : is_collineation fp_6683 fl_6683.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6683 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6683 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6683.

Lemma collineation_6684 : is_collineation fp_6684 fl_6684.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6684 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6684 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6684.

Lemma collineation_6685 : is_collineation fp_6685 fl_6685.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6685 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6685 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6685.

Lemma collineation_6686 : is_collineation fp_6686 fl_6686.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6686 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6686 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6686.

Lemma collineation_6687 : is_collineation fp_6687 fl_6687.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6687 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6687 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6687.

Lemma collineation_6688 : is_collineation fp_6688 fl_6688.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6688 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6688 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6688.

Lemma collineation_6689 : is_collineation fp_6689 fl_6689.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6689 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6689 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6689.

Lemma collineation_6690 : is_collineation fp_6690 fl_6690.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6690 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6690 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6690.

Lemma collineation_6691 : is_collineation fp_6691 fl_6691.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6691 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6691 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6691.

Lemma collineation_6692 : is_collineation fp_6692 fl_6692.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6692 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6692 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6692.

Lemma collineation_6693 : is_collineation fp_6693 fl_6693.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6693 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6693 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6693.

Lemma collineation_6694 : is_collineation fp_6694 fl_6694.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6694 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6694 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6694.

Lemma collineation_6695 : is_collineation fp_6695 fl_6695.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6695 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6695 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6695.

Lemma collineation_6696 : is_collineation fp_6696 fl_6696.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6696 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6696 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6696.

Lemma collineation_6697 : is_collineation fp_6697 fl_6697.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6697 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6697 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6697.

Lemma collineation_6698 : is_collineation fp_6698 fl_6698.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6698 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6698 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6698.

Lemma collineation_6699 : is_collineation fp_6699 fl_6699.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6699 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6699 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6699.

Lemma collineation_6700 : is_collineation fp_6700 fl_6700.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6700 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6700 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6700.

Lemma collineation_6701 : is_collineation fp_6701 fl_6701.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6701 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6701 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6701.

Lemma collineation_6702 : is_collineation fp_6702 fl_6702.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6702 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6702 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6702.

Lemma collineation_6703 : is_collineation fp_6703 fl_6703.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6703 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6703 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6703.

Lemma collineation_6704 : is_collineation fp_6704 fl_6704.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6704 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6704 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6704.

Lemma collineation_6705 : is_collineation fp_6705 fl_6705.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6705 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6705 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6705.

Lemma collineation_6706 : is_collineation fp_6706 fl_6706.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6706 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6706 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6706.

Lemma collineation_6707 : is_collineation fp_6707 fl_6707.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6707 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6707 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6707.

Lemma collineation_6708 : is_collineation fp_6708 fl_6708.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6708 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6708 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6708.

Lemma collineation_6709 : is_collineation fp_6709 fl_6709.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6709 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6709 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6709.

Lemma collineation_6710 : is_collineation fp_6710 fl_6710.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6710 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6710 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6710.

Lemma collineation_6711 : is_collineation fp_6711 fl_6711.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6711 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6711 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6711.

Lemma collineation_6712 : is_collineation fp_6712 fl_6712.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6712 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6712 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6712.

Lemma collineation_6713 : is_collineation fp_6713 fl_6713.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6713 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6713 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6713.

Lemma collineation_6714 : is_collineation fp_6714 fl_6714.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6714 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6714 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6714.

Lemma collineation_6715 : is_collineation fp_6715 fl_6715.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6715 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6715 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6715.

Lemma collineation_6716 : is_collineation fp_6716 fl_6716.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6716 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6716 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6716.

Lemma collineation_6717 : is_collineation fp_6717 fl_6717.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6717 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6717 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6717.

Lemma collineation_6718 : is_collineation fp_6718 fl_6718.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6718 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6718 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6718.

Lemma collineation_6719 : is_collineation fp_6719 fl_6719.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_6719 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_6719 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_6719.

Lemma is_col_all_c56 : forall fp fl, In (fp,fl) (all_c56++all_c57++all_c58++all_c59++all_c60++all_c61++all_c62++all_c63++all_c64++all_c65++all_c66++all_c67++all_c68++all_c69) -> is_collineation fp fl.
Proof.
 intros fp fl HIn_S.
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5376 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5377 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5378 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5379 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5380 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5381 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5382 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5383 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5384 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5385 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5386 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5387 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5388 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5389 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5390 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5391 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5392 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5393 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5394 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5395 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5396 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5397 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5398 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5399 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5400 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5401 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5402 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5403 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5404 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5405 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5406 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5407 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5408 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5409 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5410 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5411 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5412 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5413 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5414 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5415 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5416 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5417 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5418 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5419 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5420 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5421 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5422 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5423 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5424 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5425 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5426 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5427 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5428 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5429 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5430 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5431 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5432 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5433 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5434 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5435 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5436 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5437 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5438 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5439 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5440 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5441 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5442 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5443 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5444 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5445 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5446 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5447 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5448 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5449 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5450 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5451 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5452 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5453 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5454 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5455 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5456 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5457 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5458 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5459 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5460 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5461 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5462 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5463 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5464 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5465 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5466 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5467 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5468 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5469 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5470 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5471 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5472 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5473 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5474 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5475 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5476 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5477 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5478 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5479 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5480 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5481 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5482 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5483 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5484 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5485 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5486 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5487 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5488 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5489 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5490 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5491 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5492 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5493 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5494 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5495 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5496 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5497 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5498 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5499 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5500 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5501 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5502 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5503 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5504 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5505 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5506 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5507 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5508 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5509 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5510 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5511 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5512 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5513 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5514 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5515 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5516 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5517 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5518 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5519 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5520 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5521 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5522 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5523 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5524 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5525 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5526 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5527 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5528 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5529 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5530 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5531 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5532 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5533 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5534 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5535 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5536 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5537 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5538 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5539 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5540 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5541 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5542 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5543 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5544 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5545 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5546 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5547 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5548 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5549 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5550 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5551 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5552 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5553 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5554 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5555 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5556 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5557 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5558 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5559 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5560 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5561 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5562 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5563 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5564 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5565 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5566 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5567 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5568 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5569 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5570 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5571 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5572 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5573 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5574 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5575 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5576 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5577 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5578 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5579 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5580 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5581 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5582 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5583 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5584 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5585 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5586 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5587 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5588 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5589 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5590 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5591 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5592 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5593 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5594 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5595 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5596 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5597 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5598 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5599 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5600 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5601 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5602 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5603 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5604 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5605 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5606 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5607 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5608 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5609 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5610 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5611 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5612 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5613 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5614 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5615 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5616 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5617 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5618 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5619 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5620 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5621 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5622 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5623 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5624 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5625 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5626 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5627 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5628 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5629 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5630 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5631 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5632 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5633 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5634 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5635 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5636 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5637 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5638 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5639 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5640 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5641 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5642 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5643 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5644 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5645 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5646 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5647 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5648 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5649 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5650 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5651 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5652 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5653 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5654 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5655 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5656 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5657 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5658 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5659 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5660 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5661 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5662 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5663 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5664 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5665 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5666 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5667 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5668 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5669 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5670 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5671 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5672 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5673 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5674 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5675 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5676 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5677 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5678 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5679 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5680 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5681 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5682 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5683 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5684 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5685 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5686 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5687 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5688 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5689 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5690 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5691 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5692 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5693 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5694 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5695 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5696 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5697 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5698 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5699 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5700 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5701 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5702 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5703 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5704 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5705 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5706 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5707 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5708 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5709 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5710 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5711 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5712 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5713 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5714 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5715 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5716 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5717 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5718 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5719 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5720 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5721 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5722 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5723 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5724 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5725 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5726 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5727 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5728 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5729 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5730 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5731 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5732 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5733 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5734 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5735 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5736 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5737 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5738 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5739 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5740 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5741 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5742 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5743 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5744 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5745 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5746 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5747 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5748 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5749 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5750 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5751 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5752 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5753 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5754 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5755 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5756 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5757 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5758 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5759 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5760 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5761 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5762 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5763 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5764 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5765 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5766 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5767 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5768 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5769 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5770 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5771 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5772 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5773 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5774 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5775 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5776 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5777 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5778 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5779 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5780 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5781 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5782 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5783 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5784 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5785 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5786 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5787 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5788 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5789 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5790 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5791 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5792 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5793 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5794 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5795 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5796 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5797 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5798 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5799 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5800 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5801 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5802 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5803 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5804 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5805 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5806 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5807 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5808 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5809 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5810 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5811 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5812 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5813 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5814 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5815 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5816 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5817 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5818 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5819 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5820 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5821 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5822 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5823 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5824 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5825 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5826 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5827 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5828 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5829 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5830 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5831 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5832 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5833 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5834 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5835 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5836 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5837 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5838 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5839 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5840 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5841 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5842 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5843 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5844 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5845 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5846 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5847 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5848 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5849 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5850 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5851 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5852 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5853 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5854 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5855 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5856 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5857 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5858 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5859 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5860 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5861 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5862 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5863 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5864 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5865 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5866 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5867 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5868 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5869 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5870 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5871 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5872 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5873 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5874 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5875 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5876 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5877 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5878 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5879 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5880 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5881 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5882 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5883 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5884 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5885 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5886 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5887 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5888 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5889 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5890 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5891 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5892 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5893 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5894 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5895 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5896 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5897 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5898 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5899 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5900 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5901 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5902 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5903 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5904 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5905 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5906 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5907 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5908 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5909 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5910 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5911 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5912 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5913 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5914 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5915 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5916 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5917 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5918 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5919 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5920 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5921 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5922 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5923 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5924 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5925 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5926 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5927 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5928 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5929 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5930 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5931 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5932 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5933 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5934 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5935 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5936 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5937 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5938 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5939 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5940 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5941 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5942 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5943 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5944 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5945 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5946 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5947 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5948 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5949 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5950 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5951 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5952 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5953 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5954 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5955 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5956 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5957 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5958 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5959 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5960 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5961 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5962 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5963 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5964 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5965 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5966 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5967 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5968 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5969 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5970 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5971 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5972 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5973 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5974 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5975 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5976 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5977 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5978 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5979 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5980 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5981 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5982 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5983 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5984 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5985 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5986 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5987 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5988 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5989 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5990 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5991 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5992 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5993 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5994 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5995 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5996 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5997 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5998 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_5999 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6000 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6001 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6002 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6003 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6004 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6005 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6006 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6007 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6008 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6009 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6010 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6011 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6012 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6013 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6014 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6015 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6016 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6017 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6018 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6019 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6020 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6021 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6022 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6023 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6024 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6025 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6026 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6027 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6028 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6029 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6030 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6031 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6032 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6033 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6034 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6035 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6036 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6037 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6038 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6039 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6040 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6041 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6042 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6043 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6044 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6045 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6046 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6047 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6048 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6049 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6050 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6051 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6052 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6053 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6054 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6055 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6056 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6057 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6058 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6059 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6060 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6061 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6062 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6063 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6064 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6065 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6066 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6067 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6068 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6069 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6070 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6071 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6072 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6073 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6074 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6075 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6076 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6077 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6078 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6079 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6080 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6081 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6082 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6083 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6084 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6085 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6086 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6087 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6088 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6089 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6090 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6091 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6092 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6093 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6094 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6095 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6096 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6097 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6098 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6099 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6100 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6101 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6102 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6103 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6104 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6105 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6106 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6107 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6108 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6109 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6110 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6111 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6112 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6113 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6114 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6115 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6116 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6117 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6118 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6119 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6120 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6121 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6122 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6123 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6124 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6125 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6126 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6127 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6128 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6129 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6130 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6131 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6132 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6133 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6134 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6135 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6136 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6137 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6138 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6139 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6140 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6141 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6142 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6143 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6144 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6145 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6146 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6147 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6148 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6149 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6150 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6151 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6152 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6153 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6154 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6155 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6156 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6157 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6158 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6159 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6160 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6161 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6162 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6163 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6164 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6165 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6166 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6167 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6168 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6169 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6170 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6171 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6172 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6173 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6174 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6175 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6176 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6177 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6178 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6179 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6180 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6181 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6182 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6183 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6184 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6185 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6186 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6187 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6188 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6189 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6190 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6191 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6192 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6193 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6194 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6195 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6196 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6197 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6198 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6199 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6200 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6201 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6202 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6203 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6204 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6205 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6206 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6207 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6208 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6209 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6210 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6211 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6212 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6213 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6214 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6215 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6216 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6217 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6218 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6219 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6220 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6221 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6222 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6223 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6224 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6225 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6226 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6227 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6228 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6229 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6230 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6231 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6232 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6233 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6234 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6235 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6236 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6237 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6238 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6239 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6240 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6241 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6242 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6243 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6244 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6245 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6246 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6247 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6248 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6249 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6250 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6251 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6252 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6253 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6254 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6255 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6256 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6257 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6258 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6259 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6260 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6261 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6262 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6263 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6264 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6265 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6266 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6267 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6268 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6269 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6270 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6271 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6272 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6273 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6274 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6275 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6276 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6277 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6278 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6279 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6280 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6281 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6282 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6283 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6284 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6285 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6286 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6287 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6288 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6289 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6290 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6291 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6292 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6293 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6294 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6295 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6296 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6297 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6298 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6299 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6300 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6301 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6302 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6303 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6304 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6305 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6306 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6307 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6308 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6309 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6310 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6311 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6312 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6313 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6314 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6315 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6316 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6317 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6318 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6319 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6320 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6321 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6322 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6323 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6324 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6325 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6326 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6327 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6328 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6329 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6330 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6331 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6332 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6333 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6334 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6335 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6336 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6337 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6338 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6339 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6340 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6341 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6342 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6343 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6344 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6345 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6346 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6347 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6348 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6349 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6350 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6351 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6352 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6353 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6354 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6355 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6356 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6357 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6358 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6359 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6360 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6361 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6362 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6363 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6364 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6365 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6366 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6367 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6368 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6369 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6370 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6371 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6372 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6373 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6374 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6375 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6376 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6377 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6378 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6379 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6380 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6381 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6382 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6383 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6384 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6385 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6386 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6387 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6388 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6389 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6390 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6391 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6392 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6393 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6394 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6395 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6396 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6397 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6398 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6399 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6400 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6401 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6402 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6403 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6404 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6405 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6406 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6407 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6408 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6409 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6410 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6411 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6412 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6413 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6414 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6415 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6416 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6417 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6418 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6419 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6420 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6421 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6422 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6423 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6424 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6425 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6426 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6427 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6428 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6429 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6430 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6431 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6432 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6433 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6434 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6435 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6436 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6437 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6438 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6439 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6440 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6441 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6442 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6443 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6444 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6445 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6446 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6447 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6448 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6449 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6450 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6451 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6452 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6453 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6454 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6455 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6456 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6457 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6458 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6459 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6460 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6461 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6462 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6463 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6464 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6465 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6466 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6467 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6468 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6469 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6470 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6471 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6472 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6473 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6474 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6475 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6476 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6477 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6478 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6479 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6480 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6481 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6482 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6483 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6484 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6485 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6486 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6487 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6488 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6489 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6490 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6491 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6492 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6493 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6494 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6495 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6496 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6497 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6498 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6499 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6500 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6501 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6502 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6503 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6504 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6505 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6506 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6507 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6508 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6509 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6510 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6511 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6512 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6513 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6514 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6515 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6516 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6517 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6518 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6519 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6520 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6521 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6522 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6523 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6524 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6525 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6526 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6527 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6528 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6529 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6530 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6531 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6532 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6533 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6534 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6535 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6536 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6537 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6538 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6539 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6540 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6541 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6542 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6543 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6544 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6545 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6546 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6547 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6548 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6549 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6550 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6551 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6552 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6553 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6554 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6555 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6556 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6557 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6558 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6559 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6560 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6561 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6562 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6563 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6564 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6565 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6566 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6567 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6568 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6569 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6570 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6571 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6572 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6573 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6574 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6575 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6576 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6577 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6578 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6579 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6580 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6581 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6582 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6583 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6584 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6585 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6586 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6587 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6588 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6589 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6590 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6591 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6592 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6593 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6594 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6595 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6596 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6597 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6598 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6599 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6600 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6601 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6602 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6603 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6604 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6605 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6606 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6607 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6608 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6609 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6610 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6611 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6612 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6613 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6614 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6615 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6616 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6617 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6618 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6619 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6620 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6621 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6622 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6623 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6624 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6625 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6626 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6627 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6628 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6629 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6630 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6631 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6632 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6633 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6634 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6635 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6636 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6637 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6638 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6639 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6640 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6641 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6642 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6643 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6644 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6645 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6646 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6647 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6648 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6649 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6650 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6651 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6652 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6653 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6654 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6655 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6656 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6657 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6658 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6659 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6660 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6661 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6662 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6663 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6664 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6665 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6666 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6667 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6668 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6669 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6670 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6671 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6672 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6673 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6674 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6675 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6676 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6677 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6678 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6679 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6680 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6681 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6682 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6683 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6684 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6685 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6686 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6687 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6688 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6689 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6690 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6691 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6692 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6693 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6694 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6695 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6696 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6697 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6698 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6699 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6700 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6701 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6702 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6703 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6704 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6705 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6706 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6707 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6708 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6709 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6710 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6711 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6712 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6713 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6714 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6715 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6716 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6717 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6718 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_6719 | idtac].
 destruct (in_nil HIn_S).
Qed.

