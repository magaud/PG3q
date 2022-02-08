Require Import ssreflect ssrfun ssrbool.
Require Import Generic.lemmas.
Require Import PG32.pg32_inductive PG32.pg32_spreads_collineations.
Require Import PG32.pg32_automorphisms.
Require Import PG32.pg32_automorphisms_inv.
Require Import Lists.List.
Import ListNotations.
Require Import Arith.

Lemma collineation_9408 : is_collineation fp_9408 fl_9408.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9408 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9408 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9408.

Lemma collineation_9409 : is_collineation fp_9409 fl_9409.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9409 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9409 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9409.

Lemma collineation_9410 : is_collineation fp_9410 fl_9410.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9410 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9410 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9410.

Lemma collineation_9411 : is_collineation fp_9411 fl_9411.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9411 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9411 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9411.

Lemma collineation_9412 : is_collineation fp_9412 fl_9412.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9412 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9412 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9412.

Lemma collineation_9413 : is_collineation fp_9413 fl_9413.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9413 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9413 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9413.

Lemma collineation_9414 : is_collineation fp_9414 fl_9414.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9414 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9414 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9414.

Lemma collineation_9415 : is_collineation fp_9415 fl_9415.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9415 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9415 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9415.

Lemma collineation_9416 : is_collineation fp_9416 fl_9416.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9416 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9416 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9416.

Lemma collineation_9417 : is_collineation fp_9417 fl_9417.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9417 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9417 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9417.

Lemma collineation_9418 : is_collineation fp_9418 fl_9418.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9418 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9418 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9418.

Lemma collineation_9419 : is_collineation fp_9419 fl_9419.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9419 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9419 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9419.

Lemma collineation_9420 : is_collineation fp_9420 fl_9420.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9420 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9420 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9420.

Lemma collineation_9421 : is_collineation fp_9421 fl_9421.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9421 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9421 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9421.

Lemma collineation_9422 : is_collineation fp_9422 fl_9422.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9422 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9422 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9422.

Lemma collineation_9423 : is_collineation fp_9423 fl_9423.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9423 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9423 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9423.

Lemma collineation_9424 : is_collineation fp_9424 fl_9424.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9424 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9424 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9424.

Lemma collineation_9425 : is_collineation fp_9425 fl_9425.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9425 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9425 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9425.

Lemma collineation_9426 : is_collineation fp_9426 fl_9426.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9426 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9426 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9426.

Lemma collineation_9427 : is_collineation fp_9427 fl_9427.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9427 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9427 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9427.

Lemma collineation_9428 : is_collineation fp_9428 fl_9428.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9428 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9428 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9428.

Lemma collineation_9429 : is_collineation fp_9429 fl_9429.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9429 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9429 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9429.

Lemma collineation_9430 : is_collineation fp_9430 fl_9430.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9430 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9430 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9430.

Lemma collineation_9431 : is_collineation fp_9431 fl_9431.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9431 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9431 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9431.

Lemma collineation_9432 : is_collineation fp_9432 fl_9432.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9432 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9432 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9432.

Lemma collineation_9433 : is_collineation fp_9433 fl_9433.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9433 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9433 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9433.

Lemma collineation_9434 : is_collineation fp_9434 fl_9434.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9434 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9434 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9434.

Lemma collineation_9435 : is_collineation fp_9435 fl_9435.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9435 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9435 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9435.

Lemma collineation_9436 : is_collineation fp_9436 fl_9436.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9436 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9436 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9436.

Lemma collineation_9437 : is_collineation fp_9437 fl_9437.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9437 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9437 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9437.

Lemma collineation_9438 : is_collineation fp_9438 fl_9438.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9438 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9438 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9438.

Lemma collineation_9439 : is_collineation fp_9439 fl_9439.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9439 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9439 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9439.

Lemma collineation_9440 : is_collineation fp_9440 fl_9440.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9440 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9440 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9440.

Lemma collineation_9441 : is_collineation fp_9441 fl_9441.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9441 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9441 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9441.

Lemma collineation_9442 : is_collineation fp_9442 fl_9442.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9442 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9442 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9442.

Lemma collineation_9443 : is_collineation fp_9443 fl_9443.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9443 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9443 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9443.

Lemma collineation_9444 : is_collineation fp_9444 fl_9444.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9444 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9444 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9444.

Lemma collineation_9445 : is_collineation fp_9445 fl_9445.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9445 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9445 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9445.

Lemma collineation_9446 : is_collineation fp_9446 fl_9446.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9446 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9446 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9446.

Lemma collineation_9447 : is_collineation fp_9447 fl_9447.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9447 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9447 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9447.

Lemma collineation_9448 : is_collineation fp_9448 fl_9448.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9448 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9448 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9448.

Lemma collineation_9449 : is_collineation fp_9449 fl_9449.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9449 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9449 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9449.

Lemma collineation_9450 : is_collineation fp_9450 fl_9450.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9450 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9450 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9450.

Lemma collineation_9451 : is_collineation fp_9451 fl_9451.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9451 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9451 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9451.

Lemma collineation_9452 : is_collineation fp_9452 fl_9452.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9452 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9452 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9452.

Lemma collineation_9453 : is_collineation fp_9453 fl_9453.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9453 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9453 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9453.

Lemma collineation_9454 : is_collineation fp_9454 fl_9454.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9454 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9454 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9454.

Lemma collineation_9455 : is_collineation fp_9455 fl_9455.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9455 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9455 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9455.

Lemma collineation_9456 : is_collineation fp_9456 fl_9456.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9456 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9456 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9456.

Lemma collineation_9457 : is_collineation fp_9457 fl_9457.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9457 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9457 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9457.

Lemma collineation_9458 : is_collineation fp_9458 fl_9458.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9458 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9458 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9458.

Lemma collineation_9459 : is_collineation fp_9459 fl_9459.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9459 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9459 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9459.

Lemma collineation_9460 : is_collineation fp_9460 fl_9460.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9460 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9460 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9460.

Lemma collineation_9461 : is_collineation fp_9461 fl_9461.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9461 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9461 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9461.

Lemma collineation_9462 : is_collineation fp_9462 fl_9462.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9462 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9462 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9462.

Lemma collineation_9463 : is_collineation fp_9463 fl_9463.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9463 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9463 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9463.

Lemma collineation_9464 : is_collineation fp_9464 fl_9464.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9464 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9464 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9464.

Lemma collineation_9465 : is_collineation fp_9465 fl_9465.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9465 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9465 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9465.

Lemma collineation_9466 : is_collineation fp_9466 fl_9466.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9466 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9466 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9466.

Lemma collineation_9467 : is_collineation fp_9467 fl_9467.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9467 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9467 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9467.

Lemma collineation_9468 : is_collineation fp_9468 fl_9468.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9468 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9468 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9468.

Lemma collineation_9469 : is_collineation fp_9469 fl_9469.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9469 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9469 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9469.

Lemma collineation_9470 : is_collineation fp_9470 fl_9470.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9470 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9470 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9470.

Lemma collineation_9471 : is_collineation fp_9471 fl_9471.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9471 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9471 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9471.

Lemma collineation_9472 : is_collineation fp_9472 fl_9472.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9472 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9472 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9472.

Lemma collineation_9473 : is_collineation fp_9473 fl_9473.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9473 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9473 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9473.

Lemma collineation_9474 : is_collineation fp_9474 fl_9474.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9474 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9474 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9474.

Lemma collineation_9475 : is_collineation fp_9475 fl_9475.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9475 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9475 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9475.

Lemma collineation_9476 : is_collineation fp_9476 fl_9476.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9476 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9476 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9476.

Lemma collineation_9477 : is_collineation fp_9477 fl_9477.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9477 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9477 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9477.

Lemma collineation_9478 : is_collineation fp_9478 fl_9478.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9478 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9478 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9478.

Lemma collineation_9479 : is_collineation fp_9479 fl_9479.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9479 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9479 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9479.

Lemma collineation_9480 : is_collineation fp_9480 fl_9480.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9480 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9480 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9480.

Lemma collineation_9481 : is_collineation fp_9481 fl_9481.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9481 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9481 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9481.

Lemma collineation_9482 : is_collineation fp_9482 fl_9482.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9482 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9482 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9482.

Lemma collineation_9483 : is_collineation fp_9483 fl_9483.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9483 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9483 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9483.

Lemma collineation_9484 : is_collineation fp_9484 fl_9484.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9484 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9484 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9484.

Lemma collineation_9485 : is_collineation fp_9485 fl_9485.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9485 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9485 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9485.

Lemma collineation_9486 : is_collineation fp_9486 fl_9486.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9486 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9486 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9486.

Lemma collineation_9487 : is_collineation fp_9487 fl_9487.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9487 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9487 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9487.

Lemma collineation_9488 : is_collineation fp_9488 fl_9488.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9488 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9488 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9488.

Lemma collineation_9489 : is_collineation fp_9489 fl_9489.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9489 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9489 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9489.

Lemma collineation_9490 : is_collineation fp_9490 fl_9490.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9490 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9490 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9490.

Lemma collineation_9491 : is_collineation fp_9491 fl_9491.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9491 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9491 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9491.

Lemma collineation_9492 : is_collineation fp_9492 fl_9492.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9492 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9492 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9492.

Lemma collineation_9493 : is_collineation fp_9493 fl_9493.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9493 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9493 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9493.

Lemma collineation_9494 : is_collineation fp_9494 fl_9494.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9494 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9494 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9494.

Lemma collineation_9495 : is_collineation fp_9495 fl_9495.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9495 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9495 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9495.

Lemma collineation_9496 : is_collineation fp_9496 fl_9496.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9496 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9496 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9496.

Lemma collineation_9497 : is_collineation fp_9497 fl_9497.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9497 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9497 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9497.

Lemma collineation_9498 : is_collineation fp_9498 fl_9498.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9498 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9498 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9498.

Lemma collineation_9499 : is_collineation fp_9499 fl_9499.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9499 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9499 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9499.

Lemma collineation_9500 : is_collineation fp_9500 fl_9500.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9500 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9500 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9500.

Lemma collineation_9501 : is_collineation fp_9501 fl_9501.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9501 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9501 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9501.

Lemma collineation_9502 : is_collineation fp_9502 fl_9502.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9502 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9502 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9502.

Lemma collineation_9503 : is_collineation fp_9503 fl_9503.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9503 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9503 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9503.

Lemma collineation_9504 : is_collineation fp_9504 fl_9504.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9504 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9504 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9504.

Lemma collineation_9505 : is_collineation fp_9505 fl_9505.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9505 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9505 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9505.

Lemma collineation_9506 : is_collineation fp_9506 fl_9506.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9506 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9506 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9506.

Lemma collineation_9507 : is_collineation fp_9507 fl_9507.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9507 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9507 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9507.

Lemma collineation_9508 : is_collineation fp_9508 fl_9508.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9508 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9508 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9508.

Lemma collineation_9509 : is_collineation fp_9509 fl_9509.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9509 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9509 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9509.

Lemma collineation_9510 : is_collineation fp_9510 fl_9510.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9510 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9510 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9510.

Lemma collineation_9511 : is_collineation fp_9511 fl_9511.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9511 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9511 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9511.

Lemma collineation_9512 : is_collineation fp_9512 fl_9512.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9512 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9512 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9512.

Lemma collineation_9513 : is_collineation fp_9513 fl_9513.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9513 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9513 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9513.

Lemma collineation_9514 : is_collineation fp_9514 fl_9514.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9514 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9514 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9514.

Lemma collineation_9515 : is_collineation fp_9515 fl_9515.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9515 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9515 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9515.

Lemma collineation_9516 : is_collineation fp_9516 fl_9516.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9516 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9516 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9516.

Lemma collineation_9517 : is_collineation fp_9517 fl_9517.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9517 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9517 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9517.

Lemma collineation_9518 : is_collineation fp_9518 fl_9518.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9518 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9518 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9518.

Lemma collineation_9519 : is_collineation fp_9519 fl_9519.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9519 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9519 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9519.

Lemma collineation_9520 : is_collineation fp_9520 fl_9520.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9520 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9520 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9520.

Lemma collineation_9521 : is_collineation fp_9521 fl_9521.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9521 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9521 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9521.

Lemma collineation_9522 : is_collineation fp_9522 fl_9522.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9522 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9522 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9522.

Lemma collineation_9523 : is_collineation fp_9523 fl_9523.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9523 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9523 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9523.

Lemma collineation_9524 : is_collineation fp_9524 fl_9524.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9524 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9524 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9524.

Lemma collineation_9525 : is_collineation fp_9525 fl_9525.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9525 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9525 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9525.

Lemma collineation_9526 : is_collineation fp_9526 fl_9526.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9526 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9526 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9526.

Lemma collineation_9527 : is_collineation fp_9527 fl_9527.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9527 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9527 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9527.

Lemma collineation_9528 : is_collineation fp_9528 fl_9528.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9528 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9528 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9528.

Lemma collineation_9529 : is_collineation fp_9529 fl_9529.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9529 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9529 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9529.

Lemma collineation_9530 : is_collineation fp_9530 fl_9530.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9530 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9530 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9530.

Lemma collineation_9531 : is_collineation fp_9531 fl_9531.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9531 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9531 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9531.

Lemma collineation_9532 : is_collineation fp_9532 fl_9532.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9532 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9532 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9532.

Lemma collineation_9533 : is_collineation fp_9533 fl_9533.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9533 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9533 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9533.

Lemma collineation_9534 : is_collineation fp_9534 fl_9534.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9534 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9534 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9534.

Lemma collineation_9535 : is_collineation fp_9535 fl_9535.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9535 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9535 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9535.

Lemma collineation_9536 : is_collineation fp_9536 fl_9536.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9536 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9536 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9536.

Lemma collineation_9537 : is_collineation fp_9537 fl_9537.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9537 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9537 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9537.

Lemma collineation_9538 : is_collineation fp_9538 fl_9538.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9538 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9538 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9538.

Lemma collineation_9539 : is_collineation fp_9539 fl_9539.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9539 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9539 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9539.

Lemma collineation_9540 : is_collineation fp_9540 fl_9540.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9540 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9540 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9540.

Lemma collineation_9541 : is_collineation fp_9541 fl_9541.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9541 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9541 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9541.

Lemma collineation_9542 : is_collineation fp_9542 fl_9542.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9542 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9542 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9542.

Lemma collineation_9543 : is_collineation fp_9543 fl_9543.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9543 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9543 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9543.

Lemma collineation_9544 : is_collineation fp_9544 fl_9544.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9544 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9544 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9544.

Lemma collineation_9545 : is_collineation fp_9545 fl_9545.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9545 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9545 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9545.

Lemma collineation_9546 : is_collineation fp_9546 fl_9546.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9546 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9546 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9546.

Lemma collineation_9547 : is_collineation fp_9547 fl_9547.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9547 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9547 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9547.

Lemma collineation_9548 : is_collineation fp_9548 fl_9548.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9548 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9548 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9548.

Lemma collineation_9549 : is_collineation fp_9549 fl_9549.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9549 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9549 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9549.

Lemma collineation_9550 : is_collineation fp_9550 fl_9550.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9550 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9550 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9550.

Lemma collineation_9551 : is_collineation fp_9551 fl_9551.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9551 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9551 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9551.

Lemma collineation_9552 : is_collineation fp_9552 fl_9552.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9552 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9552 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9552.

Lemma collineation_9553 : is_collineation fp_9553 fl_9553.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9553 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9553 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9553.

Lemma collineation_9554 : is_collineation fp_9554 fl_9554.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9554 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9554 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9554.

Lemma collineation_9555 : is_collineation fp_9555 fl_9555.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9555 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9555 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9555.

Lemma collineation_9556 : is_collineation fp_9556 fl_9556.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9556 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9556 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9556.

Lemma collineation_9557 : is_collineation fp_9557 fl_9557.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9557 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9557 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9557.

Lemma collineation_9558 : is_collineation fp_9558 fl_9558.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9558 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9558 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9558.

Lemma collineation_9559 : is_collineation fp_9559 fl_9559.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9559 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9559 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9559.

Lemma collineation_9560 : is_collineation fp_9560 fl_9560.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9560 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9560 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9560.

Lemma collineation_9561 : is_collineation fp_9561 fl_9561.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9561 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9561 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9561.

Lemma collineation_9562 : is_collineation fp_9562 fl_9562.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9562 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9562 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9562.

Lemma collineation_9563 : is_collineation fp_9563 fl_9563.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9563 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9563 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9563.

Lemma collineation_9564 : is_collineation fp_9564 fl_9564.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9564 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9564 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9564.

Lemma collineation_9565 : is_collineation fp_9565 fl_9565.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9565 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9565 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9565.

Lemma collineation_9566 : is_collineation fp_9566 fl_9566.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9566 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9566 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9566.

Lemma collineation_9567 : is_collineation fp_9567 fl_9567.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9567 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9567 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9567.

Lemma collineation_9568 : is_collineation fp_9568 fl_9568.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9568 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9568 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9568.

Lemma collineation_9569 : is_collineation fp_9569 fl_9569.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9569 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9569 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9569.

Lemma collineation_9570 : is_collineation fp_9570 fl_9570.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9570 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9570 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9570.

Lemma collineation_9571 : is_collineation fp_9571 fl_9571.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9571 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9571 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9571.

Lemma collineation_9572 : is_collineation fp_9572 fl_9572.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9572 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9572 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9572.

Lemma collineation_9573 : is_collineation fp_9573 fl_9573.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9573 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9573 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9573.

Lemma collineation_9574 : is_collineation fp_9574 fl_9574.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9574 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9574 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9574.

Lemma collineation_9575 : is_collineation fp_9575 fl_9575.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9575 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9575 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9575.

Lemma collineation_9576 : is_collineation fp_9576 fl_9576.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9576 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9576 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9576.

Lemma collineation_9577 : is_collineation fp_9577 fl_9577.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9577 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9577 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9577.

Lemma collineation_9578 : is_collineation fp_9578 fl_9578.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9578 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9578 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9578.

Lemma collineation_9579 : is_collineation fp_9579 fl_9579.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9579 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9579 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9579.

Lemma collineation_9580 : is_collineation fp_9580 fl_9580.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9580 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9580 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9580.

Lemma collineation_9581 : is_collineation fp_9581 fl_9581.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9581 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9581 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9581.

Lemma collineation_9582 : is_collineation fp_9582 fl_9582.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9582 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9582 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9582.

Lemma collineation_9583 : is_collineation fp_9583 fl_9583.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9583 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9583 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9583.

Lemma collineation_9584 : is_collineation fp_9584 fl_9584.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9584 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9584 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9584.

Lemma collineation_9585 : is_collineation fp_9585 fl_9585.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9585 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9585 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9585.

Lemma collineation_9586 : is_collineation fp_9586 fl_9586.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9586 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9586 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9586.

Lemma collineation_9587 : is_collineation fp_9587 fl_9587.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9587 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9587 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9587.

Lemma collineation_9588 : is_collineation fp_9588 fl_9588.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9588 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9588 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9588.

Lemma collineation_9589 : is_collineation fp_9589 fl_9589.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9589 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9589 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9589.

Lemma collineation_9590 : is_collineation fp_9590 fl_9590.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9590 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9590 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9590.

Lemma collineation_9591 : is_collineation fp_9591 fl_9591.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9591 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9591 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9591.

Lemma collineation_9592 : is_collineation fp_9592 fl_9592.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9592 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9592 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9592.

Lemma collineation_9593 : is_collineation fp_9593 fl_9593.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9593 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9593 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9593.

Lemma collineation_9594 : is_collineation fp_9594 fl_9594.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9594 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9594 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9594.

Lemma collineation_9595 : is_collineation fp_9595 fl_9595.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9595 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9595 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9595.

Lemma collineation_9596 : is_collineation fp_9596 fl_9596.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9596 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9596 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9596.

Lemma collineation_9597 : is_collineation fp_9597 fl_9597.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9597 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9597 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9597.

Lemma collineation_9598 : is_collineation fp_9598 fl_9598.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9598 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9598 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9598.

Lemma collineation_9599 : is_collineation fp_9599 fl_9599.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9599 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9599 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9599.

Lemma collineation_9600 : is_collineation fp_9600 fl_9600.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9600 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9600 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9600.

Lemma collineation_9601 : is_collineation fp_9601 fl_9601.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9601 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9601 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9601.

Lemma collineation_9602 : is_collineation fp_9602 fl_9602.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9602 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9602 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9602.

Lemma collineation_9603 : is_collineation fp_9603 fl_9603.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9603 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9603 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9603.

Lemma collineation_9604 : is_collineation fp_9604 fl_9604.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9604 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9604 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9604.

Lemma collineation_9605 : is_collineation fp_9605 fl_9605.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9605 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9605 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9605.

Lemma collineation_9606 : is_collineation fp_9606 fl_9606.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9606 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9606 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9606.

Lemma collineation_9607 : is_collineation fp_9607 fl_9607.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9607 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9607 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9607.

Lemma collineation_9608 : is_collineation fp_9608 fl_9608.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9608 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9608 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9608.

Lemma collineation_9609 : is_collineation fp_9609 fl_9609.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9609 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9609 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9609.

Lemma collineation_9610 : is_collineation fp_9610 fl_9610.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9610 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9610 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9610.

Lemma collineation_9611 : is_collineation fp_9611 fl_9611.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9611 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9611 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9611.

Lemma collineation_9612 : is_collineation fp_9612 fl_9612.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9612 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9612 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9612.

Lemma collineation_9613 : is_collineation fp_9613 fl_9613.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9613 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9613 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9613.

Lemma collineation_9614 : is_collineation fp_9614 fl_9614.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9614 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9614 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9614.

Lemma collineation_9615 : is_collineation fp_9615 fl_9615.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9615 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9615 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9615.

Lemma collineation_9616 : is_collineation fp_9616 fl_9616.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9616 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9616 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9616.

Lemma collineation_9617 : is_collineation fp_9617 fl_9617.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9617 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9617 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9617.

Lemma collineation_9618 : is_collineation fp_9618 fl_9618.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9618 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9618 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9618.

Lemma collineation_9619 : is_collineation fp_9619 fl_9619.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9619 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9619 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9619.

Lemma collineation_9620 : is_collineation fp_9620 fl_9620.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9620 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9620 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9620.

Lemma collineation_9621 : is_collineation fp_9621 fl_9621.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9621 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9621 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9621.

Lemma collineation_9622 : is_collineation fp_9622 fl_9622.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9622 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9622 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9622.

Lemma collineation_9623 : is_collineation fp_9623 fl_9623.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9623 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9623 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9623.

Lemma collineation_9624 : is_collineation fp_9624 fl_9624.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9624 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9624 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9624.

Lemma collineation_9625 : is_collineation fp_9625 fl_9625.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9625 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9625 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9625.

Lemma collineation_9626 : is_collineation fp_9626 fl_9626.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9626 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9626 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9626.

Lemma collineation_9627 : is_collineation fp_9627 fl_9627.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9627 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9627 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9627.

Lemma collineation_9628 : is_collineation fp_9628 fl_9628.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9628 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9628 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9628.

Lemma collineation_9629 : is_collineation fp_9629 fl_9629.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9629 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9629 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9629.

Lemma collineation_9630 : is_collineation fp_9630 fl_9630.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9630 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9630 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9630.

Lemma collineation_9631 : is_collineation fp_9631 fl_9631.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9631 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9631 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9631.

Lemma collineation_9632 : is_collineation fp_9632 fl_9632.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9632 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9632 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9632.

Lemma collineation_9633 : is_collineation fp_9633 fl_9633.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9633 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9633 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9633.

Lemma collineation_9634 : is_collineation fp_9634 fl_9634.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9634 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9634 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9634.

Lemma collineation_9635 : is_collineation fp_9635 fl_9635.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9635 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9635 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9635.

Lemma collineation_9636 : is_collineation fp_9636 fl_9636.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9636 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9636 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9636.

Lemma collineation_9637 : is_collineation fp_9637 fl_9637.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9637 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9637 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9637.

Lemma collineation_9638 : is_collineation fp_9638 fl_9638.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9638 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9638 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9638.

Lemma collineation_9639 : is_collineation fp_9639 fl_9639.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9639 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9639 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9639.

Lemma collineation_9640 : is_collineation fp_9640 fl_9640.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9640 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9640 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9640.

Lemma collineation_9641 : is_collineation fp_9641 fl_9641.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9641 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9641 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9641.

Lemma collineation_9642 : is_collineation fp_9642 fl_9642.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9642 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9642 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9642.

Lemma collineation_9643 : is_collineation fp_9643 fl_9643.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9643 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9643 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9643.

Lemma collineation_9644 : is_collineation fp_9644 fl_9644.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9644 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9644 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9644.

Lemma collineation_9645 : is_collineation fp_9645 fl_9645.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9645 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9645 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9645.

Lemma collineation_9646 : is_collineation fp_9646 fl_9646.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9646 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9646 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9646.

Lemma collineation_9647 : is_collineation fp_9647 fl_9647.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9647 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9647 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9647.

Lemma collineation_9648 : is_collineation fp_9648 fl_9648.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9648 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9648 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9648.

Lemma collineation_9649 : is_collineation fp_9649 fl_9649.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9649 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9649 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9649.

Lemma collineation_9650 : is_collineation fp_9650 fl_9650.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9650 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9650 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9650.

Lemma collineation_9651 : is_collineation fp_9651 fl_9651.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9651 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9651 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9651.

Lemma collineation_9652 : is_collineation fp_9652 fl_9652.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9652 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9652 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9652.

Lemma collineation_9653 : is_collineation fp_9653 fl_9653.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9653 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9653 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9653.

Lemma collineation_9654 : is_collineation fp_9654 fl_9654.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9654 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9654 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9654.

Lemma collineation_9655 : is_collineation fp_9655 fl_9655.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9655 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9655 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9655.

Lemma collineation_9656 : is_collineation fp_9656 fl_9656.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9656 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9656 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9656.

Lemma collineation_9657 : is_collineation fp_9657 fl_9657.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9657 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9657 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9657.

Lemma collineation_9658 : is_collineation fp_9658 fl_9658.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9658 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9658 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9658.

Lemma collineation_9659 : is_collineation fp_9659 fl_9659.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9659 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9659 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9659.

Lemma collineation_9660 : is_collineation fp_9660 fl_9660.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9660 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9660 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9660.

Lemma collineation_9661 : is_collineation fp_9661 fl_9661.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9661 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9661 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9661.

Lemma collineation_9662 : is_collineation fp_9662 fl_9662.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9662 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9662 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9662.

Lemma collineation_9663 : is_collineation fp_9663 fl_9663.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9663 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9663 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9663.

Lemma collineation_9664 : is_collineation fp_9664 fl_9664.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9664 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9664 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9664.

Lemma collineation_9665 : is_collineation fp_9665 fl_9665.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9665 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9665 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9665.

Lemma collineation_9666 : is_collineation fp_9666 fl_9666.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9666 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9666 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9666.

Lemma collineation_9667 : is_collineation fp_9667 fl_9667.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9667 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9667 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9667.

Lemma collineation_9668 : is_collineation fp_9668 fl_9668.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9668 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9668 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9668.

Lemma collineation_9669 : is_collineation fp_9669 fl_9669.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9669 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9669 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9669.

Lemma collineation_9670 : is_collineation fp_9670 fl_9670.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9670 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9670 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9670.

Lemma collineation_9671 : is_collineation fp_9671 fl_9671.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9671 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9671 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9671.

Lemma collineation_9672 : is_collineation fp_9672 fl_9672.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9672 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9672 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9672.

Lemma collineation_9673 : is_collineation fp_9673 fl_9673.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9673 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9673 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9673.

Lemma collineation_9674 : is_collineation fp_9674 fl_9674.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9674 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9674 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9674.

Lemma collineation_9675 : is_collineation fp_9675 fl_9675.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9675 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9675 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9675.

Lemma collineation_9676 : is_collineation fp_9676 fl_9676.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9676 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9676 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9676.

Lemma collineation_9677 : is_collineation fp_9677 fl_9677.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9677 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9677 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9677.

Lemma collineation_9678 : is_collineation fp_9678 fl_9678.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9678 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9678 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9678.

Lemma collineation_9679 : is_collineation fp_9679 fl_9679.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9679 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9679 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9679.

Lemma collineation_9680 : is_collineation fp_9680 fl_9680.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9680 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9680 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9680.

Lemma collineation_9681 : is_collineation fp_9681 fl_9681.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9681 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9681 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9681.

Lemma collineation_9682 : is_collineation fp_9682 fl_9682.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9682 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9682 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9682.

Lemma collineation_9683 : is_collineation fp_9683 fl_9683.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9683 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9683 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9683.

Lemma collineation_9684 : is_collineation fp_9684 fl_9684.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9684 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9684 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9684.

Lemma collineation_9685 : is_collineation fp_9685 fl_9685.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9685 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9685 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9685.

Lemma collineation_9686 : is_collineation fp_9686 fl_9686.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9686 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9686 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9686.

Lemma collineation_9687 : is_collineation fp_9687 fl_9687.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9687 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9687 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9687.

Lemma collineation_9688 : is_collineation fp_9688 fl_9688.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9688 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9688 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9688.

Lemma collineation_9689 : is_collineation fp_9689 fl_9689.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9689 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9689 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9689.

Lemma collineation_9690 : is_collineation fp_9690 fl_9690.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9690 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9690 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9690.

Lemma collineation_9691 : is_collineation fp_9691 fl_9691.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9691 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9691 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9691.

Lemma collineation_9692 : is_collineation fp_9692 fl_9692.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9692 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9692 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9692.

Lemma collineation_9693 : is_collineation fp_9693 fl_9693.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9693 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9693 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9693.

Lemma collineation_9694 : is_collineation fp_9694 fl_9694.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9694 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9694 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9694.

Lemma collineation_9695 : is_collineation fp_9695 fl_9695.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9695 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9695 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9695.

Lemma collineation_9696 : is_collineation fp_9696 fl_9696.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9696 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9696 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9696.

Lemma collineation_9697 : is_collineation fp_9697 fl_9697.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9697 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9697 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9697.

Lemma collineation_9698 : is_collineation fp_9698 fl_9698.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9698 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9698 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9698.

Lemma collineation_9699 : is_collineation fp_9699 fl_9699.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9699 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9699 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9699.

Lemma collineation_9700 : is_collineation fp_9700 fl_9700.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9700 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9700 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9700.

Lemma collineation_9701 : is_collineation fp_9701 fl_9701.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9701 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9701 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9701.

Lemma collineation_9702 : is_collineation fp_9702 fl_9702.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9702 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9702 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9702.

Lemma collineation_9703 : is_collineation fp_9703 fl_9703.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9703 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9703 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9703.

Lemma collineation_9704 : is_collineation fp_9704 fl_9704.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9704 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9704 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9704.

Lemma collineation_9705 : is_collineation fp_9705 fl_9705.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9705 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9705 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9705.

Lemma collineation_9706 : is_collineation fp_9706 fl_9706.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9706 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9706 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9706.

Lemma collineation_9707 : is_collineation fp_9707 fl_9707.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9707 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9707 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9707.

Lemma collineation_9708 : is_collineation fp_9708 fl_9708.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9708 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9708 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9708.

Lemma collineation_9709 : is_collineation fp_9709 fl_9709.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9709 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9709 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9709.

Lemma collineation_9710 : is_collineation fp_9710 fl_9710.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9710 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9710 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9710.

Lemma collineation_9711 : is_collineation fp_9711 fl_9711.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9711 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9711 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9711.

Lemma collineation_9712 : is_collineation fp_9712 fl_9712.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9712 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9712 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9712.

Lemma collineation_9713 : is_collineation fp_9713 fl_9713.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9713 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9713 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9713.

Lemma collineation_9714 : is_collineation fp_9714 fl_9714.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9714 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9714 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9714.

Lemma collineation_9715 : is_collineation fp_9715 fl_9715.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9715 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9715 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9715.

Lemma collineation_9716 : is_collineation fp_9716 fl_9716.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9716 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9716 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9716.

Lemma collineation_9717 : is_collineation fp_9717 fl_9717.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9717 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9717 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9717.

Lemma collineation_9718 : is_collineation fp_9718 fl_9718.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9718 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9718 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9718.

Lemma collineation_9719 : is_collineation fp_9719 fl_9719.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9719 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9719 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9719.

Lemma collineation_9720 : is_collineation fp_9720 fl_9720.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9720 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9720 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9720.

Lemma collineation_9721 : is_collineation fp_9721 fl_9721.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9721 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9721 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9721.

Lemma collineation_9722 : is_collineation fp_9722 fl_9722.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9722 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9722 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9722.

Lemma collineation_9723 : is_collineation fp_9723 fl_9723.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9723 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9723 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9723.

Lemma collineation_9724 : is_collineation fp_9724 fl_9724.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9724 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9724 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9724.

Lemma collineation_9725 : is_collineation fp_9725 fl_9725.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9725 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9725 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9725.

Lemma collineation_9726 : is_collineation fp_9726 fl_9726.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9726 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9726 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9726.

Lemma collineation_9727 : is_collineation fp_9727 fl_9727.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9727 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9727 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9727.

Lemma collineation_9728 : is_collineation fp_9728 fl_9728.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9728 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9728 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9728.

Lemma collineation_9729 : is_collineation fp_9729 fl_9729.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9729 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9729 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9729.

Lemma collineation_9730 : is_collineation fp_9730 fl_9730.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9730 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9730 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9730.

Lemma collineation_9731 : is_collineation fp_9731 fl_9731.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9731 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9731 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9731.

Lemma collineation_9732 : is_collineation fp_9732 fl_9732.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9732 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9732 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9732.

Lemma collineation_9733 : is_collineation fp_9733 fl_9733.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9733 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9733 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9733.

Lemma collineation_9734 : is_collineation fp_9734 fl_9734.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9734 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9734 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9734.

Lemma collineation_9735 : is_collineation fp_9735 fl_9735.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9735 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9735 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9735.

Lemma collineation_9736 : is_collineation fp_9736 fl_9736.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9736 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9736 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9736.

Lemma collineation_9737 : is_collineation fp_9737 fl_9737.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9737 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9737 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9737.

Lemma collineation_9738 : is_collineation fp_9738 fl_9738.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9738 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9738 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9738.

Lemma collineation_9739 : is_collineation fp_9739 fl_9739.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9739 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9739 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9739.

Lemma collineation_9740 : is_collineation fp_9740 fl_9740.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9740 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9740 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9740.

Lemma collineation_9741 : is_collineation fp_9741 fl_9741.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9741 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9741 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9741.

Lemma collineation_9742 : is_collineation fp_9742 fl_9742.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9742 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9742 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9742.

Lemma collineation_9743 : is_collineation fp_9743 fl_9743.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9743 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9743 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9743.

Lemma collineation_9744 : is_collineation fp_9744 fl_9744.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9744 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9744 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9744.

Lemma collineation_9745 : is_collineation fp_9745 fl_9745.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9745 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9745 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9745.

Lemma collineation_9746 : is_collineation fp_9746 fl_9746.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9746 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9746 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9746.

Lemma collineation_9747 : is_collineation fp_9747 fl_9747.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9747 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9747 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9747.

Lemma collineation_9748 : is_collineation fp_9748 fl_9748.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9748 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9748 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9748.

Lemma collineation_9749 : is_collineation fp_9749 fl_9749.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9749 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9749 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9749.

Lemma collineation_9750 : is_collineation fp_9750 fl_9750.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9750 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9750 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9750.

Lemma collineation_9751 : is_collineation fp_9751 fl_9751.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9751 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9751 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9751.

Lemma collineation_9752 : is_collineation fp_9752 fl_9752.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9752 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9752 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9752.

Lemma collineation_9753 : is_collineation fp_9753 fl_9753.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9753 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9753 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9753.

Lemma collineation_9754 : is_collineation fp_9754 fl_9754.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9754 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9754 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9754.

Lemma collineation_9755 : is_collineation fp_9755 fl_9755.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9755 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9755 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9755.

Lemma collineation_9756 : is_collineation fp_9756 fl_9756.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9756 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9756 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9756.

Lemma collineation_9757 : is_collineation fp_9757 fl_9757.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9757 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9757 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9757.

Lemma collineation_9758 : is_collineation fp_9758 fl_9758.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9758 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9758 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9758.

Lemma collineation_9759 : is_collineation fp_9759 fl_9759.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9759 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9759 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9759.

Lemma collineation_9760 : is_collineation fp_9760 fl_9760.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9760 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9760 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9760.

Lemma collineation_9761 : is_collineation fp_9761 fl_9761.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9761 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9761 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9761.

Lemma collineation_9762 : is_collineation fp_9762 fl_9762.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9762 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9762 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9762.

Lemma collineation_9763 : is_collineation fp_9763 fl_9763.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9763 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9763 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9763.

Lemma collineation_9764 : is_collineation fp_9764 fl_9764.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9764 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9764 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9764.

Lemma collineation_9765 : is_collineation fp_9765 fl_9765.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9765 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9765 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9765.

Lemma collineation_9766 : is_collineation fp_9766 fl_9766.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9766 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9766 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9766.

Lemma collineation_9767 : is_collineation fp_9767 fl_9767.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9767 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9767 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9767.

Lemma collineation_9768 : is_collineation fp_9768 fl_9768.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9768 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9768 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9768.

Lemma collineation_9769 : is_collineation fp_9769 fl_9769.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9769 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9769 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9769.

Lemma collineation_9770 : is_collineation fp_9770 fl_9770.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9770 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9770 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9770.

Lemma collineation_9771 : is_collineation fp_9771 fl_9771.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9771 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9771 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9771.

Lemma collineation_9772 : is_collineation fp_9772 fl_9772.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9772 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9772 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9772.

Lemma collineation_9773 : is_collineation fp_9773 fl_9773.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9773 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9773 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9773.

Lemma collineation_9774 : is_collineation fp_9774 fl_9774.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9774 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9774 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9774.

Lemma collineation_9775 : is_collineation fp_9775 fl_9775.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9775 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9775 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9775.

Lemma collineation_9776 : is_collineation fp_9776 fl_9776.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9776 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9776 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9776.

Lemma collineation_9777 : is_collineation fp_9777 fl_9777.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9777 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9777 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9777.

Lemma collineation_9778 : is_collineation fp_9778 fl_9778.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9778 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9778 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9778.

Lemma collineation_9779 : is_collineation fp_9779 fl_9779.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9779 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9779 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9779.

Lemma collineation_9780 : is_collineation fp_9780 fl_9780.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9780 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9780 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9780.

Lemma collineation_9781 : is_collineation fp_9781 fl_9781.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9781 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9781 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9781.

Lemma collineation_9782 : is_collineation fp_9782 fl_9782.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9782 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9782 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9782.

Lemma collineation_9783 : is_collineation fp_9783 fl_9783.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9783 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9783 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9783.

Lemma collineation_9784 : is_collineation fp_9784 fl_9784.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9784 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9784 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9784.

Lemma collineation_9785 : is_collineation fp_9785 fl_9785.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9785 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9785 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9785.

Lemma collineation_9786 : is_collineation fp_9786 fl_9786.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9786 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9786 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9786.

Lemma collineation_9787 : is_collineation fp_9787 fl_9787.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9787 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9787 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9787.

Lemma collineation_9788 : is_collineation fp_9788 fl_9788.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9788 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9788 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9788.

Lemma collineation_9789 : is_collineation fp_9789 fl_9789.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9789 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9789 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9789.

Lemma collineation_9790 : is_collineation fp_9790 fl_9790.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9790 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9790 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9790.

Lemma collineation_9791 : is_collineation fp_9791 fl_9791.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9791 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9791 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9791.

Lemma collineation_9792 : is_collineation fp_9792 fl_9792.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9792 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9792 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9792.

Lemma collineation_9793 : is_collineation fp_9793 fl_9793.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9793 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9793 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9793.

Lemma collineation_9794 : is_collineation fp_9794 fl_9794.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9794 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9794 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9794.

Lemma collineation_9795 : is_collineation fp_9795 fl_9795.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9795 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9795 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9795.

Lemma collineation_9796 : is_collineation fp_9796 fl_9796.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9796 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9796 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9796.

Lemma collineation_9797 : is_collineation fp_9797 fl_9797.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9797 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9797 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9797.

Lemma collineation_9798 : is_collineation fp_9798 fl_9798.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9798 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9798 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9798.

Lemma collineation_9799 : is_collineation fp_9799 fl_9799.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9799 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9799 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9799.

Lemma collineation_9800 : is_collineation fp_9800 fl_9800.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9800 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9800 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9800.

Lemma collineation_9801 : is_collineation fp_9801 fl_9801.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9801 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9801 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9801.

Lemma collineation_9802 : is_collineation fp_9802 fl_9802.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9802 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9802 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9802.

Lemma collineation_9803 : is_collineation fp_9803 fl_9803.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9803 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9803 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9803.

Lemma collineation_9804 : is_collineation fp_9804 fl_9804.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9804 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9804 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9804.

Lemma collineation_9805 : is_collineation fp_9805 fl_9805.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9805 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9805 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9805.

Lemma collineation_9806 : is_collineation fp_9806 fl_9806.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9806 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9806 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9806.

Lemma collineation_9807 : is_collineation fp_9807 fl_9807.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9807 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9807 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9807.

Lemma collineation_9808 : is_collineation fp_9808 fl_9808.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9808 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9808 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9808.

Lemma collineation_9809 : is_collineation fp_9809 fl_9809.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9809 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9809 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9809.

Lemma collineation_9810 : is_collineation fp_9810 fl_9810.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9810 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9810 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9810.

Lemma collineation_9811 : is_collineation fp_9811 fl_9811.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9811 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9811 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9811.

Lemma collineation_9812 : is_collineation fp_9812 fl_9812.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9812 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9812 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9812.

Lemma collineation_9813 : is_collineation fp_9813 fl_9813.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9813 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9813 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9813.

Lemma collineation_9814 : is_collineation fp_9814 fl_9814.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9814 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9814 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9814.

Lemma collineation_9815 : is_collineation fp_9815 fl_9815.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9815 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9815 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9815.

Lemma collineation_9816 : is_collineation fp_9816 fl_9816.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9816 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9816 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9816.

Lemma collineation_9817 : is_collineation fp_9817 fl_9817.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9817 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9817 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9817.

Lemma collineation_9818 : is_collineation fp_9818 fl_9818.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9818 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9818 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9818.

Lemma collineation_9819 : is_collineation fp_9819 fl_9819.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9819 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9819 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9819.

Lemma collineation_9820 : is_collineation fp_9820 fl_9820.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9820 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9820 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9820.

Lemma collineation_9821 : is_collineation fp_9821 fl_9821.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9821 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9821 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9821.

Lemma collineation_9822 : is_collineation fp_9822 fl_9822.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9822 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9822 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9822.

Lemma collineation_9823 : is_collineation fp_9823 fl_9823.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9823 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9823 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9823.

Lemma collineation_9824 : is_collineation fp_9824 fl_9824.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9824 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9824 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9824.

Lemma collineation_9825 : is_collineation fp_9825 fl_9825.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9825 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9825 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9825.

Lemma collineation_9826 : is_collineation fp_9826 fl_9826.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9826 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9826 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9826.

Lemma collineation_9827 : is_collineation fp_9827 fl_9827.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9827 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9827 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9827.

Lemma collineation_9828 : is_collineation fp_9828 fl_9828.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9828 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9828 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9828.

Lemma collineation_9829 : is_collineation fp_9829 fl_9829.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9829 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9829 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9829.

Lemma collineation_9830 : is_collineation fp_9830 fl_9830.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9830 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9830 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9830.

Lemma collineation_9831 : is_collineation fp_9831 fl_9831.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9831 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9831 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9831.

Lemma collineation_9832 : is_collineation fp_9832 fl_9832.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9832 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9832 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9832.

Lemma collineation_9833 : is_collineation fp_9833 fl_9833.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9833 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9833 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9833.

Lemma collineation_9834 : is_collineation fp_9834 fl_9834.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9834 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9834 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9834.

Lemma collineation_9835 : is_collineation fp_9835 fl_9835.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9835 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9835 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9835.

Lemma collineation_9836 : is_collineation fp_9836 fl_9836.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9836 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9836 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9836.

Lemma collineation_9837 : is_collineation fp_9837 fl_9837.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9837 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9837 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9837.

Lemma collineation_9838 : is_collineation fp_9838 fl_9838.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9838 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9838 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9838.

Lemma collineation_9839 : is_collineation fp_9839 fl_9839.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9839 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9839 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9839.

Lemma collineation_9840 : is_collineation fp_9840 fl_9840.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9840 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9840 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9840.

Lemma collineation_9841 : is_collineation fp_9841 fl_9841.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9841 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9841 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9841.

Lemma collineation_9842 : is_collineation fp_9842 fl_9842.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9842 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9842 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9842.

Lemma collineation_9843 : is_collineation fp_9843 fl_9843.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9843 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9843 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9843.

Lemma collineation_9844 : is_collineation fp_9844 fl_9844.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9844 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9844 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9844.

Lemma collineation_9845 : is_collineation fp_9845 fl_9845.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9845 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9845 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9845.

Lemma collineation_9846 : is_collineation fp_9846 fl_9846.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9846 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9846 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9846.

Lemma collineation_9847 : is_collineation fp_9847 fl_9847.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9847 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9847 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9847.

Lemma collineation_9848 : is_collineation fp_9848 fl_9848.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9848 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9848 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9848.

Lemma collineation_9849 : is_collineation fp_9849 fl_9849.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9849 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9849 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9849.

Lemma collineation_9850 : is_collineation fp_9850 fl_9850.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9850 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9850 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9850.

Lemma collineation_9851 : is_collineation fp_9851 fl_9851.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9851 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9851 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9851.

Lemma collineation_9852 : is_collineation fp_9852 fl_9852.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9852 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9852 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9852.

Lemma collineation_9853 : is_collineation fp_9853 fl_9853.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9853 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9853 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9853.

Lemma collineation_9854 : is_collineation fp_9854 fl_9854.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9854 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9854 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9854.

Lemma collineation_9855 : is_collineation fp_9855 fl_9855.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9855 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9855 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9855.

Lemma collineation_9856 : is_collineation fp_9856 fl_9856.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9856 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9856 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9856.

Lemma collineation_9857 : is_collineation fp_9857 fl_9857.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9857 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9857 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9857.

Lemma collineation_9858 : is_collineation fp_9858 fl_9858.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9858 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9858 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9858.

Lemma collineation_9859 : is_collineation fp_9859 fl_9859.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9859 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9859 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9859.

Lemma collineation_9860 : is_collineation fp_9860 fl_9860.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9860 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9860 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9860.

Lemma collineation_9861 : is_collineation fp_9861 fl_9861.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9861 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9861 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9861.

Lemma collineation_9862 : is_collineation fp_9862 fl_9862.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9862 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9862 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9862.

Lemma collineation_9863 : is_collineation fp_9863 fl_9863.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9863 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9863 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9863.

Lemma collineation_9864 : is_collineation fp_9864 fl_9864.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9864 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9864 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9864.

Lemma collineation_9865 : is_collineation fp_9865 fl_9865.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9865 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9865 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9865.

Lemma collineation_9866 : is_collineation fp_9866 fl_9866.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9866 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9866 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9866.

Lemma collineation_9867 : is_collineation fp_9867 fl_9867.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9867 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9867 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9867.

Lemma collineation_9868 : is_collineation fp_9868 fl_9868.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9868 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9868 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9868.

Lemma collineation_9869 : is_collineation fp_9869 fl_9869.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9869 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9869 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9869.

Lemma collineation_9870 : is_collineation fp_9870 fl_9870.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9870 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9870 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9870.

Lemma collineation_9871 : is_collineation fp_9871 fl_9871.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9871 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9871 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9871.

Lemma collineation_9872 : is_collineation fp_9872 fl_9872.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9872 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9872 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9872.

Lemma collineation_9873 : is_collineation fp_9873 fl_9873.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9873 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9873 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9873.

Lemma collineation_9874 : is_collineation fp_9874 fl_9874.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9874 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9874 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9874.

Lemma collineation_9875 : is_collineation fp_9875 fl_9875.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9875 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9875 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9875.

Lemma collineation_9876 : is_collineation fp_9876 fl_9876.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9876 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9876 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9876.

Lemma collineation_9877 : is_collineation fp_9877 fl_9877.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9877 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9877 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9877.

Lemma collineation_9878 : is_collineation fp_9878 fl_9878.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9878 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9878 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9878.

Lemma collineation_9879 : is_collineation fp_9879 fl_9879.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9879 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9879 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9879.

Lemma collineation_9880 : is_collineation fp_9880 fl_9880.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9880 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9880 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9880.

Lemma collineation_9881 : is_collineation fp_9881 fl_9881.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9881 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9881 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9881.

Lemma collineation_9882 : is_collineation fp_9882 fl_9882.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9882 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9882 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9882.

Lemma collineation_9883 : is_collineation fp_9883 fl_9883.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9883 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9883 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9883.

Lemma collineation_9884 : is_collineation fp_9884 fl_9884.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9884 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9884 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9884.

Lemma collineation_9885 : is_collineation fp_9885 fl_9885.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9885 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9885 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9885.

Lemma collineation_9886 : is_collineation fp_9886 fl_9886.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9886 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9886 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9886.

Lemma collineation_9887 : is_collineation fp_9887 fl_9887.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9887 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9887 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9887.

Lemma collineation_9888 : is_collineation fp_9888 fl_9888.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9888 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9888 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9888.

Lemma collineation_9889 : is_collineation fp_9889 fl_9889.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9889 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9889 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9889.

Lemma collineation_9890 : is_collineation fp_9890 fl_9890.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9890 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9890 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9890.

Lemma collineation_9891 : is_collineation fp_9891 fl_9891.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9891 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9891 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9891.

Lemma collineation_9892 : is_collineation fp_9892 fl_9892.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9892 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9892 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9892.

Lemma collineation_9893 : is_collineation fp_9893 fl_9893.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9893 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9893 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9893.

Lemma collineation_9894 : is_collineation fp_9894 fl_9894.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9894 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9894 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9894.

Lemma collineation_9895 : is_collineation fp_9895 fl_9895.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9895 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9895 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9895.

Lemma collineation_9896 : is_collineation fp_9896 fl_9896.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9896 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9896 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9896.

Lemma collineation_9897 : is_collineation fp_9897 fl_9897.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9897 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9897 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9897.

Lemma collineation_9898 : is_collineation fp_9898 fl_9898.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9898 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9898 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9898.

Lemma collineation_9899 : is_collineation fp_9899 fl_9899.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9899 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9899 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9899.

Lemma collineation_9900 : is_collineation fp_9900 fl_9900.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9900 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9900 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9900.

Lemma collineation_9901 : is_collineation fp_9901 fl_9901.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9901 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9901 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9901.

Lemma collineation_9902 : is_collineation fp_9902 fl_9902.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9902 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9902 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9902.

Lemma collineation_9903 : is_collineation fp_9903 fl_9903.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9903 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9903 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9903.

Lemma collineation_9904 : is_collineation fp_9904 fl_9904.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9904 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9904 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9904.

Lemma collineation_9905 : is_collineation fp_9905 fl_9905.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9905 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9905 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9905.

Lemma collineation_9906 : is_collineation fp_9906 fl_9906.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9906 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9906 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9906.

Lemma collineation_9907 : is_collineation fp_9907 fl_9907.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9907 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9907 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9907.

Lemma collineation_9908 : is_collineation fp_9908 fl_9908.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9908 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9908 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9908.

Lemma collineation_9909 : is_collineation fp_9909 fl_9909.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9909 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9909 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9909.

Lemma collineation_9910 : is_collineation fp_9910 fl_9910.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9910 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9910 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9910.

Lemma collineation_9911 : is_collineation fp_9911 fl_9911.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9911 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9911 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9911.

Lemma collineation_9912 : is_collineation fp_9912 fl_9912.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9912 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9912 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9912.

Lemma collineation_9913 : is_collineation fp_9913 fl_9913.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9913 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9913 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9913.

Lemma collineation_9914 : is_collineation fp_9914 fl_9914.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9914 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9914 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9914.

Lemma collineation_9915 : is_collineation fp_9915 fl_9915.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9915 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9915 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9915.

Lemma collineation_9916 : is_collineation fp_9916 fl_9916.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9916 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9916 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9916.

Lemma collineation_9917 : is_collineation fp_9917 fl_9917.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9917 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9917 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9917.

Lemma collineation_9918 : is_collineation fp_9918 fl_9918.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9918 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9918 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9918.

Lemma collineation_9919 : is_collineation fp_9919 fl_9919.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9919 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9919 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9919.

Lemma collineation_9920 : is_collineation fp_9920 fl_9920.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9920 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9920 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9920.

Lemma collineation_9921 : is_collineation fp_9921 fl_9921.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9921 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9921 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9921.

Lemma collineation_9922 : is_collineation fp_9922 fl_9922.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9922 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9922 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9922.

Lemma collineation_9923 : is_collineation fp_9923 fl_9923.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9923 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9923 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9923.

Lemma collineation_9924 : is_collineation fp_9924 fl_9924.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9924 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9924 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9924.

Lemma collineation_9925 : is_collineation fp_9925 fl_9925.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9925 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9925 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9925.

Lemma collineation_9926 : is_collineation fp_9926 fl_9926.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9926 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9926 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9926.

Lemma collineation_9927 : is_collineation fp_9927 fl_9927.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9927 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9927 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9927.

Lemma collineation_9928 : is_collineation fp_9928 fl_9928.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9928 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9928 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9928.

Lemma collineation_9929 : is_collineation fp_9929 fl_9929.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9929 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9929 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9929.

Lemma collineation_9930 : is_collineation fp_9930 fl_9930.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9930 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9930 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9930.

Lemma collineation_9931 : is_collineation fp_9931 fl_9931.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9931 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9931 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9931.

Lemma collineation_9932 : is_collineation fp_9932 fl_9932.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9932 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9932 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9932.

Lemma collineation_9933 : is_collineation fp_9933 fl_9933.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9933 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9933 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9933.

Lemma collineation_9934 : is_collineation fp_9934 fl_9934.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9934 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9934 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9934.

Lemma collineation_9935 : is_collineation fp_9935 fl_9935.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9935 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9935 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9935.

Lemma collineation_9936 : is_collineation fp_9936 fl_9936.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9936 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9936 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9936.

Lemma collineation_9937 : is_collineation fp_9937 fl_9937.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9937 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9937 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9937.

Lemma collineation_9938 : is_collineation fp_9938 fl_9938.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9938 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9938 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9938.

Lemma collineation_9939 : is_collineation fp_9939 fl_9939.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9939 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9939 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9939.

Lemma collineation_9940 : is_collineation fp_9940 fl_9940.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9940 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9940 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9940.

Lemma collineation_9941 : is_collineation fp_9941 fl_9941.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9941 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9941 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9941.

Lemma collineation_9942 : is_collineation fp_9942 fl_9942.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9942 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9942 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9942.

Lemma collineation_9943 : is_collineation fp_9943 fl_9943.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9943 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9943 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9943.

Lemma collineation_9944 : is_collineation fp_9944 fl_9944.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9944 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9944 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9944.

Lemma collineation_9945 : is_collineation fp_9945 fl_9945.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9945 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9945 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9945.

Lemma collineation_9946 : is_collineation fp_9946 fl_9946.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9946 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9946 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9946.

Lemma collineation_9947 : is_collineation fp_9947 fl_9947.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9947 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9947 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9947.

Lemma collineation_9948 : is_collineation fp_9948 fl_9948.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9948 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9948 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9948.

Lemma collineation_9949 : is_collineation fp_9949 fl_9949.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9949 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9949 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9949.

Lemma collineation_9950 : is_collineation fp_9950 fl_9950.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9950 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9950 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9950.

Lemma collineation_9951 : is_collineation fp_9951 fl_9951.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9951 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9951 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9951.

Lemma collineation_9952 : is_collineation fp_9952 fl_9952.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9952 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9952 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9952.

Lemma collineation_9953 : is_collineation fp_9953 fl_9953.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9953 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9953 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9953.

Lemma collineation_9954 : is_collineation fp_9954 fl_9954.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9954 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9954 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9954.

Lemma collineation_9955 : is_collineation fp_9955 fl_9955.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9955 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9955 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9955.

Lemma collineation_9956 : is_collineation fp_9956 fl_9956.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9956 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9956 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9956.

Lemma collineation_9957 : is_collineation fp_9957 fl_9957.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9957 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9957 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9957.

Lemma collineation_9958 : is_collineation fp_9958 fl_9958.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9958 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9958 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9958.

Lemma collineation_9959 : is_collineation fp_9959 fl_9959.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9959 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9959 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9959.

Lemma collineation_9960 : is_collineation fp_9960 fl_9960.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9960 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9960 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9960.

Lemma collineation_9961 : is_collineation fp_9961 fl_9961.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9961 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9961 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9961.

Lemma collineation_9962 : is_collineation fp_9962 fl_9962.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9962 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9962 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9962.

Lemma collineation_9963 : is_collineation fp_9963 fl_9963.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9963 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9963 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9963.

Lemma collineation_9964 : is_collineation fp_9964 fl_9964.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9964 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9964 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9964.

Lemma collineation_9965 : is_collineation fp_9965 fl_9965.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9965 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9965 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9965.

Lemma collineation_9966 : is_collineation fp_9966 fl_9966.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9966 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9966 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9966.

Lemma collineation_9967 : is_collineation fp_9967 fl_9967.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9967 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9967 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9967.

Lemma collineation_9968 : is_collineation fp_9968 fl_9968.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9968 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9968 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9968.

Lemma collineation_9969 : is_collineation fp_9969 fl_9969.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9969 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9969 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9969.

Lemma collineation_9970 : is_collineation fp_9970 fl_9970.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9970 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9970 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9970.

Lemma collineation_9971 : is_collineation fp_9971 fl_9971.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9971 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9971 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9971.

Lemma collineation_9972 : is_collineation fp_9972 fl_9972.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9972 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9972 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9972.

Lemma collineation_9973 : is_collineation fp_9973 fl_9973.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9973 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9973 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9973.

Lemma collineation_9974 : is_collineation fp_9974 fl_9974.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9974 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9974 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9974.

Lemma collineation_9975 : is_collineation fp_9975 fl_9975.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9975 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9975 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9975.

Lemma collineation_9976 : is_collineation fp_9976 fl_9976.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9976 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9976 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9976.

Lemma collineation_9977 : is_collineation fp_9977 fl_9977.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9977 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9977 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9977.

Lemma collineation_9978 : is_collineation fp_9978 fl_9978.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9978 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9978 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9978.

Lemma collineation_9979 : is_collineation fp_9979 fl_9979.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9979 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9979 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9979.

Lemma collineation_9980 : is_collineation fp_9980 fl_9980.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9980 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9980 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9980.

Lemma collineation_9981 : is_collineation fp_9981 fl_9981.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9981 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9981 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9981.

Lemma collineation_9982 : is_collineation fp_9982 fl_9982.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9982 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9982 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9982.

Lemma collineation_9983 : is_collineation fp_9983 fl_9983.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9983 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9983 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9983.

Lemma collineation_9984 : is_collineation fp_9984 fl_9984.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9984 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9984 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9984.

Lemma collineation_9985 : is_collineation fp_9985 fl_9985.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9985 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9985 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9985.

Lemma collineation_9986 : is_collineation fp_9986 fl_9986.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9986 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9986 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9986.

Lemma collineation_9987 : is_collineation fp_9987 fl_9987.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9987 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9987 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9987.

Lemma collineation_9988 : is_collineation fp_9988 fl_9988.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9988 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9988 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9988.

Lemma collineation_9989 : is_collineation fp_9989 fl_9989.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9989 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9989 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9989.

Lemma collineation_9990 : is_collineation fp_9990 fl_9990.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9990 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9990 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9990.

Lemma collineation_9991 : is_collineation fp_9991 fl_9991.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9991 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9991 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9991.

Lemma collineation_9992 : is_collineation fp_9992 fl_9992.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9992 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9992 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9992.

Lemma collineation_9993 : is_collineation fp_9993 fl_9993.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9993 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9993 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9993.

Lemma collineation_9994 : is_collineation fp_9994 fl_9994.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9994 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9994 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9994.

Lemma collineation_9995 : is_collineation fp_9995 fl_9995.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9995 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9995 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9995.

Lemma collineation_9996 : is_collineation fp_9996 fl_9996.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9996 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9996 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9996.

Lemma collineation_9997 : is_collineation fp_9997 fl_9997.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9997 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9997 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9997.

Lemma collineation_9998 : is_collineation fp_9998 fl_9998.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9998 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9998 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9998.

Lemma collineation_9999 : is_collineation fp_9999 fl_9999.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_9999 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_9999 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_9999.

Lemma collineation_10000 : is_collineation fp_10000 fl_10000.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10000 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10000 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10000.

Lemma collineation_10001 : is_collineation fp_10001 fl_10001.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10001 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10001 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10001.

Lemma collineation_10002 : is_collineation fp_10002 fl_10002.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10002 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10002 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10002.

Lemma collineation_10003 : is_collineation fp_10003 fl_10003.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10003 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10003 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10003.

Lemma collineation_10004 : is_collineation fp_10004 fl_10004.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10004 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10004 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10004.

Lemma collineation_10005 : is_collineation fp_10005 fl_10005.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10005 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10005 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10005.

Lemma collineation_10006 : is_collineation fp_10006 fl_10006.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10006 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10006 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10006.

Lemma collineation_10007 : is_collineation fp_10007 fl_10007.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10007 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10007 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10007.

Lemma collineation_10008 : is_collineation fp_10008 fl_10008.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10008 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10008 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10008.

Lemma collineation_10009 : is_collineation fp_10009 fl_10009.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10009 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10009 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10009.

Lemma collineation_10010 : is_collineation fp_10010 fl_10010.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10010 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10010 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10010.

Lemma collineation_10011 : is_collineation fp_10011 fl_10011.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10011 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10011 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10011.

Lemma collineation_10012 : is_collineation fp_10012 fl_10012.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10012 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10012 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10012.

Lemma collineation_10013 : is_collineation fp_10013 fl_10013.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10013 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10013 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10013.

Lemma collineation_10014 : is_collineation fp_10014 fl_10014.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10014 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10014 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10014.

Lemma collineation_10015 : is_collineation fp_10015 fl_10015.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10015 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10015 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10015.

Lemma collineation_10016 : is_collineation fp_10016 fl_10016.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10016 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10016 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10016.

Lemma collineation_10017 : is_collineation fp_10017 fl_10017.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10017 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10017 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10017.

Lemma collineation_10018 : is_collineation fp_10018 fl_10018.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10018 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10018 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10018.

Lemma collineation_10019 : is_collineation fp_10019 fl_10019.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10019 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10019 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10019.

Lemma collineation_10020 : is_collineation fp_10020 fl_10020.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10020 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10020 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10020.

Lemma collineation_10021 : is_collineation fp_10021 fl_10021.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10021 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10021 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10021.

Lemma collineation_10022 : is_collineation fp_10022 fl_10022.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10022 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10022 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10022.

Lemma collineation_10023 : is_collineation fp_10023 fl_10023.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10023 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10023 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10023.

Lemma collineation_10024 : is_collineation fp_10024 fl_10024.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10024 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10024 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10024.

Lemma collineation_10025 : is_collineation fp_10025 fl_10025.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10025 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10025 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10025.

Lemma collineation_10026 : is_collineation fp_10026 fl_10026.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10026 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10026 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10026.

Lemma collineation_10027 : is_collineation fp_10027 fl_10027.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10027 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10027 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10027.

Lemma collineation_10028 : is_collineation fp_10028 fl_10028.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10028 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10028 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10028.

Lemma collineation_10029 : is_collineation fp_10029 fl_10029.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10029 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10029 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10029.

Lemma collineation_10030 : is_collineation fp_10030 fl_10030.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10030 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10030 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10030.

Lemma collineation_10031 : is_collineation fp_10031 fl_10031.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10031 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10031 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10031.

Lemma collineation_10032 : is_collineation fp_10032 fl_10032.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10032 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10032 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10032.

Lemma collineation_10033 : is_collineation fp_10033 fl_10033.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10033 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10033 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10033.

Lemma collineation_10034 : is_collineation fp_10034 fl_10034.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10034 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10034 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10034.

Lemma collineation_10035 : is_collineation fp_10035 fl_10035.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10035 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10035 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10035.

Lemma collineation_10036 : is_collineation fp_10036 fl_10036.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10036 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10036 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10036.

Lemma collineation_10037 : is_collineation fp_10037 fl_10037.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10037 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10037 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10037.

Lemma collineation_10038 : is_collineation fp_10038 fl_10038.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10038 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10038 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10038.

Lemma collineation_10039 : is_collineation fp_10039 fl_10039.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10039 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10039 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10039.

Lemma collineation_10040 : is_collineation fp_10040 fl_10040.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10040 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10040 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10040.

Lemma collineation_10041 : is_collineation fp_10041 fl_10041.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10041 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10041 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10041.

Lemma collineation_10042 : is_collineation fp_10042 fl_10042.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10042 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10042 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10042.

Lemma collineation_10043 : is_collineation fp_10043 fl_10043.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10043 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10043 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10043.

Lemma collineation_10044 : is_collineation fp_10044 fl_10044.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10044 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10044 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10044.

Lemma collineation_10045 : is_collineation fp_10045 fl_10045.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10045 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10045 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10045.

Lemma collineation_10046 : is_collineation fp_10046 fl_10046.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10046 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10046 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10046.

Lemma collineation_10047 : is_collineation fp_10047 fl_10047.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10047 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10047 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10047.

Lemma collineation_10048 : is_collineation fp_10048 fl_10048.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10048 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10048 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10048.

Lemma collineation_10049 : is_collineation fp_10049 fl_10049.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10049 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10049 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10049.

Lemma collineation_10050 : is_collineation fp_10050 fl_10050.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10050 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10050 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10050.

Lemma collineation_10051 : is_collineation fp_10051 fl_10051.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10051 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10051 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10051.

Lemma collineation_10052 : is_collineation fp_10052 fl_10052.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10052 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10052 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10052.

Lemma collineation_10053 : is_collineation fp_10053 fl_10053.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10053 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10053 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10053.

Lemma collineation_10054 : is_collineation fp_10054 fl_10054.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10054 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10054 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10054.

Lemma collineation_10055 : is_collineation fp_10055 fl_10055.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10055 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10055 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10055.

Lemma collineation_10056 : is_collineation fp_10056 fl_10056.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10056 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10056 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10056.

Lemma collineation_10057 : is_collineation fp_10057 fl_10057.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10057 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10057 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10057.

Lemma collineation_10058 : is_collineation fp_10058 fl_10058.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10058 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10058 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10058.

Lemma collineation_10059 : is_collineation fp_10059 fl_10059.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10059 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10059 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10059.

Lemma collineation_10060 : is_collineation fp_10060 fl_10060.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10060 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10060 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10060.

Lemma collineation_10061 : is_collineation fp_10061 fl_10061.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10061 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10061 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10061.

Lemma collineation_10062 : is_collineation fp_10062 fl_10062.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10062 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10062 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10062.

Lemma collineation_10063 : is_collineation fp_10063 fl_10063.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10063 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10063 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10063.

Lemma collineation_10064 : is_collineation fp_10064 fl_10064.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10064 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10064 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10064.

Lemma collineation_10065 : is_collineation fp_10065 fl_10065.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10065 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10065 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10065.

Lemma collineation_10066 : is_collineation fp_10066 fl_10066.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10066 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10066 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10066.

Lemma collineation_10067 : is_collineation fp_10067 fl_10067.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10067 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10067 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10067.

Lemma collineation_10068 : is_collineation fp_10068 fl_10068.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10068 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10068 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10068.

Lemma collineation_10069 : is_collineation fp_10069 fl_10069.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10069 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10069 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10069.

Lemma collineation_10070 : is_collineation fp_10070 fl_10070.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10070 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10070 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10070.

Lemma collineation_10071 : is_collineation fp_10071 fl_10071.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10071 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10071 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10071.

Lemma collineation_10072 : is_collineation fp_10072 fl_10072.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10072 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10072 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10072.

Lemma collineation_10073 : is_collineation fp_10073 fl_10073.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10073 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10073 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10073.

Lemma collineation_10074 : is_collineation fp_10074 fl_10074.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10074 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10074 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10074.

Lemma collineation_10075 : is_collineation fp_10075 fl_10075.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10075 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10075 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10075.

Lemma collineation_10076 : is_collineation fp_10076 fl_10076.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10076 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10076 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10076.

Lemma collineation_10077 : is_collineation fp_10077 fl_10077.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10077 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10077 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10077.

Lemma collineation_10078 : is_collineation fp_10078 fl_10078.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10078 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10078 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10078.

Lemma collineation_10079 : is_collineation fp_10079 fl_10079.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10079 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10079 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10079.

Lemma collineation_10080 : is_collineation fp_10080 fl_10080.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10080 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10080 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10080.

Lemma collineation_10081 : is_collineation fp_10081 fl_10081.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10081 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10081 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10081.

Lemma collineation_10082 : is_collineation fp_10082 fl_10082.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10082 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10082 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10082.

Lemma collineation_10083 : is_collineation fp_10083 fl_10083.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10083 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10083 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10083.

Lemma collineation_10084 : is_collineation fp_10084 fl_10084.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10084 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10084 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10084.

Lemma collineation_10085 : is_collineation fp_10085 fl_10085.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10085 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10085 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10085.

Lemma collineation_10086 : is_collineation fp_10086 fl_10086.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10086 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10086 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10086.

Lemma collineation_10087 : is_collineation fp_10087 fl_10087.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10087 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10087 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10087.

Lemma collineation_10088 : is_collineation fp_10088 fl_10088.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10088 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10088 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10088.

Lemma collineation_10089 : is_collineation fp_10089 fl_10089.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10089 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10089 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10089.

Lemma collineation_10090 : is_collineation fp_10090 fl_10090.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10090 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10090 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10090.

Lemma collineation_10091 : is_collineation fp_10091 fl_10091.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10091 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10091 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10091.

Lemma collineation_10092 : is_collineation fp_10092 fl_10092.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10092 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10092 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10092.

Lemma collineation_10093 : is_collineation fp_10093 fl_10093.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10093 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10093 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10093.

Lemma collineation_10094 : is_collineation fp_10094 fl_10094.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10094 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10094 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10094.

Lemma collineation_10095 : is_collineation fp_10095 fl_10095.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10095 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10095 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10095.

Lemma collineation_10096 : is_collineation fp_10096 fl_10096.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10096 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10096 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10096.

Lemma collineation_10097 : is_collineation fp_10097 fl_10097.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10097 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10097 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10097.

Lemma collineation_10098 : is_collineation fp_10098 fl_10098.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10098 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10098 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10098.

Lemma collineation_10099 : is_collineation fp_10099 fl_10099.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10099 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10099 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10099.

Lemma collineation_10100 : is_collineation fp_10100 fl_10100.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10100 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10100 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10100.

Lemma collineation_10101 : is_collineation fp_10101 fl_10101.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10101 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10101 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10101.

Lemma collineation_10102 : is_collineation fp_10102 fl_10102.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10102 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10102 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10102.

Lemma collineation_10103 : is_collineation fp_10103 fl_10103.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10103 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10103 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10103.

Lemma collineation_10104 : is_collineation fp_10104 fl_10104.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10104 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10104 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10104.

Lemma collineation_10105 : is_collineation fp_10105 fl_10105.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10105 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10105 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10105.

Lemma collineation_10106 : is_collineation fp_10106 fl_10106.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10106 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10106 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10106.

Lemma collineation_10107 : is_collineation fp_10107 fl_10107.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10107 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10107 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10107.

Lemma collineation_10108 : is_collineation fp_10108 fl_10108.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10108 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10108 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10108.

Lemma collineation_10109 : is_collineation fp_10109 fl_10109.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10109 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10109 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10109.

Lemma collineation_10110 : is_collineation fp_10110 fl_10110.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10110 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10110 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10110.

Lemma collineation_10111 : is_collineation fp_10111 fl_10111.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10111 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10111 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10111.

Lemma collineation_10112 : is_collineation fp_10112 fl_10112.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10112 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10112 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10112.

Lemma collineation_10113 : is_collineation fp_10113 fl_10113.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10113 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10113 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10113.

Lemma collineation_10114 : is_collineation fp_10114 fl_10114.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10114 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10114 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10114.

Lemma collineation_10115 : is_collineation fp_10115 fl_10115.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10115 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10115 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10115.

Lemma collineation_10116 : is_collineation fp_10116 fl_10116.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10116 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10116 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10116.

Lemma collineation_10117 : is_collineation fp_10117 fl_10117.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10117 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10117 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10117.

Lemma collineation_10118 : is_collineation fp_10118 fl_10118.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10118 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10118 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10118.

Lemma collineation_10119 : is_collineation fp_10119 fl_10119.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10119 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10119 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10119.

Lemma collineation_10120 : is_collineation fp_10120 fl_10120.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10120 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10120 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10120.

Lemma collineation_10121 : is_collineation fp_10121 fl_10121.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10121 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10121 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10121.

Lemma collineation_10122 : is_collineation fp_10122 fl_10122.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10122 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10122 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10122.

Lemma collineation_10123 : is_collineation fp_10123 fl_10123.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10123 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10123 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10123.

Lemma collineation_10124 : is_collineation fp_10124 fl_10124.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10124 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10124 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10124.

Lemma collineation_10125 : is_collineation fp_10125 fl_10125.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10125 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10125 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10125.

Lemma collineation_10126 : is_collineation fp_10126 fl_10126.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10126 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10126 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10126.

Lemma collineation_10127 : is_collineation fp_10127 fl_10127.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10127 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10127 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10127.

Lemma collineation_10128 : is_collineation fp_10128 fl_10128.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10128 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10128 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10128.

Lemma collineation_10129 : is_collineation fp_10129 fl_10129.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10129 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10129 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10129.

Lemma collineation_10130 : is_collineation fp_10130 fl_10130.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10130 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10130 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10130.

Lemma collineation_10131 : is_collineation fp_10131 fl_10131.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10131 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10131 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10131.

Lemma collineation_10132 : is_collineation fp_10132 fl_10132.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10132 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10132 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10132.

Lemma collineation_10133 : is_collineation fp_10133 fl_10133.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10133 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10133 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10133.

Lemma collineation_10134 : is_collineation fp_10134 fl_10134.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10134 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10134 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10134.

Lemma collineation_10135 : is_collineation fp_10135 fl_10135.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10135 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10135 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10135.

Lemma collineation_10136 : is_collineation fp_10136 fl_10136.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10136 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10136 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10136.

Lemma collineation_10137 : is_collineation fp_10137 fl_10137.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10137 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10137 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10137.

Lemma collineation_10138 : is_collineation fp_10138 fl_10138.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10138 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10138 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10138.

Lemma collineation_10139 : is_collineation fp_10139 fl_10139.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10139 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10139 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10139.

Lemma collineation_10140 : is_collineation fp_10140 fl_10140.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10140 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10140 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10140.

Lemma collineation_10141 : is_collineation fp_10141 fl_10141.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10141 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10141 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10141.

Lemma collineation_10142 : is_collineation fp_10142 fl_10142.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10142 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10142 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10142.

Lemma collineation_10143 : is_collineation fp_10143 fl_10143.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10143 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10143 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10143.

Lemma collineation_10144 : is_collineation fp_10144 fl_10144.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10144 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10144 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10144.

Lemma collineation_10145 : is_collineation fp_10145 fl_10145.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10145 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10145 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10145.

Lemma collineation_10146 : is_collineation fp_10146 fl_10146.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10146 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10146 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10146.

Lemma collineation_10147 : is_collineation fp_10147 fl_10147.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10147 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10147 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10147.

Lemma collineation_10148 : is_collineation fp_10148 fl_10148.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10148 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10148 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10148.

Lemma collineation_10149 : is_collineation fp_10149 fl_10149.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10149 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10149 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10149.

Lemma collineation_10150 : is_collineation fp_10150 fl_10150.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10150 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10150 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10150.

Lemma collineation_10151 : is_collineation fp_10151 fl_10151.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10151 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10151 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10151.

Lemma collineation_10152 : is_collineation fp_10152 fl_10152.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10152 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10152 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10152.

Lemma collineation_10153 : is_collineation fp_10153 fl_10153.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10153 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10153 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10153.

Lemma collineation_10154 : is_collineation fp_10154 fl_10154.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10154 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10154 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10154.

Lemma collineation_10155 : is_collineation fp_10155 fl_10155.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10155 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10155 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10155.

Lemma collineation_10156 : is_collineation fp_10156 fl_10156.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10156 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10156 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10156.

Lemma collineation_10157 : is_collineation fp_10157 fl_10157.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10157 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10157 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10157.

Lemma collineation_10158 : is_collineation fp_10158 fl_10158.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10158 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10158 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10158.

Lemma collineation_10159 : is_collineation fp_10159 fl_10159.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10159 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10159 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10159.

Lemma collineation_10160 : is_collineation fp_10160 fl_10160.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10160 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10160 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10160.

Lemma collineation_10161 : is_collineation fp_10161 fl_10161.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10161 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10161 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10161.

Lemma collineation_10162 : is_collineation fp_10162 fl_10162.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10162 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10162 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10162.

Lemma collineation_10163 : is_collineation fp_10163 fl_10163.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10163 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10163 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10163.

Lemma collineation_10164 : is_collineation fp_10164 fl_10164.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10164 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10164 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10164.

Lemma collineation_10165 : is_collineation fp_10165 fl_10165.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10165 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10165 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10165.

Lemma collineation_10166 : is_collineation fp_10166 fl_10166.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10166 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10166 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10166.

Lemma collineation_10167 : is_collineation fp_10167 fl_10167.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10167 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10167 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10167.

Lemma collineation_10168 : is_collineation fp_10168 fl_10168.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10168 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10168 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10168.

Lemma collineation_10169 : is_collineation fp_10169 fl_10169.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10169 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10169 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10169.

Lemma collineation_10170 : is_collineation fp_10170 fl_10170.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10170 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10170 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10170.

Lemma collineation_10171 : is_collineation fp_10171 fl_10171.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10171 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10171 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10171.

Lemma collineation_10172 : is_collineation fp_10172 fl_10172.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10172 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10172 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10172.

Lemma collineation_10173 : is_collineation fp_10173 fl_10173.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10173 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10173 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10173.

Lemma collineation_10174 : is_collineation fp_10174 fl_10174.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10174 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10174 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10174.

Lemma collineation_10175 : is_collineation fp_10175 fl_10175.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10175 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10175 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10175.

Lemma collineation_10176 : is_collineation fp_10176 fl_10176.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10176 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10176 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10176.

Lemma collineation_10177 : is_collineation fp_10177 fl_10177.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10177 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10177 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10177.

Lemma collineation_10178 : is_collineation fp_10178 fl_10178.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10178 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10178 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10178.

Lemma collineation_10179 : is_collineation fp_10179 fl_10179.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10179 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10179 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10179.

Lemma collineation_10180 : is_collineation fp_10180 fl_10180.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10180 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10180 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10180.

Lemma collineation_10181 : is_collineation fp_10181 fl_10181.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10181 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10181 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10181.

Lemma collineation_10182 : is_collineation fp_10182 fl_10182.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10182 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10182 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10182.

Lemma collineation_10183 : is_collineation fp_10183 fl_10183.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10183 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10183 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10183.

Lemma collineation_10184 : is_collineation fp_10184 fl_10184.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10184 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10184 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10184.

Lemma collineation_10185 : is_collineation fp_10185 fl_10185.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10185 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10185 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10185.

Lemma collineation_10186 : is_collineation fp_10186 fl_10186.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10186 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10186 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10186.

Lemma collineation_10187 : is_collineation fp_10187 fl_10187.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10187 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10187 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10187.

Lemma collineation_10188 : is_collineation fp_10188 fl_10188.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10188 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10188 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10188.

Lemma collineation_10189 : is_collineation fp_10189 fl_10189.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10189 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10189 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10189.

Lemma collineation_10190 : is_collineation fp_10190 fl_10190.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10190 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10190 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10190.

Lemma collineation_10191 : is_collineation fp_10191 fl_10191.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10191 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10191 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10191.

Lemma collineation_10192 : is_collineation fp_10192 fl_10192.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10192 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10192 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10192.

Lemma collineation_10193 : is_collineation fp_10193 fl_10193.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10193 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10193 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10193.

Lemma collineation_10194 : is_collineation fp_10194 fl_10194.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10194 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10194 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10194.

Lemma collineation_10195 : is_collineation fp_10195 fl_10195.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10195 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10195 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10195.

Lemma collineation_10196 : is_collineation fp_10196 fl_10196.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10196 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10196 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10196.

Lemma collineation_10197 : is_collineation fp_10197 fl_10197.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10197 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10197 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10197.

Lemma collineation_10198 : is_collineation fp_10198 fl_10198.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10198 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10198 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10198.

Lemma collineation_10199 : is_collineation fp_10199 fl_10199.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10199 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10199 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10199.

Lemma collineation_10200 : is_collineation fp_10200 fl_10200.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10200 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10200 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10200.

Lemma collineation_10201 : is_collineation fp_10201 fl_10201.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10201 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10201 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10201.

Lemma collineation_10202 : is_collineation fp_10202 fl_10202.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10202 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10202 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10202.

Lemma collineation_10203 : is_collineation fp_10203 fl_10203.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10203 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10203 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10203.

Lemma collineation_10204 : is_collineation fp_10204 fl_10204.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10204 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10204 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10204.

Lemma collineation_10205 : is_collineation fp_10205 fl_10205.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10205 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10205 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10205.

Lemma collineation_10206 : is_collineation fp_10206 fl_10206.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10206 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10206 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10206.

Lemma collineation_10207 : is_collineation fp_10207 fl_10207.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10207 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10207 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10207.

Lemma collineation_10208 : is_collineation fp_10208 fl_10208.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10208 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10208 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10208.

Lemma collineation_10209 : is_collineation fp_10209 fl_10209.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10209 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10209 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10209.

Lemma collineation_10210 : is_collineation fp_10210 fl_10210.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10210 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10210 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10210.

Lemma collineation_10211 : is_collineation fp_10211 fl_10211.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10211 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10211 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10211.

Lemma collineation_10212 : is_collineation fp_10212 fl_10212.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10212 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10212 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10212.

Lemma collineation_10213 : is_collineation fp_10213 fl_10213.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10213 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10213 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10213.

Lemma collineation_10214 : is_collineation fp_10214 fl_10214.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10214 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10214 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10214.

Lemma collineation_10215 : is_collineation fp_10215 fl_10215.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10215 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10215 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10215.

Lemma collineation_10216 : is_collineation fp_10216 fl_10216.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10216 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10216 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10216.

Lemma collineation_10217 : is_collineation fp_10217 fl_10217.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10217 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10217 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10217.

Lemma collineation_10218 : is_collineation fp_10218 fl_10218.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10218 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10218 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10218.

Lemma collineation_10219 : is_collineation fp_10219 fl_10219.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10219 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10219 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10219.

Lemma collineation_10220 : is_collineation fp_10220 fl_10220.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10220 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10220 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10220.

Lemma collineation_10221 : is_collineation fp_10221 fl_10221.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10221 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10221 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10221.

Lemma collineation_10222 : is_collineation fp_10222 fl_10222.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10222 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10222 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10222.

Lemma collineation_10223 : is_collineation fp_10223 fl_10223.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10223 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10223 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10223.

Lemma collineation_10224 : is_collineation fp_10224 fl_10224.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10224 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10224 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10224.

Lemma collineation_10225 : is_collineation fp_10225 fl_10225.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10225 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10225 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10225.

Lemma collineation_10226 : is_collineation fp_10226 fl_10226.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10226 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10226 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10226.

Lemma collineation_10227 : is_collineation fp_10227 fl_10227.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10227 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10227 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10227.

Lemma collineation_10228 : is_collineation fp_10228 fl_10228.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10228 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10228 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10228.

Lemma collineation_10229 : is_collineation fp_10229 fl_10229.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10229 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10229 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10229.

Lemma collineation_10230 : is_collineation fp_10230 fl_10230.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10230 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10230 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10230.

Lemma collineation_10231 : is_collineation fp_10231 fl_10231.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10231 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10231 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10231.

Lemma collineation_10232 : is_collineation fp_10232 fl_10232.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10232 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10232 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10232.

Lemma collineation_10233 : is_collineation fp_10233 fl_10233.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10233 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10233 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10233.

Lemma collineation_10234 : is_collineation fp_10234 fl_10234.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10234 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10234 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10234.

Lemma collineation_10235 : is_collineation fp_10235 fl_10235.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10235 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10235 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10235.

Lemma collineation_10236 : is_collineation fp_10236 fl_10236.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10236 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10236 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10236.

Lemma collineation_10237 : is_collineation fp_10237 fl_10237.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10237 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10237 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10237.

Lemma collineation_10238 : is_collineation fp_10238 fl_10238.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10238 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10238 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10238.

Lemma collineation_10239 : is_collineation fp_10239 fl_10239.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10239 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10239 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10239.

Lemma collineation_10240 : is_collineation fp_10240 fl_10240.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10240 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10240 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10240.

Lemma collineation_10241 : is_collineation fp_10241 fl_10241.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10241 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10241 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10241.

Lemma collineation_10242 : is_collineation fp_10242 fl_10242.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10242 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10242 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10242.

Lemma collineation_10243 : is_collineation fp_10243 fl_10243.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10243 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10243 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10243.

Lemma collineation_10244 : is_collineation fp_10244 fl_10244.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10244 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10244 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10244.

Lemma collineation_10245 : is_collineation fp_10245 fl_10245.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10245 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10245 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10245.

Lemma collineation_10246 : is_collineation fp_10246 fl_10246.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10246 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10246 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10246.

Lemma collineation_10247 : is_collineation fp_10247 fl_10247.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10247 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10247 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10247.

Lemma collineation_10248 : is_collineation fp_10248 fl_10248.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10248 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10248 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10248.

Lemma collineation_10249 : is_collineation fp_10249 fl_10249.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10249 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10249 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10249.

Lemma collineation_10250 : is_collineation fp_10250 fl_10250.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10250 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10250 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10250.

Lemma collineation_10251 : is_collineation fp_10251 fl_10251.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10251 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10251 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10251.

Lemma collineation_10252 : is_collineation fp_10252 fl_10252.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10252 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10252 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10252.

Lemma collineation_10253 : is_collineation fp_10253 fl_10253.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10253 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10253 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10253.

Lemma collineation_10254 : is_collineation fp_10254 fl_10254.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10254 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10254 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10254.

Lemma collineation_10255 : is_collineation fp_10255 fl_10255.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10255 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10255 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10255.

Lemma collineation_10256 : is_collineation fp_10256 fl_10256.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10256 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10256 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10256.

Lemma collineation_10257 : is_collineation fp_10257 fl_10257.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10257 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10257 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10257.

Lemma collineation_10258 : is_collineation fp_10258 fl_10258.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10258 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10258 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10258.

Lemma collineation_10259 : is_collineation fp_10259 fl_10259.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10259 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10259 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10259.

Lemma collineation_10260 : is_collineation fp_10260 fl_10260.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10260 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10260 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10260.

Lemma collineation_10261 : is_collineation fp_10261 fl_10261.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10261 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10261 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10261.

Lemma collineation_10262 : is_collineation fp_10262 fl_10262.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10262 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10262 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10262.

Lemma collineation_10263 : is_collineation fp_10263 fl_10263.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10263 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10263 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10263.

Lemma collineation_10264 : is_collineation fp_10264 fl_10264.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10264 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10264 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10264.

Lemma collineation_10265 : is_collineation fp_10265 fl_10265.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10265 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10265 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10265.

Lemma collineation_10266 : is_collineation fp_10266 fl_10266.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10266 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10266 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10266.

Lemma collineation_10267 : is_collineation fp_10267 fl_10267.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10267 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10267 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10267.

Lemma collineation_10268 : is_collineation fp_10268 fl_10268.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10268 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10268 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10268.

Lemma collineation_10269 : is_collineation fp_10269 fl_10269.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10269 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10269 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10269.

Lemma collineation_10270 : is_collineation fp_10270 fl_10270.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10270 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10270 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10270.

Lemma collineation_10271 : is_collineation fp_10271 fl_10271.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10271 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10271 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10271.

Lemma collineation_10272 : is_collineation fp_10272 fl_10272.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10272 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10272 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10272.

Lemma collineation_10273 : is_collineation fp_10273 fl_10273.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10273 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10273 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10273.

Lemma collineation_10274 : is_collineation fp_10274 fl_10274.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10274 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10274 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10274.

Lemma collineation_10275 : is_collineation fp_10275 fl_10275.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10275 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10275 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10275.

Lemma collineation_10276 : is_collineation fp_10276 fl_10276.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10276 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10276 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10276.

Lemma collineation_10277 : is_collineation fp_10277 fl_10277.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10277 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10277 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10277.

Lemma collineation_10278 : is_collineation fp_10278 fl_10278.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10278 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10278 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10278.

Lemma collineation_10279 : is_collineation fp_10279 fl_10279.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10279 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10279 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10279.

Lemma collineation_10280 : is_collineation fp_10280 fl_10280.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10280 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10280 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10280.

Lemma collineation_10281 : is_collineation fp_10281 fl_10281.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10281 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10281 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10281.

Lemma collineation_10282 : is_collineation fp_10282 fl_10282.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10282 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10282 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10282.

Lemma collineation_10283 : is_collineation fp_10283 fl_10283.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10283 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10283 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10283.

Lemma collineation_10284 : is_collineation fp_10284 fl_10284.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10284 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10284 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10284.

Lemma collineation_10285 : is_collineation fp_10285 fl_10285.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10285 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10285 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10285.

Lemma collineation_10286 : is_collineation fp_10286 fl_10286.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10286 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10286 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10286.

Lemma collineation_10287 : is_collineation fp_10287 fl_10287.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10287 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10287 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10287.

Lemma collineation_10288 : is_collineation fp_10288 fl_10288.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10288 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10288 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10288.

Lemma collineation_10289 : is_collineation fp_10289 fl_10289.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10289 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10289 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10289.

Lemma collineation_10290 : is_collineation fp_10290 fl_10290.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10290 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10290 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10290.

Lemma collineation_10291 : is_collineation fp_10291 fl_10291.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10291 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10291 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10291.

Lemma collineation_10292 : is_collineation fp_10292 fl_10292.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10292 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10292 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10292.

Lemma collineation_10293 : is_collineation fp_10293 fl_10293.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10293 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10293 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10293.

Lemma collineation_10294 : is_collineation fp_10294 fl_10294.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10294 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10294 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10294.

Lemma collineation_10295 : is_collineation fp_10295 fl_10295.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10295 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10295 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10295.

Lemma collineation_10296 : is_collineation fp_10296 fl_10296.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10296 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10296 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10296.

Lemma collineation_10297 : is_collineation fp_10297 fl_10297.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10297 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10297 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10297.

Lemma collineation_10298 : is_collineation fp_10298 fl_10298.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10298 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10298 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10298.

Lemma collineation_10299 : is_collineation fp_10299 fl_10299.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10299 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10299 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10299.

Lemma collineation_10300 : is_collineation fp_10300 fl_10300.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10300 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10300 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10300.

Lemma collineation_10301 : is_collineation fp_10301 fl_10301.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10301 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10301 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10301.

Lemma collineation_10302 : is_collineation fp_10302 fl_10302.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10302 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10302 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10302.

Lemma collineation_10303 : is_collineation fp_10303 fl_10303.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10303 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10303 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10303.

Lemma collineation_10304 : is_collineation fp_10304 fl_10304.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10304 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10304 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10304.

Lemma collineation_10305 : is_collineation fp_10305 fl_10305.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10305 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10305 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10305.

Lemma collineation_10306 : is_collineation fp_10306 fl_10306.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10306 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10306 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10306.

Lemma collineation_10307 : is_collineation fp_10307 fl_10307.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10307 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10307 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10307.

Lemma collineation_10308 : is_collineation fp_10308 fl_10308.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10308 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10308 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10308.

Lemma collineation_10309 : is_collineation fp_10309 fl_10309.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10309 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10309 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10309.

Lemma collineation_10310 : is_collineation fp_10310 fl_10310.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10310 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10310 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10310.

Lemma collineation_10311 : is_collineation fp_10311 fl_10311.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10311 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10311 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10311.

Lemma collineation_10312 : is_collineation fp_10312 fl_10312.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10312 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10312 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10312.

Lemma collineation_10313 : is_collineation fp_10313 fl_10313.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10313 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10313 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10313.

Lemma collineation_10314 : is_collineation fp_10314 fl_10314.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10314 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10314 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10314.

Lemma collineation_10315 : is_collineation fp_10315 fl_10315.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10315 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10315 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10315.

Lemma collineation_10316 : is_collineation fp_10316 fl_10316.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10316 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10316 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10316.

Lemma collineation_10317 : is_collineation fp_10317 fl_10317.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10317 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10317 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10317.

Lemma collineation_10318 : is_collineation fp_10318 fl_10318.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10318 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10318 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10318.

Lemma collineation_10319 : is_collineation fp_10319 fl_10319.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10319 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10319 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10319.

Lemma collineation_10320 : is_collineation fp_10320 fl_10320.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10320 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10320 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10320.

Lemma collineation_10321 : is_collineation fp_10321 fl_10321.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10321 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10321 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10321.

Lemma collineation_10322 : is_collineation fp_10322 fl_10322.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10322 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10322 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10322.

Lemma collineation_10323 : is_collineation fp_10323 fl_10323.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10323 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10323 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10323.

Lemma collineation_10324 : is_collineation fp_10324 fl_10324.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10324 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10324 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10324.

Lemma collineation_10325 : is_collineation fp_10325 fl_10325.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10325 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10325 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10325.

Lemma collineation_10326 : is_collineation fp_10326 fl_10326.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10326 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10326 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10326.

Lemma collineation_10327 : is_collineation fp_10327 fl_10327.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10327 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10327 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10327.

Lemma collineation_10328 : is_collineation fp_10328 fl_10328.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10328 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10328 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10328.

Lemma collineation_10329 : is_collineation fp_10329 fl_10329.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10329 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10329 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10329.

Lemma collineation_10330 : is_collineation fp_10330 fl_10330.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10330 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10330 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10330.

Lemma collineation_10331 : is_collineation fp_10331 fl_10331.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10331 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10331 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10331.

Lemma collineation_10332 : is_collineation fp_10332 fl_10332.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10332 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10332 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10332.

Lemma collineation_10333 : is_collineation fp_10333 fl_10333.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10333 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10333 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10333.

Lemma collineation_10334 : is_collineation fp_10334 fl_10334.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10334 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10334 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10334.

Lemma collineation_10335 : is_collineation fp_10335 fl_10335.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10335 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10335 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10335.

Lemma collineation_10336 : is_collineation fp_10336 fl_10336.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10336 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10336 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10336.

Lemma collineation_10337 : is_collineation fp_10337 fl_10337.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10337 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10337 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10337.

Lemma collineation_10338 : is_collineation fp_10338 fl_10338.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10338 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10338 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10338.

Lemma collineation_10339 : is_collineation fp_10339 fl_10339.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10339 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10339 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10339.

Lemma collineation_10340 : is_collineation fp_10340 fl_10340.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10340 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10340 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10340.

Lemma collineation_10341 : is_collineation fp_10341 fl_10341.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10341 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10341 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10341.

Lemma collineation_10342 : is_collineation fp_10342 fl_10342.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10342 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10342 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10342.

Lemma collineation_10343 : is_collineation fp_10343 fl_10343.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10343 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10343 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10343.

Lemma collineation_10344 : is_collineation fp_10344 fl_10344.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10344 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10344 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10344.

Lemma collineation_10345 : is_collineation fp_10345 fl_10345.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10345 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10345 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10345.

Lemma collineation_10346 : is_collineation fp_10346 fl_10346.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10346 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10346 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10346.

Lemma collineation_10347 : is_collineation fp_10347 fl_10347.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10347 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10347 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10347.

Lemma collineation_10348 : is_collineation fp_10348 fl_10348.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10348 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10348 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10348.

Lemma collineation_10349 : is_collineation fp_10349 fl_10349.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10349 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10349 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10349.

Lemma collineation_10350 : is_collineation fp_10350 fl_10350.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10350 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10350 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10350.

Lemma collineation_10351 : is_collineation fp_10351 fl_10351.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10351 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10351 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10351.

Lemma collineation_10352 : is_collineation fp_10352 fl_10352.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10352 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10352 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10352.

Lemma collineation_10353 : is_collineation fp_10353 fl_10353.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10353 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10353 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10353.

Lemma collineation_10354 : is_collineation fp_10354 fl_10354.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10354 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10354 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10354.

Lemma collineation_10355 : is_collineation fp_10355 fl_10355.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10355 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10355 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10355.

Lemma collineation_10356 : is_collineation fp_10356 fl_10356.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10356 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10356 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10356.

Lemma collineation_10357 : is_collineation fp_10357 fl_10357.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10357 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10357 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10357.

Lemma collineation_10358 : is_collineation fp_10358 fl_10358.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10358 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10358 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10358.

Lemma collineation_10359 : is_collineation fp_10359 fl_10359.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10359 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10359 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10359.

Lemma collineation_10360 : is_collineation fp_10360 fl_10360.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10360 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10360 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10360.

Lemma collineation_10361 : is_collineation fp_10361 fl_10361.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10361 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10361 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10361.

Lemma collineation_10362 : is_collineation fp_10362 fl_10362.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10362 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10362 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10362.

Lemma collineation_10363 : is_collineation fp_10363 fl_10363.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10363 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10363 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10363.

Lemma collineation_10364 : is_collineation fp_10364 fl_10364.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10364 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10364 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10364.

Lemma collineation_10365 : is_collineation fp_10365 fl_10365.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10365 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10365 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10365.

Lemma collineation_10366 : is_collineation fp_10366 fl_10366.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10366 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10366 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10366.

Lemma collineation_10367 : is_collineation fp_10367 fl_10367.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10367 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10367 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10367.

Lemma collineation_10368 : is_collineation fp_10368 fl_10368.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10368 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10368 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10368.

Lemma collineation_10369 : is_collineation fp_10369 fl_10369.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10369 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10369 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10369.

Lemma collineation_10370 : is_collineation fp_10370 fl_10370.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10370 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10370 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10370.

Lemma collineation_10371 : is_collineation fp_10371 fl_10371.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10371 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10371 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10371.

Lemma collineation_10372 : is_collineation fp_10372 fl_10372.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10372 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10372 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10372.

Lemma collineation_10373 : is_collineation fp_10373 fl_10373.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10373 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10373 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10373.

Lemma collineation_10374 : is_collineation fp_10374 fl_10374.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10374 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10374 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10374.

Lemma collineation_10375 : is_collineation fp_10375 fl_10375.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10375 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10375 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10375.

Lemma collineation_10376 : is_collineation fp_10376 fl_10376.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10376 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10376 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10376.

Lemma collineation_10377 : is_collineation fp_10377 fl_10377.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10377 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10377 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10377.

Lemma collineation_10378 : is_collineation fp_10378 fl_10378.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10378 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10378 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10378.

Lemma collineation_10379 : is_collineation fp_10379 fl_10379.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10379 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10379 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10379.

Lemma collineation_10380 : is_collineation fp_10380 fl_10380.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10380 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10380 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10380.

Lemma collineation_10381 : is_collineation fp_10381 fl_10381.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10381 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10381 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10381.

Lemma collineation_10382 : is_collineation fp_10382 fl_10382.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10382 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10382 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10382.

Lemma collineation_10383 : is_collineation fp_10383 fl_10383.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10383 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10383 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10383.

Lemma collineation_10384 : is_collineation fp_10384 fl_10384.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10384 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10384 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10384.

Lemma collineation_10385 : is_collineation fp_10385 fl_10385.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10385 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10385 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10385.

Lemma collineation_10386 : is_collineation fp_10386 fl_10386.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10386 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10386 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10386.

Lemma collineation_10387 : is_collineation fp_10387 fl_10387.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10387 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10387 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10387.

Lemma collineation_10388 : is_collineation fp_10388 fl_10388.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10388 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10388 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10388.

Lemma collineation_10389 : is_collineation fp_10389 fl_10389.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10389 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10389 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10389.

Lemma collineation_10390 : is_collineation fp_10390 fl_10390.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10390 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10390 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10390.

Lemma collineation_10391 : is_collineation fp_10391 fl_10391.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10391 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10391 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10391.

Lemma collineation_10392 : is_collineation fp_10392 fl_10392.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10392 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10392 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10392.

Lemma collineation_10393 : is_collineation fp_10393 fl_10393.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10393 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10393 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10393.

Lemma collineation_10394 : is_collineation fp_10394 fl_10394.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10394 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10394 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10394.

Lemma collineation_10395 : is_collineation fp_10395 fl_10395.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10395 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10395 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10395.

Lemma collineation_10396 : is_collineation fp_10396 fl_10396.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10396 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10396 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10396.

Lemma collineation_10397 : is_collineation fp_10397 fl_10397.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10397 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10397 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10397.

Lemma collineation_10398 : is_collineation fp_10398 fl_10398.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10398 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10398 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10398.

Lemma collineation_10399 : is_collineation fp_10399 fl_10399.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10399 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10399 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10399.

Lemma collineation_10400 : is_collineation fp_10400 fl_10400.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10400 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10400 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10400.

Lemma collineation_10401 : is_collineation fp_10401 fl_10401.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10401 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10401 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10401.

Lemma collineation_10402 : is_collineation fp_10402 fl_10402.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10402 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10402 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10402.

Lemma collineation_10403 : is_collineation fp_10403 fl_10403.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10403 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10403 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10403.

Lemma collineation_10404 : is_collineation fp_10404 fl_10404.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10404 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10404 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10404.

Lemma collineation_10405 : is_collineation fp_10405 fl_10405.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10405 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10405 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10405.

Lemma collineation_10406 : is_collineation fp_10406 fl_10406.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10406 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10406 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10406.

Lemma collineation_10407 : is_collineation fp_10407 fl_10407.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10407 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10407 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10407.

Lemma collineation_10408 : is_collineation fp_10408 fl_10408.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10408 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10408 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10408.

Lemma collineation_10409 : is_collineation fp_10409 fl_10409.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10409 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10409 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10409.

Lemma collineation_10410 : is_collineation fp_10410 fl_10410.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10410 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10410 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10410.

Lemma collineation_10411 : is_collineation fp_10411 fl_10411.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10411 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10411 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10411.

Lemma collineation_10412 : is_collineation fp_10412 fl_10412.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10412 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10412 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10412.

Lemma collineation_10413 : is_collineation fp_10413 fl_10413.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10413 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10413 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10413.

Lemma collineation_10414 : is_collineation fp_10414 fl_10414.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10414 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10414 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10414.

Lemma collineation_10415 : is_collineation fp_10415 fl_10415.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10415 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10415 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10415.

Lemma collineation_10416 : is_collineation fp_10416 fl_10416.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10416 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10416 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10416.

Lemma collineation_10417 : is_collineation fp_10417 fl_10417.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10417 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10417 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10417.

Lemma collineation_10418 : is_collineation fp_10418 fl_10418.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10418 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10418 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10418.

Lemma collineation_10419 : is_collineation fp_10419 fl_10419.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10419 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10419 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10419.

Lemma collineation_10420 : is_collineation fp_10420 fl_10420.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10420 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10420 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10420.

Lemma collineation_10421 : is_collineation fp_10421 fl_10421.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10421 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10421 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10421.

Lemma collineation_10422 : is_collineation fp_10422 fl_10422.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10422 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10422 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10422.

Lemma collineation_10423 : is_collineation fp_10423 fl_10423.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10423 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10423 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10423.

Lemma collineation_10424 : is_collineation fp_10424 fl_10424.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10424 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10424 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10424.

Lemma collineation_10425 : is_collineation fp_10425 fl_10425.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10425 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10425 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10425.

Lemma collineation_10426 : is_collineation fp_10426 fl_10426.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10426 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10426 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10426.

Lemma collineation_10427 : is_collineation fp_10427 fl_10427.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10427 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10427 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10427.

Lemma collineation_10428 : is_collineation fp_10428 fl_10428.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10428 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10428 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10428.

Lemma collineation_10429 : is_collineation fp_10429 fl_10429.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10429 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10429 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10429.

Lemma collineation_10430 : is_collineation fp_10430 fl_10430.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10430 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10430 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10430.

Lemma collineation_10431 : is_collineation fp_10431 fl_10431.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10431 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10431 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10431.

Lemma collineation_10432 : is_collineation fp_10432 fl_10432.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10432 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10432 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10432.

Lemma collineation_10433 : is_collineation fp_10433 fl_10433.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10433 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10433 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10433.

Lemma collineation_10434 : is_collineation fp_10434 fl_10434.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10434 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10434 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10434.

Lemma collineation_10435 : is_collineation fp_10435 fl_10435.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10435 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10435 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10435.

Lemma collineation_10436 : is_collineation fp_10436 fl_10436.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10436 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10436 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10436.

Lemma collineation_10437 : is_collineation fp_10437 fl_10437.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10437 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10437 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10437.

Lemma collineation_10438 : is_collineation fp_10438 fl_10438.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10438 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10438 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10438.

Lemma collineation_10439 : is_collineation fp_10439 fl_10439.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10439 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10439 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10439.

Lemma collineation_10440 : is_collineation fp_10440 fl_10440.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10440 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10440 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10440.

Lemma collineation_10441 : is_collineation fp_10441 fl_10441.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10441 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10441 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10441.

Lemma collineation_10442 : is_collineation fp_10442 fl_10442.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10442 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10442 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10442.

Lemma collineation_10443 : is_collineation fp_10443 fl_10443.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10443 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10443 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10443.

Lemma collineation_10444 : is_collineation fp_10444 fl_10444.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10444 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10444 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10444.

Lemma collineation_10445 : is_collineation fp_10445 fl_10445.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10445 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10445 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10445.

Lemma collineation_10446 : is_collineation fp_10446 fl_10446.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10446 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10446 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10446.

Lemma collineation_10447 : is_collineation fp_10447 fl_10447.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10447 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10447 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10447.

Lemma collineation_10448 : is_collineation fp_10448 fl_10448.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10448 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10448 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10448.

Lemma collineation_10449 : is_collineation fp_10449 fl_10449.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10449 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10449 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10449.

Lemma collineation_10450 : is_collineation fp_10450 fl_10450.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10450 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10450 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10450.

Lemma collineation_10451 : is_collineation fp_10451 fl_10451.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10451 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10451 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10451.

Lemma collineation_10452 : is_collineation fp_10452 fl_10452.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10452 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10452 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10452.

Lemma collineation_10453 : is_collineation fp_10453 fl_10453.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10453 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10453 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10453.

Lemma collineation_10454 : is_collineation fp_10454 fl_10454.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10454 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10454 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10454.

Lemma collineation_10455 : is_collineation fp_10455 fl_10455.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10455 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10455 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10455.

Lemma collineation_10456 : is_collineation fp_10456 fl_10456.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10456 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10456 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10456.

Lemma collineation_10457 : is_collineation fp_10457 fl_10457.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10457 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10457 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10457.

Lemma collineation_10458 : is_collineation fp_10458 fl_10458.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10458 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10458 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10458.

Lemma collineation_10459 : is_collineation fp_10459 fl_10459.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10459 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10459 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10459.

Lemma collineation_10460 : is_collineation fp_10460 fl_10460.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10460 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10460 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10460.

Lemma collineation_10461 : is_collineation fp_10461 fl_10461.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10461 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10461 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10461.

Lemma collineation_10462 : is_collineation fp_10462 fl_10462.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10462 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10462 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10462.

Lemma collineation_10463 : is_collineation fp_10463 fl_10463.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10463 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10463 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10463.

Lemma collineation_10464 : is_collineation fp_10464 fl_10464.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10464 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10464 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10464.

Lemma collineation_10465 : is_collineation fp_10465 fl_10465.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10465 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10465 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10465.

Lemma collineation_10466 : is_collineation fp_10466 fl_10466.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10466 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10466 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10466.

Lemma collineation_10467 : is_collineation fp_10467 fl_10467.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10467 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10467 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10467.

Lemma collineation_10468 : is_collineation fp_10468 fl_10468.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10468 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10468 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10468.

Lemma collineation_10469 : is_collineation fp_10469 fl_10469.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10469 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10469 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10469.

Lemma collineation_10470 : is_collineation fp_10470 fl_10470.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10470 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10470 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10470.

Lemma collineation_10471 : is_collineation fp_10471 fl_10471.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10471 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10471 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10471.

Lemma collineation_10472 : is_collineation fp_10472 fl_10472.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10472 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10472 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10472.

Lemma collineation_10473 : is_collineation fp_10473 fl_10473.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10473 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10473 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10473.

Lemma collineation_10474 : is_collineation fp_10474 fl_10474.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10474 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10474 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10474.

Lemma collineation_10475 : is_collineation fp_10475 fl_10475.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10475 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10475 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10475.

Lemma collineation_10476 : is_collineation fp_10476 fl_10476.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10476 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10476 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10476.

Lemma collineation_10477 : is_collineation fp_10477 fl_10477.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10477 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10477 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10477.

Lemma collineation_10478 : is_collineation fp_10478 fl_10478.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10478 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10478 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10478.

Lemma collineation_10479 : is_collineation fp_10479 fl_10479.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10479 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10479 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10479.

Lemma collineation_10480 : is_collineation fp_10480 fl_10480.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10480 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10480 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10480.

Lemma collineation_10481 : is_collineation fp_10481 fl_10481.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10481 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10481 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10481.

Lemma collineation_10482 : is_collineation fp_10482 fl_10482.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10482 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10482 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10482.

Lemma collineation_10483 : is_collineation fp_10483 fl_10483.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10483 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10483 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10483.

Lemma collineation_10484 : is_collineation fp_10484 fl_10484.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10484 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10484 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10484.

Lemma collineation_10485 : is_collineation fp_10485 fl_10485.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10485 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10485 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10485.

Lemma collineation_10486 : is_collineation fp_10486 fl_10486.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10486 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10486 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10486.

Lemma collineation_10487 : is_collineation fp_10487 fl_10487.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10487 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10487 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10487.

Lemma collineation_10488 : is_collineation fp_10488 fl_10488.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10488 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10488 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10488.

Lemma collineation_10489 : is_collineation fp_10489 fl_10489.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10489 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10489 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10489.

Lemma collineation_10490 : is_collineation fp_10490 fl_10490.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10490 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10490 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10490.

Lemma collineation_10491 : is_collineation fp_10491 fl_10491.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10491 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10491 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10491.

Lemma collineation_10492 : is_collineation fp_10492 fl_10492.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10492 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10492 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10492.

Lemma collineation_10493 : is_collineation fp_10493 fl_10493.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10493 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10493 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10493.

Lemma collineation_10494 : is_collineation fp_10494 fl_10494.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10494 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10494 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10494.

Lemma collineation_10495 : is_collineation fp_10495 fl_10495.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10495 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10495 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10495.

Lemma collineation_10496 : is_collineation fp_10496 fl_10496.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10496 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10496 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10496.

Lemma collineation_10497 : is_collineation fp_10497 fl_10497.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10497 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10497 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10497.

Lemma collineation_10498 : is_collineation fp_10498 fl_10498.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10498 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10498 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10498.

Lemma collineation_10499 : is_collineation fp_10499 fl_10499.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10499 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10499 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10499.

Lemma collineation_10500 : is_collineation fp_10500 fl_10500.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10500 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10500 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10500.

Lemma collineation_10501 : is_collineation fp_10501 fl_10501.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10501 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10501 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10501.

Lemma collineation_10502 : is_collineation fp_10502 fl_10502.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10502 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10502 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10502.

Lemma collineation_10503 : is_collineation fp_10503 fl_10503.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10503 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10503 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10503.

Lemma collineation_10504 : is_collineation fp_10504 fl_10504.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10504 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10504 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10504.

Lemma collineation_10505 : is_collineation fp_10505 fl_10505.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10505 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10505 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10505.

Lemma collineation_10506 : is_collineation fp_10506 fl_10506.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10506 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10506 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10506.

Lemma collineation_10507 : is_collineation fp_10507 fl_10507.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10507 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10507 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10507.

Lemma collineation_10508 : is_collineation fp_10508 fl_10508.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10508 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10508 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10508.

Lemma collineation_10509 : is_collineation fp_10509 fl_10509.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10509 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10509 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10509.

Lemma collineation_10510 : is_collineation fp_10510 fl_10510.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10510 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10510 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10510.

Lemma collineation_10511 : is_collineation fp_10511 fl_10511.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10511 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10511 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10511.

Lemma collineation_10512 : is_collineation fp_10512 fl_10512.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10512 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10512 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10512.

Lemma collineation_10513 : is_collineation fp_10513 fl_10513.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10513 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10513 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10513.

Lemma collineation_10514 : is_collineation fp_10514 fl_10514.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10514 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10514 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10514.

Lemma collineation_10515 : is_collineation fp_10515 fl_10515.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10515 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10515 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10515.

Lemma collineation_10516 : is_collineation fp_10516 fl_10516.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10516 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10516 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10516.

Lemma collineation_10517 : is_collineation fp_10517 fl_10517.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10517 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10517 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10517.

Lemma collineation_10518 : is_collineation fp_10518 fl_10518.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10518 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10518 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10518.

Lemma collineation_10519 : is_collineation fp_10519 fl_10519.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10519 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10519 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10519.

Lemma collineation_10520 : is_collineation fp_10520 fl_10520.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10520 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10520 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10520.

Lemma collineation_10521 : is_collineation fp_10521 fl_10521.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10521 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10521 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10521.

Lemma collineation_10522 : is_collineation fp_10522 fl_10522.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10522 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10522 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10522.

Lemma collineation_10523 : is_collineation fp_10523 fl_10523.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10523 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10523 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10523.

Lemma collineation_10524 : is_collineation fp_10524 fl_10524.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10524 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10524 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10524.

Lemma collineation_10525 : is_collineation fp_10525 fl_10525.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10525 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10525 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10525.

Lemma collineation_10526 : is_collineation fp_10526 fl_10526.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10526 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10526 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10526.

Lemma collineation_10527 : is_collineation fp_10527 fl_10527.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10527 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10527 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10527.

Lemma collineation_10528 : is_collineation fp_10528 fl_10528.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10528 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10528 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10528.

Lemma collineation_10529 : is_collineation fp_10529 fl_10529.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10529 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10529 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10529.

Lemma collineation_10530 : is_collineation fp_10530 fl_10530.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10530 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10530 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10530.

Lemma collineation_10531 : is_collineation fp_10531 fl_10531.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10531 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10531 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10531.

Lemma collineation_10532 : is_collineation fp_10532 fl_10532.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10532 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10532 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10532.

Lemma collineation_10533 : is_collineation fp_10533 fl_10533.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10533 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10533 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10533.

Lemma collineation_10534 : is_collineation fp_10534 fl_10534.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10534 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10534 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10534.

Lemma collineation_10535 : is_collineation fp_10535 fl_10535.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10535 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10535 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10535.

Lemma collineation_10536 : is_collineation fp_10536 fl_10536.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10536 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10536 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10536.

Lemma collineation_10537 : is_collineation fp_10537 fl_10537.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10537 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10537 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10537.

Lemma collineation_10538 : is_collineation fp_10538 fl_10538.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10538 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10538 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10538.

Lemma collineation_10539 : is_collineation fp_10539 fl_10539.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10539 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10539 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10539.

Lemma collineation_10540 : is_collineation fp_10540 fl_10540.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10540 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10540 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10540.

Lemma collineation_10541 : is_collineation fp_10541 fl_10541.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10541 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10541 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10541.

Lemma collineation_10542 : is_collineation fp_10542 fl_10542.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10542 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10542 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10542.

Lemma collineation_10543 : is_collineation fp_10543 fl_10543.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10543 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10543 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10543.

Lemma collineation_10544 : is_collineation fp_10544 fl_10544.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10544 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10544 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10544.

Lemma collineation_10545 : is_collineation fp_10545 fl_10545.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10545 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10545 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10545.

Lemma collineation_10546 : is_collineation fp_10546 fl_10546.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10546 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10546 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10546.

Lemma collineation_10547 : is_collineation fp_10547 fl_10547.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10547 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10547 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10547.

Lemma collineation_10548 : is_collineation fp_10548 fl_10548.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10548 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10548 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10548.

Lemma collineation_10549 : is_collineation fp_10549 fl_10549.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10549 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10549 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10549.

Lemma collineation_10550 : is_collineation fp_10550 fl_10550.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10550 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10550 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10550.

Lemma collineation_10551 : is_collineation fp_10551 fl_10551.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10551 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10551 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10551.

Lemma collineation_10552 : is_collineation fp_10552 fl_10552.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10552 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10552 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10552.

Lemma collineation_10553 : is_collineation fp_10553 fl_10553.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10553 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10553 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10553.

Lemma collineation_10554 : is_collineation fp_10554 fl_10554.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10554 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10554 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10554.

Lemma collineation_10555 : is_collineation fp_10555 fl_10555.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10555 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10555 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10555.

Lemma collineation_10556 : is_collineation fp_10556 fl_10556.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10556 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10556 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10556.

Lemma collineation_10557 : is_collineation fp_10557 fl_10557.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10557 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10557 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10557.

Lemma collineation_10558 : is_collineation fp_10558 fl_10558.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10558 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10558 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10558.

Lemma collineation_10559 : is_collineation fp_10559 fl_10559.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10559 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10559 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10559.

Lemma collineation_10560 : is_collineation fp_10560 fl_10560.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10560 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10560 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10560.

Lemma collineation_10561 : is_collineation fp_10561 fl_10561.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10561 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10561 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10561.

Lemma collineation_10562 : is_collineation fp_10562 fl_10562.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10562 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10562 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10562.

Lemma collineation_10563 : is_collineation fp_10563 fl_10563.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10563 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10563 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10563.

Lemma collineation_10564 : is_collineation fp_10564 fl_10564.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10564 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10564 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10564.

Lemma collineation_10565 : is_collineation fp_10565 fl_10565.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10565 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10565 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10565.

Lemma collineation_10566 : is_collineation fp_10566 fl_10566.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10566 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10566 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10566.

Lemma collineation_10567 : is_collineation fp_10567 fl_10567.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10567 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10567 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10567.

Lemma collineation_10568 : is_collineation fp_10568 fl_10568.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10568 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10568 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10568.

Lemma collineation_10569 : is_collineation fp_10569 fl_10569.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10569 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10569 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10569.

Lemma collineation_10570 : is_collineation fp_10570 fl_10570.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10570 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10570 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10570.

Lemma collineation_10571 : is_collineation fp_10571 fl_10571.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10571 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10571 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10571.

Lemma collineation_10572 : is_collineation fp_10572 fl_10572.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10572 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10572 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10572.

Lemma collineation_10573 : is_collineation fp_10573 fl_10573.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10573 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10573 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10573.

Lemma collineation_10574 : is_collineation fp_10574 fl_10574.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10574 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10574 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10574.

Lemma collineation_10575 : is_collineation fp_10575 fl_10575.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10575 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10575 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10575.

Lemma collineation_10576 : is_collineation fp_10576 fl_10576.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10576 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10576 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10576.

Lemma collineation_10577 : is_collineation fp_10577 fl_10577.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10577 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10577 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10577.

Lemma collineation_10578 : is_collineation fp_10578 fl_10578.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10578 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10578 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10578.

Lemma collineation_10579 : is_collineation fp_10579 fl_10579.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10579 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10579 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10579.

Lemma collineation_10580 : is_collineation fp_10580 fl_10580.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10580 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10580 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10580.

Lemma collineation_10581 : is_collineation fp_10581 fl_10581.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10581 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10581 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10581.

Lemma collineation_10582 : is_collineation fp_10582 fl_10582.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10582 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10582 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10582.

Lemma collineation_10583 : is_collineation fp_10583 fl_10583.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10583 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10583 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10583.

Lemma collineation_10584 : is_collineation fp_10584 fl_10584.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10584 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10584 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10584.

Lemma collineation_10585 : is_collineation fp_10585 fl_10585.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10585 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10585 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10585.

Lemma collineation_10586 : is_collineation fp_10586 fl_10586.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10586 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10586 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10586.

Lemma collineation_10587 : is_collineation fp_10587 fl_10587.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10587 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10587 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10587.

Lemma collineation_10588 : is_collineation fp_10588 fl_10588.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10588 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10588 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10588.

Lemma collineation_10589 : is_collineation fp_10589 fl_10589.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10589 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10589 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10589.

Lemma collineation_10590 : is_collineation fp_10590 fl_10590.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10590 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10590 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10590.

Lemma collineation_10591 : is_collineation fp_10591 fl_10591.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10591 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10591 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10591.

Lemma collineation_10592 : is_collineation fp_10592 fl_10592.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10592 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10592 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10592.

Lemma collineation_10593 : is_collineation fp_10593 fl_10593.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10593 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10593 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10593.

Lemma collineation_10594 : is_collineation fp_10594 fl_10594.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10594 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10594 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10594.

Lemma collineation_10595 : is_collineation fp_10595 fl_10595.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10595 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10595 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10595.

Lemma collineation_10596 : is_collineation fp_10596 fl_10596.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10596 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10596 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10596.

Lemma collineation_10597 : is_collineation fp_10597 fl_10597.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10597 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10597 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10597.

Lemma collineation_10598 : is_collineation fp_10598 fl_10598.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10598 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10598 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10598.

Lemma collineation_10599 : is_collineation fp_10599 fl_10599.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10599 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10599 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10599.

Lemma collineation_10600 : is_collineation fp_10600 fl_10600.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10600 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10600 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10600.

Lemma collineation_10601 : is_collineation fp_10601 fl_10601.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10601 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10601 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10601.

Lemma collineation_10602 : is_collineation fp_10602 fl_10602.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10602 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10602 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10602.

Lemma collineation_10603 : is_collineation fp_10603 fl_10603.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10603 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10603 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10603.

Lemma collineation_10604 : is_collineation fp_10604 fl_10604.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10604 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10604 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10604.

Lemma collineation_10605 : is_collineation fp_10605 fl_10605.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10605 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10605 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10605.

Lemma collineation_10606 : is_collineation fp_10606 fl_10606.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10606 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10606 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10606.

Lemma collineation_10607 : is_collineation fp_10607 fl_10607.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10607 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10607 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10607.

Lemma collineation_10608 : is_collineation fp_10608 fl_10608.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10608 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10608 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10608.

Lemma collineation_10609 : is_collineation fp_10609 fl_10609.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10609 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10609 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10609.

Lemma collineation_10610 : is_collineation fp_10610 fl_10610.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10610 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10610 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10610.

Lemma collineation_10611 : is_collineation fp_10611 fl_10611.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10611 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10611 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10611.

Lemma collineation_10612 : is_collineation fp_10612 fl_10612.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10612 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10612 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10612.

Lemma collineation_10613 : is_collineation fp_10613 fl_10613.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10613 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10613 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10613.

Lemma collineation_10614 : is_collineation fp_10614 fl_10614.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10614 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10614 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10614.

Lemma collineation_10615 : is_collineation fp_10615 fl_10615.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10615 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10615 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10615.

Lemma collineation_10616 : is_collineation fp_10616 fl_10616.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10616 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10616 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10616.

Lemma collineation_10617 : is_collineation fp_10617 fl_10617.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10617 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10617 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10617.

Lemma collineation_10618 : is_collineation fp_10618 fl_10618.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10618 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10618 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10618.

Lemma collineation_10619 : is_collineation fp_10619 fl_10619.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10619 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10619 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10619.

Lemma collineation_10620 : is_collineation fp_10620 fl_10620.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10620 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10620 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10620.

Lemma collineation_10621 : is_collineation fp_10621 fl_10621.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10621 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10621 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10621.

Lemma collineation_10622 : is_collineation fp_10622 fl_10622.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10622 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10622 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10622.

Lemma collineation_10623 : is_collineation fp_10623 fl_10623.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10623 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10623 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10623.

Lemma collineation_10624 : is_collineation fp_10624 fl_10624.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10624 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10624 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10624.

Lemma collineation_10625 : is_collineation fp_10625 fl_10625.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10625 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10625 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10625.

Lemma collineation_10626 : is_collineation fp_10626 fl_10626.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10626 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10626 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10626.

Lemma collineation_10627 : is_collineation fp_10627 fl_10627.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10627 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10627 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10627.

Lemma collineation_10628 : is_collineation fp_10628 fl_10628.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10628 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10628 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10628.

Lemma collineation_10629 : is_collineation fp_10629 fl_10629.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10629 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10629 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10629.

Lemma collineation_10630 : is_collineation fp_10630 fl_10630.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10630 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10630 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10630.

Lemma collineation_10631 : is_collineation fp_10631 fl_10631.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10631 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10631 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10631.

Lemma collineation_10632 : is_collineation fp_10632 fl_10632.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10632 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10632 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10632.

Lemma collineation_10633 : is_collineation fp_10633 fl_10633.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10633 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10633 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10633.

Lemma collineation_10634 : is_collineation fp_10634 fl_10634.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10634 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10634 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10634.

Lemma collineation_10635 : is_collineation fp_10635 fl_10635.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10635 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10635 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10635.

Lemma collineation_10636 : is_collineation fp_10636 fl_10636.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10636 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10636 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10636.

Lemma collineation_10637 : is_collineation fp_10637 fl_10637.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10637 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10637 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10637.

Lemma collineation_10638 : is_collineation fp_10638 fl_10638.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10638 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10638 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10638.

Lemma collineation_10639 : is_collineation fp_10639 fl_10639.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10639 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10639 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10639.

Lemma collineation_10640 : is_collineation fp_10640 fl_10640.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10640 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10640 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10640.

Lemma collineation_10641 : is_collineation fp_10641 fl_10641.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10641 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10641 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10641.

Lemma collineation_10642 : is_collineation fp_10642 fl_10642.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10642 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10642 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10642.

Lemma collineation_10643 : is_collineation fp_10643 fl_10643.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10643 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10643 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10643.

Lemma collineation_10644 : is_collineation fp_10644 fl_10644.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10644 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10644 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10644.

Lemma collineation_10645 : is_collineation fp_10645 fl_10645.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10645 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10645 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10645.

Lemma collineation_10646 : is_collineation fp_10646 fl_10646.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10646 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10646 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10646.

Lemma collineation_10647 : is_collineation fp_10647 fl_10647.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10647 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10647 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10647.

Lemma collineation_10648 : is_collineation fp_10648 fl_10648.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10648 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10648 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10648.

Lemma collineation_10649 : is_collineation fp_10649 fl_10649.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10649 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10649 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10649.

Lemma collineation_10650 : is_collineation fp_10650 fl_10650.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10650 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10650 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10650.

Lemma collineation_10651 : is_collineation fp_10651 fl_10651.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10651 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10651 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10651.

Lemma collineation_10652 : is_collineation fp_10652 fl_10652.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10652 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10652 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10652.

Lemma collineation_10653 : is_collineation fp_10653 fl_10653.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10653 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10653 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10653.

Lemma collineation_10654 : is_collineation fp_10654 fl_10654.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10654 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10654 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10654.

Lemma collineation_10655 : is_collineation fp_10655 fl_10655.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10655 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10655 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10655.

Lemma collineation_10656 : is_collineation fp_10656 fl_10656.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10656 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10656 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10656.

Lemma collineation_10657 : is_collineation fp_10657 fl_10657.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10657 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10657 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10657.

Lemma collineation_10658 : is_collineation fp_10658 fl_10658.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10658 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10658 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10658.

Lemma collineation_10659 : is_collineation fp_10659 fl_10659.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10659 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10659 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10659.

Lemma collineation_10660 : is_collineation fp_10660 fl_10660.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10660 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10660 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10660.

Lemma collineation_10661 : is_collineation fp_10661 fl_10661.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10661 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10661 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10661.

Lemma collineation_10662 : is_collineation fp_10662 fl_10662.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10662 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10662 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10662.

Lemma collineation_10663 : is_collineation fp_10663 fl_10663.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10663 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10663 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10663.

Lemma collineation_10664 : is_collineation fp_10664 fl_10664.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10664 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10664 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10664.

Lemma collineation_10665 : is_collineation fp_10665 fl_10665.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10665 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10665 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10665.

Lemma collineation_10666 : is_collineation fp_10666 fl_10666.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10666 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10666 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10666.

Lemma collineation_10667 : is_collineation fp_10667 fl_10667.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10667 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10667 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10667.

Lemma collineation_10668 : is_collineation fp_10668 fl_10668.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10668 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10668 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10668.

Lemma collineation_10669 : is_collineation fp_10669 fl_10669.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10669 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10669 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10669.

Lemma collineation_10670 : is_collineation fp_10670 fl_10670.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10670 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10670 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10670.

Lemma collineation_10671 : is_collineation fp_10671 fl_10671.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10671 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10671 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10671.

Lemma collineation_10672 : is_collineation fp_10672 fl_10672.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10672 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10672 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10672.

Lemma collineation_10673 : is_collineation fp_10673 fl_10673.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10673 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10673 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10673.

Lemma collineation_10674 : is_collineation fp_10674 fl_10674.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10674 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10674 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10674.

Lemma collineation_10675 : is_collineation fp_10675 fl_10675.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10675 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10675 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10675.

Lemma collineation_10676 : is_collineation fp_10676 fl_10676.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10676 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10676 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10676.

Lemma collineation_10677 : is_collineation fp_10677 fl_10677.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10677 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10677 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10677.

Lemma collineation_10678 : is_collineation fp_10678 fl_10678.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10678 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10678 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10678.

Lemma collineation_10679 : is_collineation fp_10679 fl_10679.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10679 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10679 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10679.

Lemma collineation_10680 : is_collineation fp_10680 fl_10680.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10680 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10680 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10680.

Lemma collineation_10681 : is_collineation fp_10681 fl_10681.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10681 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10681 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10681.

Lemma collineation_10682 : is_collineation fp_10682 fl_10682.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10682 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10682 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10682.

Lemma collineation_10683 : is_collineation fp_10683 fl_10683.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10683 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10683 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10683.

Lemma collineation_10684 : is_collineation fp_10684 fl_10684.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10684 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10684 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10684.

Lemma collineation_10685 : is_collineation fp_10685 fl_10685.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10685 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10685 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10685.

Lemma collineation_10686 : is_collineation fp_10686 fl_10686.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10686 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10686 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10686.

Lemma collineation_10687 : is_collineation fp_10687 fl_10687.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10687 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10687 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10687.

Lemma collineation_10688 : is_collineation fp_10688 fl_10688.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10688 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10688 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10688.

Lemma collineation_10689 : is_collineation fp_10689 fl_10689.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10689 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10689 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10689.

Lemma collineation_10690 : is_collineation fp_10690 fl_10690.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10690 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10690 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10690.

Lemma collineation_10691 : is_collineation fp_10691 fl_10691.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10691 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10691 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10691.

Lemma collineation_10692 : is_collineation fp_10692 fl_10692.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10692 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10692 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10692.

Lemma collineation_10693 : is_collineation fp_10693 fl_10693.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10693 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10693 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10693.

Lemma collineation_10694 : is_collineation fp_10694 fl_10694.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10694 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10694 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10694.

Lemma collineation_10695 : is_collineation fp_10695 fl_10695.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10695 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10695 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10695.

Lemma collineation_10696 : is_collineation fp_10696 fl_10696.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10696 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10696 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10696.

Lemma collineation_10697 : is_collineation fp_10697 fl_10697.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10697 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10697 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10697.

Lemma collineation_10698 : is_collineation fp_10698 fl_10698.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10698 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10698 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10698.

Lemma collineation_10699 : is_collineation fp_10699 fl_10699.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10699 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10699 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10699.

Lemma collineation_10700 : is_collineation fp_10700 fl_10700.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10700 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10700 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10700.

Lemma collineation_10701 : is_collineation fp_10701 fl_10701.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10701 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10701 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10701.

Lemma collineation_10702 : is_collineation fp_10702 fl_10702.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10702 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10702 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10702.

Lemma collineation_10703 : is_collineation fp_10703 fl_10703.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10703 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10703 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10703.

Lemma collineation_10704 : is_collineation fp_10704 fl_10704.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10704 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10704 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10704.

Lemma collineation_10705 : is_collineation fp_10705 fl_10705.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10705 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10705 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10705.

Lemma collineation_10706 : is_collineation fp_10706 fl_10706.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10706 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10706 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10706.

Lemma collineation_10707 : is_collineation fp_10707 fl_10707.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10707 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10707 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10707.

Lemma collineation_10708 : is_collineation fp_10708 fl_10708.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10708 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10708 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10708.

Lemma collineation_10709 : is_collineation fp_10709 fl_10709.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10709 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10709 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10709.

Lemma collineation_10710 : is_collineation fp_10710 fl_10710.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10710 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10710 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10710.

Lemma collineation_10711 : is_collineation fp_10711 fl_10711.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10711 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10711 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10711.

Lemma collineation_10712 : is_collineation fp_10712 fl_10712.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10712 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10712 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10712.

Lemma collineation_10713 : is_collineation fp_10713 fl_10713.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10713 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10713 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10713.

Lemma collineation_10714 : is_collineation fp_10714 fl_10714.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10714 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10714 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10714.

Lemma collineation_10715 : is_collineation fp_10715 fl_10715.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10715 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10715 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10715.

Lemma collineation_10716 : is_collineation fp_10716 fl_10716.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10716 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10716 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10716.

Lemma collineation_10717 : is_collineation fp_10717 fl_10717.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10717 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10717 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10717.

Lemma collineation_10718 : is_collineation fp_10718 fl_10718.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10718 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10718 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10718.

Lemma collineation_10719 : is_collineation fp_10719 fl_10719.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10719 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10719 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10719.

Lemma collineation_10720 : is_collineation fp_10720 fl_10720.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10720 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10720 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10720.

Lemma collineation_10721 : is_collineation fp_10721 fl_10721.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10721 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10721 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10721.

Lemma collineation_10722 : is_collineation fp_10722 fl_10722.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10722 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10722 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10722.

Lemma collineation_10723 : is_collineation fp_10723 fl_10723.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10723 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10723 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10723.

Lemma collineation_10724 : is_collineation fp_10724 fl_10724.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10724 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10724 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10724.

Lemma collineation_10725 : is_collineation fp_10725 fl_10725.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10725 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10725 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10725.

Lemma collineation_10726 : is_collineation fp_10726 fl_10726.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10726 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10726 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10726.

Lemma collineation_10727 : is_collineation fp_10727 fl_10727.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10727 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10727 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10727.

Lemma collineation_10728 : is_collineation fp_10728 fl_10728.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10728 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10728 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10728.

Lemma collineation_10729 : is_collineation fp_10729 fl_10729.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10729 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10729 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10729.

Lemma collineation_10730 : is_collineation fp_10730 fl_10730.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10730 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10730 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10730.

Lemma collineation_10731 : is_collineation fp_10731 fl_10731.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10731 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10731 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10731.

Lemma collineation_10732 : is_collineation fp_10732 fl_10732.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10732 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10732 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10732.

Lemma collineation_10733 : is_collineation fp_10733 fl_10733.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10733 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10733 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10733.

Lemma collineation_10734 : is_collineation fp_10734 fl_10734.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10734 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10734 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10734.

Lemma collineation_10735 : is_collineation fp_10735 fl_10735.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10735 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10735 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10735.

Lemma collineation_10736 : is_collineation fp_10736 fl_10736.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10736 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10736 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10736.

Lemma collineation_10737 : is_collineation fp_10737 fl_10737.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10737 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10737 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10737.

Lemma collineation_10738 : is_collineation fp_10738 fl_10738.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10738 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10738 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10738.

Lemma collineation_10739 : is_collineation fp_10739 fl_10739.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10739 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10739 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10739.

Lemma collineation_10740 : is_collineation fp_10740 fl_10740.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10740 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10740 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10740.

Lemma collineation_10741 : is_collineation fp_10741 fl_10741.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10741 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10741 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10741.

Lemma collineation_10742 : is_collineation fp_10742 fl_10742.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10742 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10742 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10742.

Lemma collineation_10743 : is_collineation fp_10743 fl_10743.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10743 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10743 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10743.

Lemma collineation_10744 : is_collineation fp_10744 fl_10744.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10744 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10744 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10744.

Lemma collineation_10745 : is_collineation fp_10745 fl_10745.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10745 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10745 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10745.

Lemma collineation_10746 : is_collineation fp_10746 fl_10746.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10746 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10746 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10746.

Lemma collineation_10747 : is_collineation fp_10747 fl_10747.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10747 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10747 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10747.

Lemma collineation_10748 : is_collineation fp_10748 fl_10748.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10748 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10748 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10748.

Lemma collineation_10749 : is_collineation fp_10749 fl_10749.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10749 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10749 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10749.

Lemma collineation_10750 : is_collineation fp_10750 fl_10750.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10750 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10750 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10750.

Lemma collineation_10751 : is_collineation fp_10751 fl_10751.
Proof.
  time (split ;
    [split;
    [intros x y; destruct x; destruct y; intros [=]; apply erefl |
     intros y; exists (inv_fp_10751 y); destruct y; apply erefl]
    | split; [
        split; 
[ intros x y; destruct x; destruct y; intros [=]; apply erefl
        | intros y; exists (inv_fl_10751 y); destruct y; apply erefl]
     | intros x l; destruct x; destruct l;intros H; solve [apply (degen_bool _ H) | apply is_true_true]]]).
Qed.

Check collineation_10751.

Lemma is_col_all_c98 : forall fp fl, In (fp,fl) (all_c98++all_c99++all_c100++all_c101++all_c102++all_c103++all_c104++all_c105++all_c106++all_c107++all_c108++all_c109++all_c110++all_c111) -> is_collineation fp fl.
Proof.
 intros fp fl HIn_S.
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9408 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9409 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9410 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9411 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9412 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9413 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9414 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9415 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9416 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9417 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9418 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9419 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9420 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9421 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9422 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9423 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9424 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9425 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9426 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9427 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9428 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9429 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9430 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9431 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9432 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9433 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9434 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9435 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9436 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9437 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9438 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9439 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9440 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9441 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9442 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9443 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9444 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9445 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9446 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9447 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9448 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9449 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9450 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9451 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9452 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9453 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9454 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9455 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9456 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9457 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9458 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9459 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9460 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9461 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9462 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9463 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9464 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9465 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9466 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9467 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9468 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9469 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9470 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9471 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9472 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9473 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9474 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9475 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9476 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9477 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9478 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9479 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9480 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9481 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9482 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9483 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9484 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9485 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9486 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9487 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9488 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9489 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9490 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9491 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9492 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9493 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9494 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9495 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9496 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9497 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9498 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9499 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9500 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9501 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9502 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9503 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9504 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9505 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9506 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9507 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9508 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9509 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9510 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9511 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9512 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9513 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9514 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9515 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9516 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9517 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9518 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9519 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9520 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9521 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9522 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9523 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9524 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9525 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9526 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9527 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9528 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9529 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9530 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9531 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9532 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9533 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9534 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9535 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9536 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9537 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9538 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9539 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9540 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9541 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9542 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9543 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9544 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9545 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9546 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9547 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9548 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9549 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9550 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9551 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9552 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9553 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9554 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9555 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9556 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9557 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9558 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9559 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9560 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9561 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9562 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9563 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9564 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9565 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9566 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9567 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9568 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9569 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9570 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9571 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9572 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9573 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9574 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9575 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9576 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9577 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9578 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9579 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9580 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9581 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9582 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9583 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9584 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9585 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9586 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9587 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9588 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9589 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9590 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9591 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9592 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9593 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9594 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9595 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9596 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9597 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9598 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9599 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9600 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9601 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9602 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9603 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9604 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9605 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9606 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9607 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9608 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9609 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9610 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9611 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9612 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9613 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9614 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9615 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9616 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9617 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9618 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9619 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9620 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9621 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9622 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9623 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9624 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9625 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9626 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9627 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9628 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9629 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9630 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9631 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9632 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9633 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9634 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9635 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9636 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9637 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9638 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9639 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9640 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9641 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9642 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9643 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9644 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9645 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9646 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9647 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9648 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9649 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9650 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9651 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9652 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9653 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9654 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9655 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9656 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9657 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9658 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9659 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9660 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9661 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9662 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9663 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9664 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9665 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9666 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9667 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9668 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9669 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9670 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9671 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9672 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9673 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9674 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9675 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9676 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9677 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9678 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9679 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9680 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9681 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9682 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9683 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9684 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9685 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9686 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9687 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9688 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9689 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9690 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9691 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9692 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9693 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9694 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9695 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9696 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9697 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9698 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9699 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9700 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9701 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9702 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9703 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9704 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9705 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9706 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9707 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9708 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9709 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9710 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9711 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9712 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9713 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9714 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9715 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9716 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9717 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9718 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9719 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9720 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9721 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9722 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9723 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9724 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9725 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9726 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9727 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9728 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9729 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9730 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9731 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9732 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9733 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9734 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9735 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9736 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9737 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9738 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9739 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9740 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9741 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9742 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9743 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9744 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9745 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9746 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9747 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9748 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9749 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9750 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9751 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9752 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9753 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9754 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9755 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9756 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9757 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9758 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9759 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9760 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9761 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9762 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9763 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9764 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9765 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9766 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9767 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9768 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9769 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9770 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9771 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9772 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9773 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9774 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9775 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9776 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9777 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9778 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9779 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9780 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9781 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9782 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9783 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9784 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9785 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9786 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9787 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9788 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9789 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9790 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9791 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9792 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9793 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9794 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9795 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9796 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9797 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9798 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9799 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9800 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9801 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9802 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9803 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9804 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9805 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9806 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9807 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9808 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9809 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9810 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9811 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9812 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9813 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9814 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9815 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9816 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9817 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9818 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9819 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9820 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9821 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9822 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9823 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9824 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9825 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9826 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9827 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9828 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9829 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9830 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9831 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9832 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9833 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9834 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9835 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9836 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9837 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9838 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9839 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9840 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9841 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9842 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9843 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9844 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9845 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9846 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9847 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9848 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9849 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9850 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9851 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9852 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9853 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9854 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9855 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9856 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9857 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9858 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9859 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9860 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9861 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9862 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9863 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9864 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9865 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9866 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9867 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9868 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9869 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9870 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9871 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9872 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9873 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9874 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9875 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9876 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9877 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9878 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9879 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9880 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9881 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9882 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9883 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9884 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9885 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9886 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9887 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9888 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9889 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9890 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9891 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9892 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9893 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9894 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9895 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9896 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9897 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9898 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9899 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9900 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9901 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9902 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9903 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9904 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9905 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9906 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9907 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9908 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9909 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9910 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9911 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9912 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9913 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9914 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9915 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9916 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9917 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9918 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9919 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9920 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9921 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9922 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9923 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9924 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9925 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9926 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9927 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9928 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9929 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9930 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9931 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9932 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9933 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9934 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9935 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9936 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9937 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9938 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9939 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9940 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9941 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9942 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9943 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9944 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9945 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9946 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9947 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9948 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9949 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9950 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9951 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9952 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9953 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9954 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9955 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9956 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9957 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9958 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9959 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9960 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9961 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9962 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9963 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9964 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9965 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9966 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9967 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9968 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9969 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9970 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9971 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9972 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9973 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9974 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9975 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9976 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9977 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9978 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9979 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9980 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9981 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9982 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9983 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9984 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9985 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9986 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9987 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9988 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9989 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9990 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9991 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9992 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9993 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9994 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9995 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9996 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9997 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9998 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_9999 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10000 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10001 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10002 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10003 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10004 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10005 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10006 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10007 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10008 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10009 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10010 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10011 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10012 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10013 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10014 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10015 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10016 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10017 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10018 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10019 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10020 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10021 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10022 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10023 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10024 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10025 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10026 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10027 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10028 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10029 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10030 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10031 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10032 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10033 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10034 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10035 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10036 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10037 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10038 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10039 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10040 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10041 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10042 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10043 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10044 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10045 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10046 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10047 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10048 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10049 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10050 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10051 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10052 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10053 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10054 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10055 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10056 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10057 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10058 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10059 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10060 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10061 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10062 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10063 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10064 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10065 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10066 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10067 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10068 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10069 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10070 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10071 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10072 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10073 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10074 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10075 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10076 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10077 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10078 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10079 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10080 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10081 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10082 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10083 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10084 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10085 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10086 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10087 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10088 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10089 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10090 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10091 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10092 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10093 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10094 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10095 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10096 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10097 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10098 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10099 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10100 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10101 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10102 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10103 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10104 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10105 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10106 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10107 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10108 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10109 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10110 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10111 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10112 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10113 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10114 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10115 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10116 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10117 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10118 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10119 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10120 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10121 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10122 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10123 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10124 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10125 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10126 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10127 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10128 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10129 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10130 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10131 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10132 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10133 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10134 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10135 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10136 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10137 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10138 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10139 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10140 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10141 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10142 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10143 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10144 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10145 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10146 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10147 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10148 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10149 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10150 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10151 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10152 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10153 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10154 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10155 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10156 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10157 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10158 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10159 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10160 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10161 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10162 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10163 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10164 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10165 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10166 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10167 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10168 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10169 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10170 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10171 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10172 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10173 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10174 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10175 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10176 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10177 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10178 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10179 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10180 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10181 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10182 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10183 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10184 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10185 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10186 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10187 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10188 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10189 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10190 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10191 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10192 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10193 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10194 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10195 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10196 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10197 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10198 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10199 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10200 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10201 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10202 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10203 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10204 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10205 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10206 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10207 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10208 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10209 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10210 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10211 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10212 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10213 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10214 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10215 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10216 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10217 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10218 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10219 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10220 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10221 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10222 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10223 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10224 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10225 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10226 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10227 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10228 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10229 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10230 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10231 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10232 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10233 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10234 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10235 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10236 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10237 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10238 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10239 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10240 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10241 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10242 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10243 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10244 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10245 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10246 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10247 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10248 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10249 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10250 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10251 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10252 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10253 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10254 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10255 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10256 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10257 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10258 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10259 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10260 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10261 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10262 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10263 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10264 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10265 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10266 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10267 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10268 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10269 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10270 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10271 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10272 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10273 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10274 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10275 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10276 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10277 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10278 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10279 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10280 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10281 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10282 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10283 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10284 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10285 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10286 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10287 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10288 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10289 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10290 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10291 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10292 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10293 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10294 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10295 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10296 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10297 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10298 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10299 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10300 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10301 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10302 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10303 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10304 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10305 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10306 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10307 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10308 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10309 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10310 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10311 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10312 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10313 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10314 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10315 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10316 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10317 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10318 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10319 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10320 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10321 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10322 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10323 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10324 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10325 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10326 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10327 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10328 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10329 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10330 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10331 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10332 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10333 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10334 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10335 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10336 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10337 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10338 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10339 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10340 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10341 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10342 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10343 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10344 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10345 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10346 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10347 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10348 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10349 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10350 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10351 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10352 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10353 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10354 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10355 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10356 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10357 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10358 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10359 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10360 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10361 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10362 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10363 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10364 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10365 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10366 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10367 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10368 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10369 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10370 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10371 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10372 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10373 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10374 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10375 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10376 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10377 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10378 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10379 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10380 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10381 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10382 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10383 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10384 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10385 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10386 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10387 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10388 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10389 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10390 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10391 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10392 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10393 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10394 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10395 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10396 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10397 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10398 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10399 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10400 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10401 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10402 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10403 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10404 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10405 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10406 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10407 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10408 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10409 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10410 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10411 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10412 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10413 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10414 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10415 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10416 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10417 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10418 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10419 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10420 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10421 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10422 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10423 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10424 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10425 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10426 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10427 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10428 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10429 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10430 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10431 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10432 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10433 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10434 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10435 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10436 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10437 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10438 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10439 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10440 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10441 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10442 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10443 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10444 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10445 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10446 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10447 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10448 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10449 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10450 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10451 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10452 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10453 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10454 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10455 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10456 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10457 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10458 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10459 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10460 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10461 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10462 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10463 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10464 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10465 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10466 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10467 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10468 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10469 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10470 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10471 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10472 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10473 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10474 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10475 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10476 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10477 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10478 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10479 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10480 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10481 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10482 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10483 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10484 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10485 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10486 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10487 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10488 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10489 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10490 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10491 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10492 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10493 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10494 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10495 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10496 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10497 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10498 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10499 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10500 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10501 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10502 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10503 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10504 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10505 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10506 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10507 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10508 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10509 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10510 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10511 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10512 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10513 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10514 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10515 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10516 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10517 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10518 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10519 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10520 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10521 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10522 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10523 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10524 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10525 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10526 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10527 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10528 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10529 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10530 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10531 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10532 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10533 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10534 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10535 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10536 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10537 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10538 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10539 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10540 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10541 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10542 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10543 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10544 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10545 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10546 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10547 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10548 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10549 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10550 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10551 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10552 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10553 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10554 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10555 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10556 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10557 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10558 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10559 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10560 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10561 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10562 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10563 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10564 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10565 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10566 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10567 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10568 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10569 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10570 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10571 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10572 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10573 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10574 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10575 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10576 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10577 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10578 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10579 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10580 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10581 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10582 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10583 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10584 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10585 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10586 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10587 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10588 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10589 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10590 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10591 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10592 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10593 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10594 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10595 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10596 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10597 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10598 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10599 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10600 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10601 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10602 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10603 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10604 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10605 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10606 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10607 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10608 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10609 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10610 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10611 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10612 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10613 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10614 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10615 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10616 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10617 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10618 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10619 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10620 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10621 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10622 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10623 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10624 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10625 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10626 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10627 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10628 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10629 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10630 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10631 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10632 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10633 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10634 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10635 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10636 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10637 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10638 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10639 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10640 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10641 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10642 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10643 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10644 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10645 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10646 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10647 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10648 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10649 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10650 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10651 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10652 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10653 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10654 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10655 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10656 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10657 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10658 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10659 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10660 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10661 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10662 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10663 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10664 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10665 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10666 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10667 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10668 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10669 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10670 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10671 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10672 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10673 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10674 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10675 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10676 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10677 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10678 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10679 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10680 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10681 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10682 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10683 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10684 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10685 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10686 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10687 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10688 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10689 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10690 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10691 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10692 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10693 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10694 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10695 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10696 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10697 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10698 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10699 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10700 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10701 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10702 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10703 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10704 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10705 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10706 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10707 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10708 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10709 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10710 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10711 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10712 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10713 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10714 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10715 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10716 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10717 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10718 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10719 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10720 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10721 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10722 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10723 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10724 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10725 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10726 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10727 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10728 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10729 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10730 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10731 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10732 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10733 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10734 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10735 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10736 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10737 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10738 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10739 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10740 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10741 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10742 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10743 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10744 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10745 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10746 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10747 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10748 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10749 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10750 | idtac].
 destruct HIn_S as [HeqL | HIn_S]; [inversion HeqL; subst fp;subst fl; apply collineation_10751 | idtac].
 destruct (in_nil HIn_S).
Qed.

