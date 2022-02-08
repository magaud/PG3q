Require Import ssreflect ssrfun ssrbool.
Require Import Generic.lemmas Generic.wlog Generic.modulo56.
Require Import PG32.pg32_inductive PG32.pg32_spreads_packings.

Require Import Lia.
Require Import Lists.List.
Import ListNotations.

Ltac solve_surjP :=
  solve [
             exists P0; apply erefl |
             exists P1; apply erefl |
             exists P2; apply erefl |
             exists P3; apply erefl |
             exists P4; apply erefl |
             exists P5; apply erefl |
             exists P6; apply erefl |
             exists P7; apply erefl |
             exists P8; apply erefl |
             exists P9; apply erefl |
             exists P10; apply erefl |
             exists P11; apply erefl |
             exists P12; apply erefl |
             exists P13; apply erefl |
             exists P14; apply erefl ].

Ltac solve_surjL :=
  solve [
             exists L0; apply erefl |
             exists L1; apply erefl |
             exists L2; apply erefl |
             exists L3; apply erefl |
             exists L4; apply erefl |
             exists L5; apply erefl |
             exists L6; apply erefl |
             exists L7; apply erefl |
             exists L8; apply erefl |
             exists L9; apply erefl |
             exists L10; apply erefl |
             exists L11; apply erefl |
             exists L12; apply erefl |
             exists L13; apply erefl |
             exists L14; apply erefl | 
             exists L15; apply erefl |
             exists L16; apply erefl |
             exists L17; apply erefl |
             exists L18; apply erefl |
             exists L19; apply erefl |
             exists L20; apply erefl |
             exists L21; apply erefl |
             exists L22; apply erefl |
             exists L23; apply erefl |
             exists L24; apply erefl |
             exists L25; apply erefl |
             exists L26; apply erefl |
             exists L27; apply erefl |
             exists L28; apply erefl |
             exists L29; apply erefl |
             exists L30; apply erefl |
             exists L31; apply erefl |
             exists L32; apply erefl |
             exists L33; apply erefl |
             exists L34; apply erefl
    ].

Ltac is_col' := split;
                [ split; [
                          let x:= fresh in let y:=fresh in
                                           intros x y;
                                           destruct x; destruct y; intros [=]; apply erefl |
                          let y:= fresh in intros y; destruct y; solve_surjP]
    | 
    split; [
      split; [ let x:= fresh in let y:=fresh in intros x y; destruct x; destruct y; intros [=]; apply erefl | 
                let y:= fresh in intros y; destruct y; solve_surjL] | 
      intros x l; destruct x; destruct l;
      let H := fresh in intros H; solve [apply (degen_bool _ H) | apply is_true_true]]].
