Require Import ssreflect ssrfun ssrbool.
Require Import Generic.lemmas Generic.wlog Generic.modulo56.
Require Import PG32.pg32_inductive PG32.pg32_spreads_packings.

Require Import Lia.
Require Import Lists.List.
Import ListNotations.

(* all collineations from the n^th to (n+1)^th element of the list of spreads *)

(* s0 : l0 : | p0 p1 p2 | l19 : | p3 p10 p14 | l24 : | p4 p8 p11 | l28 : | p5 p7 p13 | l33 : | p6 p9 p12 | -> 
   s1 : l0 : | p0 p1 p2 | l19 : | p3 p10 p14 | l26 : | p4 p7 p12 | l29 : | p5 p9 p11 | l32 : | p6 p8 p13 |  *)
Definition fp0_1 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P11 | P8 => P12 | P9 => P13 | P10 => P14 | P11 => P7 | P12 => P8 | P13 => P9 | P14 => P10 end.
Definition fl0_1 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L5 | L4 => L6 | L5 => L3 | L6 => L4 | L7 => L7 | L8 => L9 | L9 => L8 | L10 => L11 | L11 => L10 | L12 => L12 | L13 => L14 | L14 => L13 | L15 => L15 | L16 => L18 | L17 => L17 | L18 => L16 | L19 => L19 | L20 => L20 | L21 => L21 | L22 => L22 | L23 => L25 | L24 => L26 | L25 => L23 | L26 => L24 | L27 => L30 | L28 => L29 | L29 => L28 | L30 => L27 | L31 => L34 | L32 => L33 | L33 => L32 | L34 => L31 end.

(* s1 : l0 : | p0 p1 p2 | l19 : | p3 p10 p14 | l26 : | p4 p7 p12 | l29 : | p5 p9 p11 | l32 : | p6 p8 p13 | -> 
   s2 : l0 : | p0 p1 p2 | l20 : | p3 p8 p12 | l23 : | p4 p9 p14 | l28 : | p5 p7 p13 | l34 : | p6 p10 p11 |  *)
Definition fp1_2 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P9 | P8 => P10 | P9 => P7 | P10 => P8 | P11 => P13 | P12 => P14 | P13 => P11 | P14 => P12 end.
Definition fl1_2 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L4 | L4 => L3 | L5 => L6 | L6 => L5 | L7 => L7 | L8 => L8 | L9 => L9 | L10 => L10 | L11 => L11 | L12 => L12 | L13 => L18 | L14 => L16 | L15 => L15 | L16 => L14 | L17 => L17 | L18 => L13 | L19 => L20 | L20 => L19 | L21 => L22 | L22 => L21 | L23 => L26 | L24 => L25 | L25 => L24 | L26 => L23 | L27 => L30 | L28 => L29 | L29 => L28 | L30 => L27 | L31 => L33 | L32 => L34 | L33 => L31 | L34 => L32 end.

(* s2 : l0 : | p0 p1 p2 | l20 : | p3 p8 p12 | l23 : | p4 p9 p14 | l28 : | p5 p7 p13 | l34 : | p6 p10 p11 | -> 
   s3 : l0 : | p0 p1 p2 | l20 : | p3 p8 p12 | l25 : | p4 p10 p13 | l29 : | p5 p9 p11 | l31 : | p6 p7 p14 |  *)
Definition fp2_3 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P11 | P8 => P12 | P9 => P13 | P10 => P14 | P11 => P7 | P12 => P8 | P13 => P9 | P14 => P10 end.
Definition fl2_3 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L5 | L4 => L6 | L5 => L3 | L6 => L4 | L7 => L7 | L8 => L9 | L9 => L8 | L10 => L11 | L11 => L10 | L12 => L12 | L13 => L14 | L14 => L13 | L15 => L15 | L16 => L18 | L17 => L17 | L18 => L16 | L19 => L19 | L20 => L20 | L21 => L21 | L22 => L22 | L23 => L25 | L24 => L26 | L25 => L23 | L26 => L24 | L27 => L30 | L28 => L29 | L29 => L28 | L30 => L27 | L31 => L34 | L32 => L33 | L33 => L32 | L34 => L31 end.

(* s3 : l0 : | p0 p1 p2 | l20 : | p3 p8 p12 | l25 : | p4 p10 p13 | l29 : | p5 p9 p11 | l31 : | p6 p7 p14 | -> 
   s4 : l0 : | p0 p1 p2 | l21 : | p3 p9 p13 | l24 : | p4 p8 p11 | l30 : | p5 p10 p12 | l31 : | p6 p7 p14 |  *)
Definition fp3_4 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P14 | P8 => P13 | P9 => P12 | P10 => P11 | P11 => P10 | P12 => P9 | P13 => P8 | P14 => P7 end.
Definition fl3_4 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L6 | L4 => L5 | L5 => L4 | L6 => L3 | L7 => L7 | L8 => L11 | L9 => L10 | L10 => L9 | L11 => L8 | L12 => L12 | L13 => L14 | L14 => L13 | L15 => L15 | L16 => L18 | L17 => L17 | L18 => L16 | L19 => L22 | L20 => L21 | L21 => L20 | L22 => L19 | L23 => L26 | L24 => L25 | L25 => L24 | L26 => L23 | L27 => L28 | L28 => L27 | L29 => L30 | L30 => L29 | L31 => L31 | L32 => L32 | L33 => L33 | L34 => L34 end.

(* s4 : l0 : | p0 p1 p2 | l21 : | p3 p9 p13 | l24 : | p4 p8 p11 | l30 : | p5 p10 p12 | l31 : | p6 p7 p14 | -> 
   s5 : l0 : | p0 p1 p2 | l21 : | p3 p9 p13 | l26 : | p4 p7 p12 | l27 : | p5 p8 p14 | l34 : | p6 p10 p11 |  *)
Definition fp4_5 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P11 | P8 => P12 | P9 => P13 | P10 => P14 | P11 => P7 | P12 => P8 | P13 => P9 | P14 => P10 end.
Definition fl4_5 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L5 | L4 => L6 | L5 => L3 | L6 => L4 | L7 => L7 | L8 => L9 | L9 => L8 | L10 => L11 | L11 => L10 | L12 => L12 | L13 => L14 | L14 => L13 | L15 => L15 | L16 => L18 | L17 => L17 | L18 => L16 | L19 => L19 | L20 => L20 | L21 => L21 | L22 => L22 | L23 => L25 | L24 => L26 | L25 => L23 | L26 => L24 | L27 => L30 | L28 => L29 | L29 => L28 | L30 => L27 | L31 => L34 | L32 => L33 | L33 => L32 | L34 => L31 end.

(* s5 : l0 : | p0 p1 p2 | l21 : | p3 p9 p13 | l26 : | p4 p7 p12 | l27 : | p5 p8 p14 | l34 : | p6 p10 p11 | -> 
   s6 : l0 : | p0 p1 p2 | l22 : | p3 p7 p11 | l23 : | p4 p9 p14 | l30 : | p5 p10 p12 | l32 : | p6 p8 p13 |  *)
Definition fp5_6 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P9 | P8 => P10 | P9 => P7 | P10 => P8 | P11 => P13 | P12 => P14 | P13 => P11 | P14 => P12 end.
Definition fl5_6 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L4 | L4 => L3 | L5 => L6 | L6 => L5 | L7 => L7 | L8 => L8 | L9 => L9 | L10 => L10 | L11 => L11 | L12 => L12 | L13 => L18 | L14 => L16 | L15 => L15 | L16 => L14 | L17 => L17 | L18 => L13 | L19 => L20 | L20 => L19 | L21 => L22 | L22 => L21 | L23 => L26 | L24 => L25 | L25 => L24 | L26 => L23 | L27 => L30 | L28 => L29 | L29 => L28 | L30 => L27 | L31 => L33 | L32 => L34 | L33 => L31 | L34 => L32 end.

(* s6 : l0 : | p0 p1 p2 | l22 : | p3 p7 p11 | l23 : | p4 p9 p14 | l30 : | p5 p10 p12 | l32 : | p6 p8 p13 | -> 
   s7 : l0 : | p0 p1 p2 | l22 : | p3 p7 p11 | l25 : | p4 p10 p13 | l27 : | p5 p8 p14 | l33 : | p6 p9 p12 |  *)
Definition fp6_7 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P11 | P8 => P12 | P9 => P13 | P10 => P14 | P11 => P7 | P12 => P8 | P13 => P9 | P14 => P10 end.
Definition fl6_7 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L5 | L4 => L6 | L5 => L3 | L6 => L4 | L7 => L7 | L8 => L9 | L9 => L8 | L10 => L11 | L11 => L10 | L12 => L12 | L13 => L14 | L14 => L13 | L15 => L15 | L16 => L18 | L17 => L17 | L18 => L16 | L19 => L19 | L20 => L20 | L21 => L21 | L22 => L22 | L23 => L25 | L24 => L26 | L25 => L23 | L26 => L24 | L27 => L30 | L28 => L29 | L29 => L28 | L30 => L27 | L31 => L34 | L32 => L33 | L33 => L32 | L34 => L31 end.

(* s7 : l0 : | p0 p1 p2 | l22 : | p3 p7 p11 | l25 : | p4 p10 p13 | l27 : | p5 p8 p14 | l33 : | p6 p9 p12 | -> 
   s8 : l1 : | p0 p3 p4 | l8 : | p1 p8 p10 | l14 : | p2 p11 p14 | l28 : | p5 p7 p13 | l33 : | p6 p9 p12 |  *)
Definition fp7_8 (p:Point) := match p with P0 => P0 | P1 => P3 | P2 => P4 | P3 => P1 | P4 => P2 | P5 => P5 | P6 => P6 | P7 => P8 | P8 => P7 | P9 => P12 | P10 => P11 | P11 => P10 | P12 => P9 | P13 => P14 | P14 => P13 end.
Definition fl7_8 (l:Line) := match l with L0 => L1 | L1 => L0 | L2 => L2 | L3 => L3 | L4 => L5 | L5 => L4 | L6 => L6 | L7 => L15 | L8 => L22 | L9 => L21 | L10 => L20 | L11 => L19 | L12 => L12 | L13 => L24 | L14 => L25 | L15 => L7 | L16 => L23 | L17 => L17 | L18 => L26 | L19 => L11 | L20 => L10 | L21 => L9 | L22 => L8 | L23 => L16 | L24 => L13 | L25 => L14 | L26 => L18 | L27 => L28 | L28 => L27 | L29 => L30 | L30 => L29 | L31 => L32 | L32 => L31 | L33 => L33 | L34 => L34 end.

(* s8 : l1 : | p0 p3 p4 | l8 : | p1 p8 p10 | l14 : | p2 p11 p14 | l28 : | p5 p7 p13 | l33 : | p6 p9 p12 | -> 
   s9 : l1 : | p0 p3 p4 | l8 : | p1 p8 p10 | l16 : | p2 p12 p13 | l29 : | p5 p9 p11 | l31 : | p6 p7 p14 |  *)
Definition fp8_9 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P9 | P8 => P10 | P9 => P7 | P10 => P8 | P11 => P13 | P12 => P14 | P13 => P11 | P14 => P12 end.
Definition fl8_9 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L4 | L4 => L3 | L5 => L6 | L6 => L5 | L7 => L7 | L8 => L8 | L9 => L9 | L10 => L10 | L11 => L11 | L12 => L12 | L13 => L18 | L14 => L16 | L15 => L15 | L16 => L14 | L17 => L17 | L18 => L13 | L19 => L20 | L20 => L19 | L21 => L22 | L22 => L21 | L23 => L26 | L24 => L25 | L25 => L24 | L26 => L23 | L27 => L30 | L28 => L29 | L29 => L28 | L30 => L27 | L31 => L33 | L32 => L34 | L33 => L31 | L34 => L32 end.

(* s9 : l1 : | p0 p3 p4 | l8 : | p1 p8 p10 | l16 : | p2 p12 p13 | l29 : | p5 p9 p11 | l31 : | p6 p7 p14 | -> 
   s10 : l1 : | p0 p3 p4 | l9 : | p1 p12 p14 | l13 : | p2 p7 p10 | l29 : | p5 p9 p11 | l32 : | p6 p8 p13 |  *)
Definition fp9_10 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P13 | P8 => P14 | P9 => P11 | P10 => P12 | P11 => P9 | P12 => P10 | P13 => P7 | P14 => P8 end.
Definition fl9_10 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L6 | L4 => L5 | L5 => L4 | L6 => L3 | L7 => L7 | L8 => L9 | L9 => L8 | L10 => L11 | L11 => L10 | L12 => L12 | L13 => L16 | L14 => L18 | L15 => L15 | L16 => L13 | L17 => L17 | L18 => L14 | L19 => L20 | L20 => L19 | L21 => L22 | L22 => L21 | L23 => L24 | L24 => L23 | L25 => L26 | L26 => L25 | L27 => L27 | L28 => L28 | L29 => L29 | L30 => L30 | L31 => L32 | L32 => L31 | L33 => L34 | L34 => L33 end.

(* s10 : l1 : | p0 p3 p4 | l9 : | p1 p12 p14 | l13 : | p2 p7 p10 | l29 : | p5 p9 p11 | l32 : | p6 p8 p13 | -> 
   s11 : l1 : | p0 p3 p4 | l9 : | p1 p12 p14 | l18 : | p2 p8 p9 | l28 : | p5 p7 p13 | l34 : | p6 p10 p11 |  *)
Definition fp10_11 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P9 | P8 => P10 | P9 => P7 | P10 => P8 | P11 => P13 | P12 => P14 | P13 => P11 | P14 => P12 end.
Definition fl10_11 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L4 | L4 => L3 | L5 => L6 | L6 => L5 | L7 => L7 | L8 => L8 | L9 => L9 | L10 => L10 | L11 => L11 | L12 => L12 | L13 => L18 | L14 => L16 | L15 => L15 | L16 => L14 | L17 => L17 | L18 => L13 | L19 => L20 | L20 => L19 | L21 => L22 | L22 => L21 | L23 => L26 | L24 => L25 | L25 => L24 | L26 => L23 | L27 => L30 | L28 => L29 | L29 => L28 | L30 => L27 | L31 => L33 | L32 => L34 | L33 => L31 | L34 => L32 end.

(* s11 : l1 : | p0 p3 p4 | l9 : | p1 p12 p14 | l18 : | p2 p8 p9 | l28 : | p5 p7 p13 | l34 : | p6 p10 p11 | -> 
   s12 : l1 : | p0 p3 p4 | l10 : | p1 p7 p9 | l14 : | p2 p11 p14 | l30 : | p5 p10 p12 | l32 : | p6 p8 p13 |  *)
Definition fp11_12 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P12 | P8 => P11 | P9 => P14 | P10 => P13 | P11 => P8 | P12 => P7 | P13 => P10 | P14 => P9 end.
Definition fl11_12 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L5 | L4 => L6 | L5 => L3 | L6 => L4 | L7 => L7 | L8 => L11 | L9 => L10 | L10 => L9 | L11 => L8 | L12 => L12 | L13 => L16 | L14 => L18 | L15 => L15 | L16 => L13 | L17 => L17 | L18 => L14 | L19 => L21 | L20 => L22 | L21 => L19 | L22 => L20 | L23 => L23 | L24 => L24 | L25 => L25 | L26 => L26 | L27 => L29 | L28 => L30 | L29 => L27 | L30 => L28 | L31 => L33 | L32 => L34 | L33 => L31 | L34 => L32 end.

(* s12 : l1 : | p0 p3 p4 | l10 : | p1 p7 p9 | l14 : | p2 p11 p14 | l30 : | p5 p10 p12 | l32 : | p6 p8 p13 | -> 
   s13 : l1 : | p0 p3 p4 | l10 : | p1 p7 p9 | l16 : | p2 p12 p13 | l27 : | p5 p8 p14 | l34 : | p6 p10 p11 |  *)
Definition fp12_13 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P9 | P8 => P10 | P9 => P7 | P10 => P8 | P11 => P13 | P12 => P14 | P13 => P11 | P14 => P12 end.
Definition fl12_13 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L4 | L4 => L3 | L5 => L6 | L6 => L5 | L7 => L7 | L8 => L8 | L9 => L9 | L10 => L10 | L11 => L11 | L12 => L12 | L13 => L18 | L14 => L16 | L15 => L15 | L16 => L14 | L17 => L17 | L18 => L13 | L19 => L20 | L20 => L19 | L21 => L22 | L22 => L21 | L23 => L26 | L24 => L25 | L25 => L24 | L26 => L23 | L27 => L30 | L28 => L29 | L29 => L28 | L30 => L27 | L31 => L33 | L32 => L34 | L33 => L31 | L34 => L32 end.

(* s13 : l1 : | p0 p3 p4 | l10 : | p1 p7 p9 | l16 : | p2 p12 p13 | l27 : | p5 p8 p14 | l34 : | p6 p10 p11 | -> 
   s14 : l1 : | p0 p3 p4 | l11 : | p1 p13 p11 | l13 : | p2 p7 p10 | l27 : | p5 p8 p14 | l33 : | p6 p9 p12 |  *)
Definition fp13_14 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P13 | P8 => P14 | P9 => P11 | P10 => P12 | P11 => P9 | P12 => P10 | P13 => P7 | P14 => P8 end.
Definition fl13_14 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L6 | L4 => L5 | L5 => L4 | L6 => L3 | L7 => L7 | L8 => L9 | L9 => L8 | L10 => L11 | L11 => L10 | L12 => L12 | L13 => L16 | L14 => L18 | L15 => L15 | L16 => L13 | L17 => L17 | L18 => L14 | L19 => L20 | L20 => L19 | L21 => L22 | L22 => L21 | L23 => L24 | L24 => L23 | L25 => L26 | L26 => L25 | L27 => L27 | L28 => L28 | L29 => L29 | L30 => L30 | L31 => L32 | L32 => L31 | L33 => L34 | L34 => L33 end.

(* s14 : l1 : | p0 p3 p4 | l11 : | p1 p13 p11 | l13 : | p2 p7 p10 | l27 : | p5 p8 p14 | l33 : | p6 p9 p12 | -> 
   s15 : l1 : | p0 p3 p4 | l11 : | p1 p13 p11 | l18 : | p2 p8 p9 | l30 : | p5 p10 p12 | l31 : | p6 p7 p14 |  *)
Definition fp14_15 (p:Point) := match p with P0 => P3 | P1 => P13 | P2 => P9 | P3 => P4 | P4 => P0 | P5 => P10 | P6 => P14 | P7 => P8 | P8 => P12 | P9 => P6 | P10 => P2 | P11 => P11 | P12 => P7 | P13 => P1 | P14 => P5 end.
Definition fl14_15 (l:Line) := match l with L0 => L21 | L1 => L1 | L2 => L19 | L3 => L20 | L4 => L15 | L5 => L22 | L6 => L12 | L7 => L6 | L8 => L16 | L9 => L28 | L10 => L32 | L11 => L11 | L12 => L25 | L13 => L18 | L14 => L29 | L15 => L23 | L16 => L10 | L17 => L4 | L18 => L33 | L19 => L17 | L20 => L26 | L21 => L7 | L22 => L24 | L23 => L2 | L24 => L5 | L25 => L0 | L26 => L3 | L27 => L30 | L28 => L8 | L29 => L34 | L30 => L13 | L31 => L27 | L32 => L9 | L33 => L31 | L34 => L14 end.

(* s15 : l1 : | p0 p3 p4 | l11 : | p1 p13 p11 | l18 : | p2 p8 p9 | l30 : | p5 p10 p12 | l31 : | p6 p7 p14 | -> 
   s16 : l2 : | p0 p5 p6 | l8 : | p1 p8 p10 | l14 : | p2 p11 p14 | l21 : | p3 p9 p13 | l26 : | p4 p7 p12 |  *)
Definition fp15_16 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P5 | P4 => P6 | P5 => P3 | P6 => P4 | P7 => P12 | P8 => P11 | P9 => P14 | P10 => P13 | P11 => P10 | P12 => P9 | P13 => P8 | P14 => P7 end.
Definition fl15_16 (l:Line) := match l with L0 => L0 | L1 => L2 | L2 => L1 | L3 => L5 | L4 => L6 | L5 => L4 | L6 => L3 | L7 => L7 | L8 => L11 | L9 => L10 | L10 => L9 | L11 => L8 | L12 => L12 | L13 => L16 | L14 => L13 | L15 => L17 | L16 => L18 | L17 => L15 | L18 => L14 | L19 => L28 | L20 => L29 | L21 => L27 | L22 => L30 | L23 => L31 | L24 => L34 | L25 => L32 | L26 => L33 | L27 => L22 | L28 => L20 | L29 => L19 | L30 => L21 | L31 => L26 | L32 => L24 | L33 => L23 | L34 => L25 end.

(* s16 : l2 : | p0 p5 p6 | l8 : | p1 p8 p10 | l14 : | p2 p11 p14 | l21 : | p3 p9 p13 | l26 : | p4 p7 p12 | -> 
   s17 : l2 : | p0 p5 p6 | l8 : | p1 p8 p10 | l16 : | p2 p12 p13 | l22 : | p3 p7 p11 | l23 : | p4 p9 p14 |  *)
Definition fp16_17 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P9 | P8 => P10 | P9 => P7 | P10 => P8 | P11 => P13 | P12 => P14 | P13 => P11 | P14 => P12 end.
Definition fl16_17 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L4 | L4 => L3 | L5 => L6 | L6 => L5 | L7 => L7 | L8 => L8 | L9 => L9 | L10 => L10 | L11 => L11 | L12 => L12 | L13 => L18 | L14 => L16 | L15 => L15 | L16 => L14 | L17 => L17 | L18 => L13 | L19 => L20 | L20 => L19 | L21 => L22 | L22 => L21 | L23 => L26 | L24 => L25 | L25 => L24 | L26 => L23 | L27 => L30 | L28 => L29 | L29 => L28 | L30 => L27 | L31 => L33 | L32 => L34 | L33 => L31 | L34 => L32 end.

(* s17 : l2 : | p0 p5 p6 | l8 : | p1 p8 p10 | l16 : | p2 p12 p13 | l22 : | p3 p7 p11 | l23 : | p4 p9 p14 | -> 
   s18 : l2 : | p0 p5 p6 | l9 : | p1 p12 p14 | l13 : | p2 p7 p10 | l21 : | p3 p9 p13 | l24 : | p4 p8 p11 |  *)
Definition fp17_18 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P13 | P8 => P14 | P9 => P11 | P10 => P12 | P11 => P9 | P12 => P10 | P13 => P7 | P14 => P8 end.
Definition fl17_18 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L6 | L4 => L5 | L5 => L4 | L6 => L3 | L7 => L7 | L8 => L9 | L9 => L8 | L10 => L11 | L11 => L10 | L12 => L12 | L13 => L16 | L14 => L18 | L15 => L15 | L16 => L13 | L17 => L17 | L18 => L14 | L19 => L20 | L20 => L19 | L21 => L22 | L22 => L21 | L23 => L24 | L24 => L23 | L25 => L26 | L26 => L25 | L27 => L27 | L28 => L28 | L29 => L29 | L30 => L30 | L31 => L32 | L32 => L31 | L33 => L34 | L34 => L33 end.

(* s18 : l2 : | p0 p5 p6 | l9 : | p1 p12 p14 | l13 : | p2 p7 p10 | l21 : | p3 p9 p13 | l24 : | p4 p8 p11 | -> 
   s19 : l2 : | p0 p5 p6 | l9 : | p1 p12 p14 | l18 : | p2 p8 p9 | l22 : | p3 p7 p11 | l25 : | p4 p10 p13 |  *)
Definition fp18_19 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P9 | P8 => P10 | P9 => P7 | P10 => P8 | P11 => P13 | P12 => P14 | P13 => P11 | P14 => P12 end.
Definition fl18_19 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L4 | L4 => L3 | L5 => L6 | L6 => L5 | L7 => L7 | L8 => L8 | L9 => L9 | L10 => L10 | L11 => L11 | L12 => L12 | L13 => L18 | L14 => L16 | L15 => L15 | L16 => L14 | L17 => L17 | L18 => L13 | L19 => L20 | L20 => L19 | L21 => L22 | L22 => L21 | L23 => L26 | L24 => L25 | L25 => L24 | L26 => L23 | L27 => L30 | L28 => L29 | L29 => L28 | L30 => L27 | L31 => L33 | L32 => L34 | L33 => L31 | L34 => L32 end.

(* s19 : l2 : | p0 p5 p6 | l9 : | p1 p12 p14 | l18 : | p2 p8 p9 | l22 : | p3 p7 p11 | l25 : | p4 p10 p13 | -> 
   s20 : l2 : | p0 p5 p6 | l10 : | p1 p7 p9 | l14 : | p2 p11 p14 | l20 : | p3 p8 p12 | l25 : | p4 p10 p13 |  *)
Definition fp19_20 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P12 | P8 => P11 | P9 => P14 | P10 => P13 | P11 => P8 | P12 => P7 | P13 => P10 | P14 => P9 end.
Definition fl19_20 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L5 | L4 => L6 | L5 => L3 | L6 => L4 | L7 => L7 | L8 => L11 | L9 => L10 | L10 => L9 | L11 => L8 | L12 => L12 | L13 => L16 | L14 => L18 | L15 => L15 | L16 => L13 | L17 => L17 | L18 => L14 | L19 => L21 | L20 => L22 | L21 => L19 | L22 => L20 | L23 => L23 | L24 => L24 | L25 => L25 | L26 => L26 | L27 => L29 | L28 => L30 | L29 => L27 | L30 => L28 | L31 => L33 | L32 => L34 | L33 => L31 | L34 => L32 end.

(* s20 : l2 : | p0 p5 p6 | l10 : | p1 p7 p9 | l14 : | p2 p11 p14 | l20 : | p3 p8 p12 | l25 : | p4 p10 p13 | -> 
   s21 : l2 : | p0 p5 p6 | l10 : | p1 p7 p9 | l16 : | p2 p12 p13 | l19 : | p3 p10 p14 | l24 : | p4 p8 p11 |  *)
Definition fp20_21 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P9 | P8 => P10 | P9 => P7 | P10 => P8 | P11 => P13 | P12 => P14 | P13 => P11 | P14 => P12 end.
Definition fl20_21 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L4 | L4 => L3 | L5 => L6 | L6 => L5 | L7 => L7 | L8 => L8 | L9 => L9 | L10 => L10 | L11 => L11 | L12 => L12 | L13 => L18 | L14 => L16 | L15 => L15 | L16 => L14 | L17 => L17 | L18 => L13 | L19 => L20 | L20 => L19 | L21 => L22 | L22 => L21 | L23 => L26 | L24 => L25 | L25 => L24 | L26 => L23 | L27 => L30 | L28 => L29 | L29 => L28 | L30 => L27 | L31 => L33 | L32 => L34 | L33 => L31 | L34 => L32 end.

(* s21 : l2 : | p0 p5 p6 | l10 : | p1 p7 p9 | l16 : | p2 p12 p13 | l19 : | p3 p10 p14 | l24 : | p4 p8 p11 | -> 
   s22 : l2 : | p0 p5 p6 | l11 : | p1 p13 p11 | l13 : | p2 p7 p10 | l20 : | p3 p8 p12 | l23 : | p4 p9 p14 |  *)
Definition fp21_22 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P13 | P8 => P14 | P9 => P11 | P10 => P12 | P11 => P9 | P12 => P10 | P13 => P7 | P14 => P8 end.
Definition fl21_22 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L6 | L4 => L5 | L5 => L4 | L6 => L3 | L7 => L7 | L8 => L9 | L9 => L8 | L10 => L11 | L11 => L10 | L12 => L12 | L13 => L16 | L14 => L18 | L15 => L15 | L16 => L13 | L17 => L17 | L18 => L14 | L19 => L20 | L20 => L19 | L21 => L22 | L22 => L21 | L23 => L24 | L24 => L23 | L25 => L26 | L26 => L25 | L27 => L27 | L28 => L28 | L29 => L29 | L30 => L30 | L31 => L32 | L32 => L31 | L33 => L34 | L34 => L33 end.

(* s22 : l2 : | p0 p5 p6 | l11 : | p1 p13 p11 | l13 : | p2 p7 p10 | l20 : | p3 p8 p12 | l23 : | p4 p9 p14 | -> 
   s23 : l2 : | p0 p5 p6 | l11 : | p1 p13 p11 | l18 : | p2 p8 p9 | l19 : | p3 p10 p14 | l26 : | p4 p7 p12 |  *)
Definition fp22_23 (p:Point) := match p with P0 => P5 | P1 => P11 | P2 => P9 | P3 => P10 | P4 => P12 | P5 => P6 | P6 => P0 | P7 => P8 | P8 => P14 | P9 => P4 | P10 => P2 | P11 => P1 | P12 => P3 | P13 => P13 | P14 => P7 end.
Definition fl22_23 (l:Line) := match l with L0 => L29 | L1 => L30 | L2 => L2 | L3 => L27 | L4 => L17 | L5 => L12 | L6 => L28 | L7 => L5 | L8 => L14 | L9 => L22 | L10 => L24 | L11 => L11 | L12 => L34 | L13 => L18 | L14 => L10 | L15 => L4 | L16 => L21 | L17 => L33 | L18 => L23 | L19 => L13 | L20 => L19 | L21 => L25 | L22 => L8 | L23 => L26 | L24 => L9 | L25 => L16 | L26 => L20 | L27 => L31 | L28 => L32 | L29 => L7 | L30 => L15 | L31 => L3 | L32 => L6 | L33 => L1 | L34 => L0 end.

(* s23 : l2 : | p0 p5 p6 | l11 : | p1 p13 p11 | l18 : | p2 p8 p9 | l19 : | p3 p10 p14 | l26 : | p4 p7 p12 | -> 
   s24 : l3 : | p0 p7 p8 | l7 : | p1 p4 p6 | l14 : | p2 p11 p14 | l21 : | p3 p9 p13 | l30 : | p5 p10 p12 |  *)
Definition fp23_24 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P9 | P4 => P10 | P5 => P7 | P6 => P8 | P7 => P12 | P8 => P11 | P9 => P14 | P10 => P13 | P11 => P6 | P12 => P5 | P13 => P4 | P14 => P3 end.
Definition fl23_24 (l:Line) := match l with L0 => L0 | L1 => L4 | L2 => L3 | L3 => L5 | L4 => L6 | L5 => L2 | L6 => L1 | L7 => L8 | L8 => L11 | L9 => L12 | L10 => L9 | L11 => L7 | L12 => L10 | L13 => L16 | L14 => L15 | L15 => L18 | L16 => L17 | L17 => L13 | L18 => L14 | L19 => L21 | L20 => L29 | L21 => L23 | L22 => L33 | L23 => L19 | L24 => L34 | L25 => L25 | L26 => L30 | L27 => L22 | L28 => L26 | L29 => L31 | L30 => L28 | L31 => L20 | L32 => L24 | L33 => L27 | L34 => L32 end.

(* s24 : l3 : | p0 p7 p8 | l7 : | p1 p4 p6 | l14 : | p2 p11 p14 | l21 : | p3 p9 p13 | l30 : | p5 p10 p12 | -> 
   s25 : l3 : | p0 p7 p8 | l7 : | p1 p4 p6 | l16 : | p2 p12 p13 | l19 : | p3 p10 p14 | l29 : | p5 p9 p11 |  *)
Definition fp24_25 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P8 | P8 => P7 | P9 => P10 | P10 => P9 | P11 => P12 | P12 => P11 | P13 => P14 | P14 => P13 end.
Definition fl24_25 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L3 | L4 => L4 | L5 => L5 | L6 => L6 | L7 => L7 | L8 => L10 | L9 => L11 | L10 => L8 | L11 => L9 | L12 => L12 | L13 => L18 | L14 => L16 | L15 => L15 | L16 => L14 | L17 => L17 | L18 => L13 | L19 => L21 | L20 => L22 | L21 => L19 | L22 => L20 | L23 => L25 | L24 => L26 | L25 => L23 | L26 => L24 | L27 => L28 | L28 => L27 | L29 => L30 | L30 => L29 | L31 => L32 | L32 => L31 | L33 => L34 | L34 => L33 end.

(* s25 : l3 : | p0 p7 p8 | l7 : | p1 p4 p6 | l16 : | p2 p12 p13 | l19 : | p3 p10 p14 | l29 : | p5 p9 p11 | -> 
   s26 : l3 : | p0 p7 p8 | l9 : | p1 p12 p14 | l15 : | p2 p3 p6 | l25 : | p4 p10 p13 | l29 : | p5 p9 p11 |  *)
Definition fp25_26 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P13 | P4 => P14 | P5 => P11 | P6 => P12 | P7 => P7 | P8 => P8 | P9 => P9 | P10 => P10 | P11 => P5 | P12 => P6 | P13 => P3 | P14 => P4 end.
Definition fl25_26 (l:Line) := match l with L0 => L0 | L1 => L6 | L2 => L5 | L3 => L3 | L4 => L4 | L5 => L2 | L6 => L1 | L7 => L9 | L8 => L8 | L9 => L7 | L10 => L10 | L11 => L12 | L12 => L11 | L13 => L13 | L14 => L17 | L15 => L16 | L16 => L15 | L17 => L14 | L18 => L18 | L19 => L25 | L20 => L32 | L21 => L21 | L22 => L28 | L23 => L23 | L24 => L27 | L25 => L19 | L26 => L31 | L27 => L24 | L28 => L22 | L29 => L29 | L30 => L34 | L31 => L26 | L32 => L20 | L33 => L33 | L34 => L30 end.

(* s26 : l3 : | p0 p7 p8 | l9 : | p1 p12 p14 | l15 : | p2 p3 p6 | l25 : | p4 p10 p13 | l29 : | p5 p9 p11 | -> 
   s27 : l3 : | p0 p7 p8 | l9 : | p1 p12 p14 | l17 : | p2 p4 p5 | l21 : | p3 p9 p13 | l34 : | p6 p10 p11 |  *)
Definition fp26_27 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P4 | P4 => P3 | P5 => P6 | P6 => P5 | P7 => P8 | P8 => P7 | P9 => P10 | P10 => P9 | P11 => P11 | P12 => P12 | P13 => P13 | P14 => P14 end.
Definition fl26_27 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L3 | L4 => L4 | L5 => L5 | L6 => L6 | L7 => L12 | L8 => L10 | L9 => L9 | L10 => L8 | L11 => L11 | L12 => L7 | L13 => L18 | L14 => L14 | L15 => L17 | L16 => L16 | L17 => L15 | L18 => L13 | L19 => L23 | L20 => L26 | L21 => L25 | L22 => L24 | L23 => L19 | L24 => L22 | L25 => L21 | L26 => L20 | L27 => L31 | L28 => L32 | L29 => L34 | L30 => L33 | L31 => L27 | L32 => L28 | L33 => L30 | L34 => L29 end.

(* s27 : l3 : | p0 p7 p8 | l9 : | p1 p12 p14 | l17 : | p2 p4 p5 | l21 : | p3 p9 p13 | l34 : | p6 p10 p11 | -> 
   s28 : l3 : | p0 p7 p8 | l11 : | p1 p13 p11 | l15 : | p2 p3 p6 | l23 : | p4 p9 p14 | l30 : | p5 p10 p12 |  *)
Definition fp27_28 (p:Point) := match p with P0 => P7 | P1 => P11 | P2 => P3 | P3 => P14 | P4 => P6 | P5 => P2 | P6 => P10 | P7 => P8 | P8 => P0 | P9 => P4 | P10 => P12 | P11 => P5 | P12 => P13 | P13 => P9 | P14 => P1 end.
Definition fl27_28 (l:Line) := match l with L0 => L22 | L1 => L31 | L2 => L13 | L3 => L3 | L4 => L26 | L5 => L28 | L6 => L10 | L7 => L34 | L8 => L5 | L9 => L11 | L10 => L24 | L11 => L29 | L12 => L14 | L13 => L20 | L14 => L12 | L15 => L19 | L16 => L21 | L17 => L15 | L18 => L1 | L19 => L9 | L20 => L6 | L21 => L23 | L22 => L27 | L23 => L7 | L24 => L2 | L25 => L33 | L26 => L32 | L27 => L0 | L28 => L18 | L29 => L17 | L30 => L16 | L31 => L8 | L32 => L4 | L33 => L25 | L34 => L30 end.

(* s28 : l3 : | p0 p7 p8 | l11 : | p1 p13 p11 | l15 : | p2 p3 p6 | l23 : | p4 p9 p14 | l30 : | p5 p10 p12 | -> 
   s29 : l3 : | p0 p7 p8 | l11 : | p1 p13 p11 | l17 : | p2 p4 p5 | l19 : | p3 p10 p14 | l33 : | p6 p9 p12 |  *)
Definition fp28_29 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P4 | P4 => P3 | P5 => P6 | P6 => P5 | P7 => P8 | P8 => P7 | P9 => P10 | P10 => P9 | P11 => P11 | P12 => P12 | P13 => P13 | P14 => P14 end.
Definition fl28_29 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L3 | L4 => L4 | L5 => L5 | L6 => L6 | L7 => L12 | L8 => L10 | L9 => L9 | L10 => L8 | L11 => L11 | L12 => L7 | L13 => L18 | L14 => L14 | L15 => L17 | L16 => L16 | L17 => L15 | L18 => L13 | L19 => L23 | L20 => L26 | L21 => L25 | L22 => L24 | L23 => L19 | L24 => L22 | L25 => L21 | L26 => L20 | L27 => L31 | L28 => L32 | L29 => L34 | L30 => L33 | L31 => L27 | L32 => L28 | L33 => L30 | L34 => L29 end.

(* s29 : l3 : | p0 p7 p8 | l11 : | p1 p13 p11 | l17 : | p2 p4 p5 | l19 : | p3 p10 p14 | l33 : | p6 p9 p12 | -> 
   s30 : l3 : | p0 p7 p8 | l12 : | p1 p3 p5 | l14 : | p2 p11 p14 | l25 : | p4 p10 p13 | l33 : | p6 p9 p12 |  *)
Definition fp29_30 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P13 | P4 => P14 | P5 => P11 | P6 => P12 | P7 => P7 | P8 => P8 | P9 => P9 | P10 => P10 | P11 => P5 | P12 => P6 | P13 => P3 | P14 => P4 end.
Definition fl29_30 (l:Line) := match l with L0 => L0 | L1 => L6 | L2 => L5 | L3 => L3 | L4 => L4 | L5 => L2 | L6 => L1 | L7 => L9 | L8 => L8 | L9 => L7 | L10 => L10 | L11 => L12 | L12 => L11 | L13 => L13 | L14 => L17 | L15 => L16 | L16 => L15 | L17 => L14 | L18 => L18 | L19 => L25 | L20 => L32 | L21 => L21 | L22 => L28 | L23 => L23 | L24 => L27 | L25 => L19 | L26 => L31 | L27 => L24 | L28 => L22 | L29 => L29 | L30 => L34 | L31 => L26 | L32 => L20 | L33 => L33 | L34 => L30 end.

(* s30 : l3 : | p0 p7 p8 | l12 : | p1 p3 p5 | l14 : | p2 p11 p14 | l25 : | p4 p10 p13 | l33 : | p6 p9 p12 | -> 
   s31 : l3 : | p0 p7 p8 | l12 : | p1 p3 p5 | l16 : | p2 p12 p13 | l23 : | p4 p9 p14 | l34 : | p6 p10 p11 |  *)
Definition fp30_31 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P8 | P8 => P7 | P9 => P10 | P10 => P9 | P11 => P12 | P12 => P11 | P13 => P14 | P14 => P13 end.
Definition fl30_31 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L3 | L4 => L4 | L5 => L5 | L6 => L6 | L7 => L7 | L8 => L10 | L9 => L11 | L10 => L8 | L11 => L9 | L12 => L12 | L13 => L18 | L14 => L16 | L15 => L15 | L16 => L14 | L17 => L17 | L18 => L13 | L19 => L21 | L20 => L22 | L21 => L19 | L22 => L20 | L23 => L25 | L24 => L26 | L25 => L23 | L26 => L24 | L27 => L28 | L28 => L27 | L29 => L30 | L30 => L29 | L31 => L32 | L32 => L31 | L33 => L34 | L34 => L33 end.

(* s31 : l3 : | p0 p7 p8 | l12 : | p1 p3 p5 | l16 : | p2 p12 p13 | l23 : | p4 p9 p14 | l34 : | p6 p10 p11 | -> 
   s32 : l4 : | p0 p10 p9 | l7 : | p1 p4 p6 | l14 : | p2 p11 p14 | l20 : | p3 p8 p12 | l28 : | p5 p7 p13 |  *)
Definition fp31_32 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P4 | P4 => P3 | P5 => P6 | P6 => P5 | P7 => P10 | P8 => P9 | P9 => P8 | P10 => P7 | P11 => P13 | P12 => P14 | P13 => P11 | P14 => P12 end.
Definition fl31_32 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L4 | L4 => L3 | L5 => L6 | L6 => L5 | L7 => L12 | L8 => L10 | L9 => L9 | L10 => L8 | L11 => L11 | L12 => L7 | L13 => L13 | L14 => L16 | L15 => L17 | L16 => L14 | L17 => L15 | L18 => L18 | L19 => L26 | L20 => L23 | L21 => L24 | L22 => L25 | L23 => L20 | L24 => L21 | L25 => L22 | L26 => L19 | L27 => L33 | L28 => L34 | L29 => L32 | L30 => L31 | L31 => L30 | L32 => L29 | L33 => L27 | L34 => L28 end.

(* s32 : l4 : | p0 p10 p9 | l7 : | p1 p4 p6 | l14 : | p2 p11 p14 | l20 : | p3 p8 p12 | l28 : | p5 p7 p13 | -> 
   s33 : l4 : | p0 p10 p9 | l7 : | p1 p4 p6 | l16 : | p2 p12 p13 | l22 : | p3 p7 p11 | l27 : | p5 p8 p14 |  *)
Definition fp32_33 (p:Point) := match p with P0 => P9 | P1 => P6 | P2 => P12 | P3 => P7 | P4 => P1 | P5 => P14 | P6 => P4 | P7 => P5 | P8 => P11 | P9 => P0 | P10 => P10 | P11 => P13 | P12 => P3 | P13 => P8 | P14 => P2 end.
Definition fl32_33 (l:Line) := match l with L0 => L33 | L1 => L10 | L2 => L23 | L3 => L29 | L4 => L4 | L5 => L21 | L6 => L18 | L7 => L7 | L8 => L34 | L9 => L15 | L10 => L2 | L11 => L32 | L12 => L31 | L13 => L30 | L14 => L16 | L15 => L26 | L16 => L20 | L17 => L9 | L18 => L5 | L19 => L13 | L20 => L22 | L21 => L3 | L22 => L28 | L23 => L0 | L24 => L11 | L25 => L8 | L26 => L12 | L27 => L14 | L28 => L27 | L29 => L6 | L30 => L19 | L31 => L17 | L32 => L24 | L33 => L1 | L34 => L25 end.

(* s33 : l4 : | p0 p10 p9 | l7 : | p1 p4 p6 | l16 : | p2 p12 p13 | l22 : | p3 p7 p11 | l27 : | p5 p8 p14 | -> 
   s34 : l4 : | p0 p10 p9 | l9 : | p1 p12 p14 | l15 : | p2 p3 p6 | l24 : | p4 p8 p11 | l28 : | p5 p7 p13 |  *)
Definition fp33_34 (p:Point) := match p with P0 => P9 | P1 => P12 | P2 => P6 | P3 => P4 | P4 => P14 | P5 => P7 | P6 => P1 | P7 => P11 | P8 => P5 | P9 => P0 | P10 => P10 | P11 => P8 | P12 => P2 | P13 => P3 | P14 => P13 end.
Definition fl33_34 (l:Line) := match l with L0 => L33 | L1 => L23 | L2 => L10 | L3 => L29 | L4 => L4 | L5 => L18 | L6 => L21 | L7 => L9 | L8 => L30 | L9 => L16 | L10 => L5 | L11 => L20 | L12 => L26 | L13 => L34 | L14 => L32 | L15 => L7 | L16 => L15 | L17 => L31 | L18 => L2 | L19 => L25 | L20 => L17 | L21 => L1 | L22 => L24 | L23 => L6 | L24 => L27 | L25 => L19 | L26 => L14 | L27 => L28 | L28 => L22 | L29 => L3 | L30 => L13 | L31 => L11 | L32 => L12 | L33 => L0 | L34 => L8 end.

(* s34 : l4 : | p0 p10 p9 | l9 : | p1 p12 p14 | l15 : | p2 p3 p6 | l24 : | p4 p8 p11 | l28 : | p5 p7 p13 | -> 
   s35 : l4 : | p0 p10 p9 | l9 : | p1 p12 p14 | l17 : | p2 p4 p5 | l22 : | p3 p7 p11 | l32 : | p6 p8 p13 |  *)
Definition fp34_35 (p:Point) := match p with P0 => P9 | P1 => P14 | P2 => P4 | P3 => P5 | P4 => P11 | P5 => P8 | P6 => P2 | P7 => P13 | P8 => P3 | P9 => P0 | P10 => P10 | P11 => P7 | P12 => P1 | P13 => P6 | P14 => P12 end.
Definition fl34_35 (l:Line) := match l with L0 => L23 | L1 => L29 | L2 => L18 | L3 => L21 | L4 => L4 | L5 => L10 | L6 => L33 | L7 => L14 | L8 => L19 | L9 => L9 | L10 => L6 | L11 => L31 | L12 => L27 | L13 => L25 | L14 => L26 | L15 => L17 | L16 => L7 | L17 => L24 | L18 => L1 | L19 => L30 | L20 => L12 | L21 => L2 | L22 => L28 | L23 => L5 | L24 => L22 | L25 => L34 | L26 => L11 | L27 => L20 | L28 => L32 | L29 => L3 | L30 => L8 | L31 => L16 | L32 => L15 | L33 => L0 | L34 => L13 end.

(* s35 : l4 : | p0 p10 p9 | l9 : | p1 p12 p14 | l17 : | p2 p4 p5 | l22 : | p3 p7 p11 | l32 : | p6 p8 p13 | -> 
   s36 : l4 : | p0 p10 p9 | l11 : | p1 p13 p11 | l15 : | p2 p3 p6 | l26 : | p4 p7 p12 | l27 : | p5 p8 p14 |  *)
Definition fp35_36 (p:Point) := match p with P0 => P9 | P1 => P13 | P2 => P3 | P3 => P12 | P4 => P6 | P5 => P2 | P6 => P8 | P7 => P4 | P8 => P14 | P9 => P10 | P10 => P0 | P11 => P7 | P12 => P1 | P13 => P5 | P14 => P11 end.
Definition fl35_36 (l:Line) := match l with L0 => L21 | L1 => L33 | L2 => L18 | L3 => L23 | L4 => L4 | L5 => L10 | L6 => L29 | L7 => L32 | L8 => L6 | L9 => L11 | L10 => L25 | L11 => L28 | L12 => L16 | L13 => L1 | L14 => L22 | L15 => L20 | L16 => L12 | L17 => L15 | L18 => L19 | L19 => L5 | L20 => L9 | L21 => L30 | L22 => L26 | L23 => L34 | L24 => L31 | L25 => L2 | L26 => L7 | L27 => L14 | L28 => L17 | L29 => L13 | L30 => L0 | L31 => L24 | L32 => L27 | L33 => L8 | L34 => L3 end.

(* s36 : l4 : | p0 p10 p9 | l11 : | p1 p13 p11 | l15 : | p2 p3 p6 | l26 : | p4 p7 p12 | l27 : | p5 p8 p14 | -> 
   s37 : l4 : | p0 p10 p9 | l11 : | p1 p13 p11 | l17 : | p2 p4 p5 | l20 : | p3 p8 p12 | l31 : | p6 p7 p14 |  *)
Definition fp36_37 (p:Point) := match p with P0 => P9 | P1 => P11 | P2 => P5 | P3 => P2 | P4 => P8 | P5 => P14 | P6 => P4 | P7 => P12 | P8 => P6 | P9 => P0 | P10 => P10 | P11 => P13 | P12 => P3 | P13 => P1 | P14 => P7 end.
Definition fl36_37 (l:Line) := match l with L0 => L29 | L1 => L18 | L2 => L23 | L3 => L33 | L4 => L4 | L5 => L21 | L6 => L10 | L7 => L24 | L8 => L34 | L9 => L22 | L10 => L5 | L11 => L11 | L12 => L14 | L13 => L30 | L14 => L28 | L15 => L17 | L16 => L12 | L17 => L27 | L18 => L2 | L19 => L13 | L20 => L15 | L21 => L0 | L22 => L16 | L23 => L3 | L24 => L32 | L25 => L8 | L26 => L20 | L27 => L31 | L28 => L9 | L29 => L6 | L30 => L19 | L31 => L26 | L32 => L7 | L33 => L1 | L34 => L25 end.

(* s37 : l4 : | p0 p10 p9 | l11 : | p1 p13 p11 | l17 : | p2 p4 p5 | l20 : | p3 p8 p12 | l31 : | p6 p7 p14 | -> 
   s38 : l4 : | p0 p10 p9 | l12 : | p1 p3 p5 | l14 : | p2 p11 p14 | l26 : | p4 p7 p12 | l32 : | p6 p8 p13 |  *)
Definition fp37_38 (p:Point) := match p with P0 => P9 | P1 => P5 | P2 => P11 | P3 => P4 | P4 => P14 | P5 => P2 | P6 => P8 | P7 => P6 | P8 => P12 | P9 => P0 | P10 => P10 | P11 => P1 | P12 => P7 | P13 => P3 | P14 => P13 end.
Definition fl37_38 (l:Line) := match l with L0 => L29 | L1 => L23 | L2 => L18 | L3 => L33 | L4 => L4 | L5 => L10 | L6 => L21 | L7 => L27 | L8 => L30 | L9 => L28 | L10 => L2 | L11 => L12 | L12 => L17 | L13 => L34 | L14 => L11 | L15 => L24 | L16 => L22 | L17 => L14 | L18 => L5 | L19 => L25 | L20 => L26 | L21 => L1 | L22 => L7 | L23 => L6 | L24 => L9 | L25 => L19 | L26 => L31 | L27 => L16 | L28 => L15 | L29 => L0 | L30 => L13 | L31 => L32 | L32 => L20 | L33 => L3 | L34 => L8 end.

(* s38 : l4 : | p0 p10 p9 | l12 : | p1 p3 p5 | l14 : | p2 p11 p14 | l26 : | p4 p7 p12 | l32 : | p6 p8 p13 | -> 
   s39 : l4 : | p0 p10 p9 | l12 : | p1 p3 p5 | l16 : | p2 p12 p13 | l24 : | p4 p8 p11 | l31 : | p6 p7 p14 |  *)
Definition fp38_39 (p:Point) := match p with P0 => P9 | P1 => P3 | P2 => P13 | P3 => P5 | P4 => P11 | P5 => P1 | P6 => P7 | P7 => P4 | P8 => P14 | P9 => P0 | P10 => P10 | P11 => P2 | P12 => P8 | P13 => P6 | P14 => P12 end.
Definition fl38_39 (l:Line) := match l with L0 => L21 | L1 => L29 | L2 => L10 | L3 => L23 | L4 => L4 | L5 => L18 | L6 => L33 | L7 => L22 | L8 => L19 | L9 => L20 | L10 => L1 | L11 => L15 | L12 => L12 | L13 => L25 | L14 => L16 | L15 => L28 | L16 => L32 | L17 => L11 | L18 => L6 | L19 => L30 | L20 => L27 | L21 => L2 | L22 => L17 | L23 => L5 | L24 => L14 | L25 => L34 | L26 => L24 | L27 => L9 | L28 => L7 | L29 => L0 | L30 => L8 | L31 => L26 | L32 => L31 | L33 => L3 | L34 => L13 end.

(* s39 : l4 : | p0 p10 p9 | l12 : | p1 p3 p5 | l16 : | p2 p12 p13 | l24 : | p4 p8 p11 | l31 : | p6 p7 p14 | -> 
   s40 : l5 : | p0 p11 p12 | l7 : | p1 p4 p6 | l13 : | p2 p7 p10 | l21 : | p3 p9 p13 | l27 : | p5 p8 p14 |  *)
Definition fp39_40 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P4 | P4 => P3 | P5 => P6 | P6 => P5 | P7 => P14 | P8 => P13 | P9 => P12 | P10 => P11 | P11 => P9 | P12 => P10 | P13 => P7 | P14 => P8 end.
Definition fl39_40 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L6 | L4 => L5 | L5 => L4 | L6 => L3 | L7 => L12 | L8 => L11 | L9 => L8 | L10 => L9 | L11 => L10 | L12 => L7 | L13 => L14 | L14 => L18 | L15 => L17 | L16 => L13 | L17 => L15 | L18 => L16 | L19 => L24 | L20 => L25 | L21 => L26 | L22 => L23 | L23 => L20 | L24 => L21 | L25 => L22 | L26 => L19 | L27 => L32 | L28 => L31 | L29 => L33 | L30 => L34 | L31 => L27 | L32 => L28 | L33 => L30 | L34 => L29 end.

(* s40 : l5 : | p0 p11 p12 | l7 : | p1 p4 p6 | l13 : | p2 p7 p10 | l21 : | p3 p9 p13 | l27 : | p5 p8 p14 | -> 
   s41 : l5 : | p0 p11 p12 | l7 : | p1 p4 p6 | l18 : | p2 p8 p9 | l19 : | p3 p10 p14 | l28 : | p5 p7 p13 |  *)
Definition fp40_41 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P8 | P8 => P7 | P9 => P10 | P10 => P9 | P11 => P12 | P12 => P11 | P13 => P14 | P14 => P13 end.
Definition fl40_41 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L3 | L4 => L4 | L5 => L5 | L6 => L6 | L7 => L7 | L8 => L10 | L9 => L11 | L10 => L8 | L11 => L9 | L12 => L12 | L13 => L18 | L14 => L16 | L15 => L15 | L16 => L14 | L17 => L17 | L18 => L13 | L19 => L21 | L20 => L22 | L21 => L19 | L22 => L20 | L23 => L25 | L24 => L26 | L25 => L23 | L26 => L24 | L27 => L28 | L28 => L27 | L29 => L30 | L30 => L29 | L31 => L32 | L32 => L31 | L33 => L34 | L34 => L33 end.

(* s41 : l5 : | p0 p11 p12 | l7 : | p1 p4 p6 | l18 : | p2 p8 p9 | l19 : | p3 p10 p14 | l28 : | p5 p7 p13 | -> 
   s42 : l5 : | p0 p11 p12 | l8 : | p1 p8 p10 | l15 : | p2 p3 p6 | l23 : | p4 p9 p14 | l28 : | p5 p7 p13 |  *)
Definition fp41_42 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P9 | P4 => P10 | P5 => P7 | P6 => P8 | P7 => P5 | P8 => P6 | P9 => P3 | P10 => P4 | P11 => P11 | P12 => P12 | P13 => P13 | P14 => P14 end.
Definition fl41_42 (l:Line) := match l with L0 => L0 | L1 => L4 | L2 => L3 | L3 => L2 | L4 => L1 | L5 => L5 | L6 => L6 | L7 => L8 | L8 => L7 | L9 => L9 | L10 => L12 | L11 => L11 | L12 => L10 | L13 => L17 | L14 => L14 | L15 => L18 | L16 => L16 | L17 => L13 | L18 => L15 | L19 => L23 | L20 => L33 | L21 => L21 | L22 => L29 | L23 => L19 | L24 => L34 | L25 => L25 | L26 => L30 | L27 => L31 | L28 => L28 | L29 => L22 | L30 => L26 | L31 => L27 | L32 => L32 | L33 => L20 | L34 => L24 end.

(* s42 : l5 : | p0 p11 p12 | l8 : | p1 p8 p10 | l15 : | p2 p3 p6 | l23 : | p4 p9 p14 | l28 : | p5 p7 p13 | -> 
   s43 : l5 : | p0 p11 p12 | l8 : | p1 p8 p10 | l17 : | p2 p4 p5 | l21 : | p3 p9 p13 | l31 : | p6 p7 p14 |  *)
Definition fp42_43 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P4 | P4 => P3 | P5 => P6 | P6 => P5 | P7 => P7 | P8 => P8 | P9 => P9 | P10 => P10 | P11 => P12 | P12 => P11 | P13 => P14 | P14 => P13 end.
Definition fl42_43 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L3 | L4 => L4 | L5 => L5 | L6 => L6 | L7 => L12 | L8 => L8 | L9 => L11 | L10 => L10 | L11 => L9 | L12 => L7 | L13 => L13 | L14 => L16 | L15 => L17 | L16 => L14 | L17 => L15 | L18 => L18 | L19 => L25 | L20 => L24 | L21 => L23 | L22 => L26 | L23 => L21 | L24 => L20 | L25 => L19 | L26 => L22 | L27 => L32 | L28 => L31 | L29 => L33 | L30 => L34 | L31 => L28 | L32 => L27 | L33 => L29 | L34 => L30 end.

(* s43 : l5 : | p0 p11 p12 | l8 : | p1 p8 p10 | l17 : | p2 p4 p5 | l21 : | p3 p9 p13 | l31 : | p6 p7 p14 | -> 
   s44 : l5 : | p0 p11 p12 | l10 : | p1 p7 p9 | l15 : | p2 p3 p6 | l25 : | p4 p10 p13 | l27 : | p5 p8 p14 |  *)
Definition fp43_44 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P4 | P4 => P3 | P5 => P6 | P6 => P5 | P7 => P8 | P8 => P7 | P9 => P10 | P10 => P9 | P11 => P11 | P12 => P12 | P13 => P13 | P14 => P14 end.
Definition fl43_44 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L3 | L4 => L4 | L5 => L5 | L6 => L6 | L7 => L12 | L8 => L10 | L9 => L9 | L10 => L8 | L11 => L11 | L12 => L7 | L13 => L18 | L14 => L14 | L15 => L17 | L16 => L16 | L17 => L15 | L18 => L13 | L19 => L23 | L20 => L26 | L21 => L25 | L22 => L24 | L23 => L19 | L24 => L22 | L25 => L21 | L26 => L20 | L27 => L31 | L28 => L32 | L29 => L34 | L30 => L33 | L31 => L27 | L32 => L28 | L33 => L30 | L34 => L29 end.

(* s44 : l5 : | p0 p11 p12 | l10 : | p1 p7 p9 | l15 : | p2 p3 p6 | l25 : | p4 p10 p13 | l27 : | p5 p8 p14 | -> 
   s45 : l5 : | p0 p11 p12 | l10 : | p1 p7 p9 | l17 : | p2 p4 p5 | l19 : | p3 p10 p14 | l32 : | p6 p8 p13 |  *)
Definition fp44_45 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P4 | P4 => P3 | P5 => P6 | P6 => P5 | P7 => P7 | P8 => P8 | P9 => P9 | P10 => P10 | P11 => P12 | P12 => P11 | P13 => P14 | P14 => P13 end.
Definition fl44_45 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L3 | L4 => L4 | L5 => L5 | L6 => L6 | L7 => L12 | L8 => L8 | L9 => L11 | L10 => L10 | L11 => L9 | L12 => L7 | L13 => L13 | L14 => L16 | L15 => L17 | L16 => L14 | L17 => L15 | L18 => L18 | L19 => L25 | L20 => L24 | L21 => L23 | L22 => L26 | L23 => L21 | L24 => L20 | L25 => L19 | L26 => L22 | L27 => L32 | L28 => L31 | L29 => L33 | L30 => L34 | L31 => L28 | L32 => L27 | L33 => L29 | L34 => L30 end.

(* s45 : l5 : | p0 p11 p12 | l10 : | p1 p7 p9 | l17 : | p2 p4 p5 | l19 : | p3 p10 p14 | l32 : | p6 p8 p13 | -> 
   s46 : l5 : | p0 p11 p12 | l12 : | p1 p3 p5 | l13 : | p2 p7 p10 | l23 : | p4 p9 p14 | l32 : | p6 p8 p13 |  *)
Definition fp45_46 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P9 | P4 => P10 | P5 => P7 | P6 => P8 | P7 => P5 | P8 => P6 | P9 => P3 | P10 => P4 | P11 => P11 | P12 => P12 | P13 => P13 | P14 => P14 end.
Definition fl45_46 (l:Line) := match l with L0 => L0 | L1 => L4 | L2 => L3 | L3 => L2 | L4 => L1 | L5 => L5 | L6 => L6 | L7 => L8 | L8 => L7 | L9 => L9 | L10 => L12 | L11 => L11 | L12 => L10 | L13 => L17 | L14 => L14 | L15 => L18 | L16 => L16 | L17 => L13 | L18 => L15 | L19 => L23 | L20 => L33 | L21 => L21 | L22 => L29 | L23 => L19 | L24 => L34 | L25 => L25 | L26 => L30 | L27 => L31 | L28 => L28 | L29 => L22 | L30 => L26 | L31 => L27 | L32 => L32 | L33 => L20 | L34 => L24 end.

(* s46 : l5 : | p0 p11 p12 | l12 : | p1 p3 p5 | l13 : | p2 p7 p10 | l23 : | p4 p9 p14 | l32 : | p6 p8 p13 | -> 
   s47 : l5 : | p0 p11 p12 | l12 : | p1 p3 p5 | l18 : | p2 p8 p9 | l25 : | p4 p10 p13 | l31 : | p6 p7 p14 |  *)
Definition fp46_47 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P8 | P8 => P7 | P9 => P10 | P10 => P9 | P11 => P12 | P12 => P11 | P13 => P14 | P14 => P13 end.
Definition fl46_47 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L3 | L4 => L4 | L5 => L5 | L6 => L6 | L7 => L7 | L8 => L10 | L9 => L11 | L10 => L8 | L11 => L9 | L12 => L12 | L13 => L18 | L14 => L16 | L15 => L15 | L16 => L14 | L17 => L17 | L18 => L13 | L19 => L21 | L20 => L22 | L21 => L19 | L22 => L20 | L23 => L25 | L24 => L26 | L25 => L23 | L26 => L24 | L27 => L28 | L28 => L27 | L29 => L30 | L30 => L29 | L31 => L32 | L32 => L31 | L33 => L34 | L34 => L33 end.

(* s47 : l5 : | p0 p11 p12 | l12 : | p1 p3 p5 | l18 : | p2 p8 p9 | l25 : | p4 p10 p13 | l31 : | p6 p7 p14 | -> 
   s48 : l6 : | p0 p13 p14 | l7 : | p1 p4 p6 | l13 : | p2 p7 p10 | l20 : | p3 p8 p12 | l29 : | p5 p9 p11 |  *)
Definition fp47_48 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P4 | P4 => P3 | P5 => P6 | P6 => P5 | P7 => P9 | P8 => P10 | P9 => P7 | P10 => P8 | P11 => P14 | P12 => P13 | P13 => P12 | P14 => P11 end.
Definition fl47_48 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L4 | L4 => L3 | L5 => L6 | L6 => L5 | L7 => L12 | L8 => L8 | L9 => L11 | L10 => L10 | L11 => L9 | L12 => L7 | L13 => L18 | L14 => L14 | L15 => L17 | L16 => L16 | L17 => L15 | L18 => L13 | L19 => L24 | L20 => L25 | L21 => L26 | L22 => L23 | L23 => L22 | L24 => L19 | L25 => L20 | L26 => L21 | L27 => L34 | L28 => L33 | L29 => L31 | L30 => L32 | L31 => L29 | L32 => L30 | L33 => L28 | L34 => L27 end.

(* s48 : l6 : | p0 p13 p14 | l7 : | p1 p4 p6 | l13 : | p2 p7 p10 | l20 : | p3 p8 p12 | l29 : | p5 p9 p11 | -> 
   s49 : l6 : | p0 p13 p14 | l7 : | p1 p4 p6 | l18 : | p2 p8 p9 | l22 : | p3 p7 p11 | l30 : | p5 p10 p12 |  *)
Definition fp48_49 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P8 | P8 => P7 | P9 => P10 | P10 => P9 | P11 => P12 | P12 => P11 | P13 => P14 | P14 => P13 end.
Definition fl48_49 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L3 | L4 => L4 | L5 => L5 | L6 => L6 | L7 => L7 | L8 => L10 | L9 => L11 | L10 => L8 | L11 => L9 | L12 => L12 | L13 => L18 | L14 => L16 | L15 => L15 | L16 => L14 | L17 => L17 | L18 => L13 | L19 => L21 | L20 => L22 | L21 => L19 | L22 => L20 | L23 => L25 | L24 => L26 | L25 => L23 | L26 => L24 | L27 => L28 | L28 => L27 | L29 => L30 | L30 => L29 | L31 => L32 | L32 => L31 | L33 => L34 | L34 => L33 end.

(* s49 : l6 : | p0 p13 p14 | l7 : | p1 p4 p6 | l18 : | p2 p8 p9 | l22 : | p3 p7 p11 | l30 : | p5 p10 p12 | -> 
   s50 : l6 : | p0 p13 p14 | l8 : | p1 p8 p10 | l15 : | p2 p3 p6 | l26 : | p4 p7 p12 | l29 : | p5 p9 p11 |  *)
Definition fp49_50 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P7 | P4 => P8 | P5 => P9 | P6 => P10 | P7 => P4 | P8 => P3 | P9 => P6 | P10 => P5 | P11 => P12 | P12 => P11 | P13 => P14 | P14 => P13 end.
Definition fl49_50 (l:Line) := match l with L0 => L0 | L1 => L3 | L2 => L4 | L3 => L1 | L4 => L2 | L5 => L5 | L6 => L6 | L7 => L8 | L8 => L12 | L9 => L11 | L10 => L7 | L11 => L9 | L12 => L10 | L13 => L17 | L14 => L16 | L15 => L13 | L16 => L14 | L17 => L18 | L18 => L15 | L19 => L28 | L20 => L22 | L21 => L31 | L22 => L26 | L23 => L32 | L24 => L20 | L25 => L27 | L26 => L24 | L27 => L21 | L28 => L23 | L29 => L33 | L30 => L29 | L31 => L25 | L32 => L19 | L33 => L34 | L34 => L30 end.

(* s50 : l6 : | p0 p13 p14 | l8 : | p1 p8 p10 | l15 : | p2 p3 p6 | l26 : | p4 p7 p12 | l29 : | p5 p9 p11 | -> 
   s51 : l6 : | p0 p13 p14 | l8 : | p1 p8 p10 | l17 : | p2 p4 p5 | l22 : | p3 p7 p11 | l33 : | p6 p9 p12 |  *)
Definition fp50_51 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P4 | P4 => P3 | P5 => P6 | P6 => P5 | P7 => P7 | P8 => P8 | P9 => P9 | P10 => P10 | P11 => P12 | P12 => P11 | P13 => P14 | P14 => P13 end.
Definition fl50_51 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L3 | L4 => L4 | L5 => L5 | L6 => L6 | L7 => L12 | L8 => L8 | L9 => L11 | L10 => L10 | L11 => L9 | L12 => L7 | L13 => L13 | L14 => L16 | L15 => L17 | L16 => L14 | L17 => L15 | L18 => L18 | L19 => L25 | L20 => L24 | L21 => L23 | L22 => L26 | L23 => L21 | L24 => L20 | L25 => L19 | L26 => L22 | L27 => L32 | L28 => L31 | L29 => L33 | L30 => L34 | L31 => L28 | L32 => L27 | L33 => L29 | L34 => L30 end.

(* s51 : l6 : | p0 p13 p14 | l8 : | p1 p8 p10 | l17 : | p2 p4 p5 | l22 : | p3 p7 p11 | l33 : | p6 p9 p12 | -> 
   s52 : l6 : | p0 p13 p14 | l10 : | p1 p7 p9 | l15 : | p2 p3 p6 | l24 : | p4 p8 p11 | l30 : | p5 p10 p12 |  *)
Definition fp51_52 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P4 | P4 => P3 | P5 => P6 | P6 => P5 | P7 => P8 | P8 => P7 | P9 => P10 | P10 => P9 | P11 => P11 | P12 => P12 | P13 => P13 | P14 => P14 end.
Definition fl51_52 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L3 | L4 => L4 | L5 => L5 | L6 => L6 | L7 => L12 | L8 => L10 | L9 => L9 | L10 => L8 | L11 => L11 | L12 => L7 | L13 => L18 | L14 => L14 | L15 => L17 | L16 => L16 | L17 => L15 | L18 => L13 | L19 => L23 | L20 => L26 | L21 => L25 | L22 => L24 | L23 => L19 | L24 => L22 | L25 => L21 | L26 => L20 | L27 => L31 | L28 => L32 | L29 => L34 | L30 => L33 | L31 => L27 | L32 => L28 | L33 => L30 | L34 => L29 end.

(* s52 : l6 : | p0 p13 p14 | l10 : | p1 p7 p9 | l15 : | p2 p3 p6 | l24 : | p4 p8 p11 | l30 : | p5 p10 p12 | -> 
   s53 : l6 : | p0 p13 p14 | l10 : | p1 p7 p9 | l17 : | p2 p4 p5 | l20 : | p3 p8 p12 | l34 : | p6 p10 p11 |  *)
Definition fp52_53 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P4 | P4 => P3 | P5 => P6 | P6 => P5 | P7 => P7 | P8 => P8 | P9 => P9 | P10 => P10 | P11 => P12 | P12 => P11 | P13 => P14 | P14 => P13 end.
Definition fl52_53 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L3 | L4 => L4 | L5 => L5 | L6 => L6 | L7 => L12 | L8 => L8 | L9 => L11 | L10 => L10 | L11 => L9 | L12 => L7 | L13 => L13 | L14 => L16 | L15 => L17 | L16 => L14 | L17 => L15 | L18 => L18 | L19 => L25 | L20 => L24 | L21 => L23 | L22 => L26 | L23 => L21 | L24 => L20 | L25 => L19 | L26 => L22 | L27 => L32 | L28 => L31 | L29 => L33 | L30 => L34 | L31 => L28 | L32 => L27 | L33 => L29 | L34 => L30 end.

(* s53 : l6 : | p0 p13 p14 | l10 : | p1 p7 p9 | l17 : | p2 p4 p5 | l20 : | p3 p8 p12 | l34 : | p6 p10 p11 | -> 
   s54 : l6 : | p0 p13 p14 | l12 : | p1 p3 p5 | l13 : | p2 p7 p10 | l24 : | p4 p8 p11 | l33 : | p6 p9 p12 |  *)
Definition fp53_54 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P8 | P4 => P7 | P5 => P10 | P6 => P9 | P7 => P3 | P8 => P4 | P9 => P5 | P10 => P6 | P11 => P12 | P12 => P11 | P13 => P14 | P14 => P13 end.
Definition fl53_54 (l:Line) := match l with L0 => L0 | L1 => L3 | L2 => L4 | L3 => L1 | L4 => L2 | L5 => L5 | L6 => L6 | L7 => L10 | L8 => L7 | L9 => L11 | L10 => L12 | L11 => L9 | L12 => L8 | L13 => L15 | L14 => L16 | L15 => L18 | L16 => L14 | L17 => L13 | L18 => L17 | L19 => L32 | L20 => L24 | L21 => L27 | L22 => L20 | L23 => L28 | L24 => L26 | L25 => L31 | L26 => L22 | L27 => L25 | L28 => L19 | L29 => L30 | L30 => L34 | L31 => L21 | L32 => L23 | L33 => L29 | L34 => L33 end.

(* s54 : l6 : | p0 p13 p14 | l12 : | p1 p3 p5 | l13 : | p2 p7 p10 | l24 : | p4 p8 p11 | l33 : | p6 p9 p12 | -> 
   s55 : l6 : | p0 p13 p14 | l12 : | p1 p3 p5 | l18 : | p2 p8 p9 | l26 : | p4 p7 p12 | l34 : | p6 p10 p11 |  *)
Definition fp54_55 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P8 | P8 => P7 | P9 => P10 | P10 => P9 | P11 => P12 | P12 => P11 | P13 => P14 | P14 => P13 end.
Definition fl54_55 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L3 | L4 => L4 | L5 => L5 | L6 => L6 | L7 => L7 | L8 => L10 | L9 => L11 | L10 => L8 | L11 => L9 | L12 => L12 | L13 => L18 | L14 => L16 | L15 => L15 | L16 => L14 | L17 => L17 | L18 => L13 | L19 => L21 | L20 => L22 | L21 => L19 | L22 => L20 | L23 => L25 | L24 => L26 | L25 => L23 | L26 => L24 | L27 => L28 | L28 => L27 | L29 => L30 | L30 => L29 | L31 => L32 | L32 => L31 | L33 => L34 | L34 => L33 end.

(* s55 : l6 : | p0 p13 p14 | l12 : | p1 p3 p5 | l18 : | p2 p8 p9 | l26 : | p4 p7 p12 | l34 : | p6 p10 p11 | -> 
   s0 : l0 : | p0 p1 p2 | l19 : | p3 p10 p14 | l24 : | p4 p8 p11 | l28 : | p5 p7 p13 | l33 : | p6 p9 p12 |  *)
Definition fp55_0 (p:Point) := match p with P0 => P0 | P1 => P3 | P2 => P4 | P3 => P14 | P4 => P13 | P5 => P10 | P6 => P9 | P7 => P7 | P8 => P8 | P9 => P11 | P10 => P12 | P11 => P6 | P12 => P5 | P13 => P2 | P14 => P1 end.
Definition fl55_0 (l:Line) := match l with L0 => L1 | L1 => L6 | L2 => L4 | L3 => L3 | L4 => L5 | L5 => L2 | L6 => L0 | L7 => L21 | L8 => L20 | L9 => L12 | L10 => L22 | L11 => L15 | L12 => L19 | L13 => L26 | L14 => L7 | L15 => L23 | L16 => L17 | L17 => L25 | L18 => L24 | L19 => L9 | L20 => L27 | L21 => L14 | L22 => L31 | L23 => L11 | L24 => L32 | L25 => L16 | L26 => L28 | L27 => L8 | L28 => L13 | L29 => L34 | L30 => L30 | L31 => L10 | L32 => L18 | L33 => L29 | L34 => L33 end.


(* tools to deal with collineations *)

Definition inj {A:Set} {B:Set} (f:A->B) : Prop := forall x y:A, f x = f y -> x = y. 
Definition surj {A:Set} {B:Set} (f:A->B) : Prop := forall y:B, exists x:A, y=f(x).

Definition bij {A:Set} {B:Set} (f:A->B) : Prop  := (inj f) /\ (surj f).

Definition is_collineation fp fl :=
  ((bij fp) /\ ((bij fl) /\ (forall x l, incid_lp x l -> incid_lp (fp x) (fl l))))%type.

Ltac solve_surjP :=
  solve [
      exists P0; reflexivity |
             exists P0; reflexivity |
             exists P1; reflexivity |
             exists P2; reflexivity |
             exists P3; reflexivity |
             exists P4; reflexivity |
             exists P5; reflexivity |
             exists P6; reflexivity |
             exists P7; reflexivity |
             exists P8; reflexivity |
             exists P9; reflexivity |
             exists P10; reflexivity |
             exists P11; reflexivity |
             exists P12; reflexivity |
             exists P13; reflexivity |
             exists P14; reflexivity ].

Ltac solve_surjL :=
  solve [
      exists L0; reflexivity |
             exists L0; reflexivity |
             exists L1; reflexivity |
             exists L2; reflexivity |
             exists L3; reflexivity |
             exists L4; reflexivity |
             exists L5; reflexivity |
             exists L6; reflexivity |
             exists L7; reflexivity |
             exists L8; reflexivity |
             exists L9; reflexivity |
             exists L10; reflexivity |
             exists L11; reflexivity |
             exists L12; reflexivity |
             exists L13; reflexivity |
             exists L14; reflexivity | 
             exists L15; reflexivity |
             exists L16; reflexivity |
             exists L17; reflexivity |
             exists L18; reflexivity |
             exists L19; reflexivity |
             exists L20; reflexivity |
             exists L21; reflexivity |
             exists L22; reflexivity |
             exists L23; reflexivity |
             exists L24; reflexivity |
             exists L25; reflexivity |
             exists L26; reflexivity |
             exists L27; reflexivity |
             exists L28; reflexivity |
             exists L29; reflexivity |
             exists L30; reflexivity |
             exists L31; reflexivity |
             exists L32; reflexivity |
             exists L33; reflexivity |
             exists L34; reflexivity
    ].

Ltac is_col := split;
    [ split; [unfold inj; let x:= fresh in let y:=fresh in  intros x y; destruct x; destruct y; simpl; let H := fresh in intros H; solve [discriminate H | reflexivity ] |
              unfold surj; let y:= fresh in intros y; destruct y; solve_surjP]
    | 
    split; [
      split; [unfold inj; let x:= fresh in let y:=fresh in intros x y; destruct x; destruct y; simpl;  let H := fresh in intros H; solve [discriminate H | reflexivity ] |
              unfold surj; let y:= fresh in intros y; destruct y; solve_surjL] | 
      intros x l; destruct x; destruct l;
      let H := fresh in intros H; solve [apply (degen_bool _ H) | apply is_true_true]]].

(* test of the tactic is_col *)
Lemma c0_1 : is_collineation fp0_1 fl0_1.
Proof.
  is_col.
Qed.

Definition all_isomorphic (A:Set) (P:(list A)->(list A)->Prop) l :=
  forall t1 t2: (list A), In t1 l -> In t2 l -> P t1 t2.

Definition all_iso_decomp  (A:Set) (P:(list A)->(list A)->Prop) (l:list (list A)) :=
  forall n:nat, (length l <> 0) -> P (nth (Nat.modulo n (length l)) l []) (nth (Nat.modulo (S n) (length l)) l []).

Section P.
  Variable A:Set.
  Variable l:list (list A).
  Variable P:(list A -> list A -> Prop).
  Hypothesis length_l : length l <> 0 .

  Hypothesis P_refl : forall a, P a a.
(*  Hypothesis P_sym : forall a b, P a b -> P b a.*)
  Hypothesis P_trans : forall a b c, P a b -> P b c -> P a c.
  
  Lemma induction_step_1 :  (forall n,
                                P (nth (Nat.modulo n (length l)) l []) (nth (Nat.modulo (S n) (length l)) l [])) -> 
                            forall m t, P (nth (Nat.modulo m (length l)) l []) (nth (Nat.modulo (t + m) (length l)) l []).
    intros.
    induction t.
    simpl.
    apply P_refl.
    apply P_trans with (nth (Nat.modulo (t + m) (length l)) l []).
    assumption.
    apply H.
  Qed.
  
  Lemma induction_step :
    (forall n : nat, P (nth (Nat.modulo n (length l)) l []) (nth (Nat.modulo (S n) (length l)) l []))
    <-> (forall p q :nat, P (nth (Nat.modulo p (length l)) l []) (nth (Nat.modulo q (length l)) l [])).
  Proof.                         
    intros.
    split.
    (* -> *)
    intros.
    destruct (PeanoNat.Nat.lt_ge_cases p q).
    assert (p<=q) by lia.
    destruct (PeanoNat.Nat.le_exists_sub _ _ H1) as [t [Ha Hb]].
    rewrite Ha.
    apply induction_step_1.
    apply H; assumption.
    destruct (PeanoNat.Nat.le_exists_sub _ _ H0) as [t [Ha Hb]].
    rewrite Ha.
    replace  (Nat.modulo q (length l)) with (Nat.modulo ((((S(Nat.div t (length l)))*(length l)) -t)+(t+q)) (length l)).
    apply induction_step_1.
    assumption.
    rewrite <-    PeanoNat.Nat.add_sub_swap.
    replace (S(Nat.div t (length l)) * length l + (t + q) - t) with (q + ((S(Nat.div t (length l)) * length l))) by lia.
    rewrite PeanoNat.Nat.mod_add; try lia. 
    apply PeanoNat.Nat.lt_le_incl.
    rewrite PeanoNat.Nat.mul_comm.
    apply PeanoNat.Nat.mul_succ_div_gt.
    lia.
    (* <- *)
    intros.
    apply H.
  Qed.
  
  Lemma all_equiv : all_isomorphic A P l <-> all_iso_decomp A P l.
  Proof.
    unfold all_isomorphic,all_iso_decomp; split.
    intros.
    apply H.
    apply nth_In.
    apply PeanoNat.Nat.mod_upper_bound; assumption.
    apply nth_In.
    apply PeanoNat.Nat.mod_upper_bound; assumption.
    
    intros.
    destruct (In_nth l t1 [] H0) as[x1 [Hx1 Hx1']].
    destruct (In_nth l t2 [] H1) as[x2 [Hx2 Hx2']].
    rewrite <- Hx1'.
    rewrite <- Hx2'.
    assert (Hx1bis:x1=Nat.modulo x1 (length l)).
    symmetry; apply PeanoNat.Nat.mod_small with(b:=length l); assumption.
    assert (Hx2bis: x2=Nat.modulo x2 (length l)).
    symmetry; apply PeanoNat.Nat.mod_small with(b:=length l); assumption.
    rewrite Hx1bis.
    rewrite Hx2bis.
    apply induction_step.
    intros; apply H; assumption.
  Qed.
End P.

Definition are_isomorphic (s1:list Line) (s2:list Line) : Prop :=
  exists fp, exists fl, ((is_collineation fp fl) /\ (map fl s1 = s2)).

Lemma are_isomorphic_refl : forall s, are_isomorphic s s.
Proof.
  exists (fun (p:Point) => p).
  exists (fun (l:Line) => l).
  split.
  simpl.
  split.
  split.
  unfold inj; destruct x; destruct y; simpl; intros H; solve [discriminate H | reflexivity ].
  unfold surj; destruct y; solve_surjP.
  split.
  split.
  unfold inj; destruct x; destruct y; simpl; intros H; solve [discriminate H | reflexivity ].
  unfold surj; destruct y; solve_surjL.
  intros; assumption.
  apply map_id.
Qed.
                                                                      
Lemma are_isomorphic_trans :
  forall s1 s2 s3, are_isomorphic s1 s2 -> are_isomorphic s2 s3 -> are_isomorphic s1 s3.
Proof.
intros s1 s2 s3 Hs1s2 Hs2s3.
destruct Hs1s2 as [fp [ fl [is_col is_map]]].
destruct Hs2s3 as [fp' [ fl' [is_col' is_map']]].
destruct is_col as [[Hinjp Hsurjp] [[Hinjl Hsurjl] Hcompat]].
destruct is_col' as [[Hinjp' Hsurjp'] [[Hinjl' Hsurjl'] Hcompat']].

exists (fun (x:Point) => fp' (fp x)).
exists (fun (x:Line) => fl' (fl x)).
split.
split.
split.
unfold inj.
intros.
apply Hinjp.
apply Hinjp'.
assumption.
unfold surj.
intros.
unfold surj in *.
destruct (Hsurjp' y).
destruct (Hsurjp x).
exists x0.
rewrite H0 in H.
assumption.
split.
split.
unfold inj.
intros.
apply Hinjl.
apply Hinjl'.
assumption.
unfold surj.
intros.
unfold surj in *.
destruct (Hsurjl' y).
destruct (Hsurjl x).
exists x0.
rewrite H0 in H.
assumption.
intros.
apply Hcompat'.
apply Hcompat.
assumption.
rewrite <- map_map.
rewrite is_map.
assumption.
Qed.

Lemma equiv :
  forall P:nat->Prop,
    (forall n:nat, n<56 -> P n) <->
    (P 0 /\ P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5 /\ P 6 /\ P 7 /\ P 8 /\ P 9 /\
     P 10 /\ P 11 /\ P 12 /\ P 13 /\ P 14 /\ P 15 /\ P 16 /\ P 17 /\ P 18 /\ P 19 /\
     P 20 /\ P 21 /\ P 22 /\ P 23 /\ P 24 /\ P 25 /\ P 26 /\ P 27 /\ P 28 /\ P 29 /\
     P 30 /\ P 31 /\ P 32 /\ P 33 /\ P 34 /\ P 35 /\ P 36 /\ P 37 /\ P 38 /\ P 39 /\
     P 40 /\ P 41 /\ P 42 /\ P 43 /\ P 44 /\ P 45 /\ P 46 /\ P 47 /\ P 48 /\ P 49 /\
     P 50 /\ P 51 /\ P 52 /\ P 53 /\ P 54 /\ P 55).
Proof.
intros.
split.  
intros.
repeat split; apply H; lia.
intros.
assert (foo:forall x y : nat, x < S y -> x=y \/ x < y) by (intros; lia).
repeat (match goal with T:?n< S ?i |- _ => let Hequal := fresh in let Hlt := fresh in destruct (foo n i T) as [Hequal | Hlt]; clear T; [subst;intuition|idtac] end).
lia.
Qed.

Lemma n56_decomp : forall n:nat, n < 56 <->
                        n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n  = 8 \/ n = 9 \/
                        n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16 \/ n = 17 \/ n  = 18 \/ n = 19 \/
                        n = 20 \/ n = 21 \/ n = 22 \/ n = 23 \/ n = 24 \/ n = 25 \/ n = 26 \/ n = 27 \/ n  = 28 \/ n = 29 \/
                        n = 30 \/ n = 31 \/ n = 32 \/ n = 33 \/ n = 34 \/ n = 35 \/ n = 36 \/ n = 37 \/ n  = 38 \/ n = 39 \/
                        n = 40 \/ n = 41 \/ n = 42 \/ n = 43 \/ n = 44 \/ n = 45 \/ n = 46 \/ n = 47 \/ n  = 48 \/ n = 49 \/
                        n = 50 \/ n = 51 \/ n = 52 \/ n = 53 \/ n = 54 \/ n = 55 .
Proof.
  split.
  assert (foo:forall x y : nat, x < S y -> x=y \/ x < y) by (intros; lia).
  intros.  
  repeat (match goal with T:?n< S ?i |- _ => let Hequal := fresh in let Hlt := fresh in destruct (foo n i T) as [Hequal | Hlt]; clear T; [subst;intuition|idtac] end).
inversion H0.
lia.
Qed.

Lemma modulo_prop : forall n:nat, exists p:nat, p<56 /\ PeanoNat.Nat.modulo n 56 = p.
Proof.
  intros.
  exists (PeanoNat.Nat.modulo n 56).
  split.
  apply PeanoNat.Nat.mod_bound_pos.
  lia.
  lia.
  reflexivity.
Qed.

Lemma modulo_S : forall n:nat,
    (Nat.modulo (S n) 56 = S (Nat.modulo n 56)) \/ ((Nat.modulo n 56=55)/\(Nat.modulo (S n) 56=0)).
Proof.
  intros; apply or_comm;apply modulo_S56.
Qed.

Lemma equiv' :
  forall P:nat->nat->Prop,
    (forall n:nat, P (Nat.modulo n 56) (Nat.modulo (S n) 56)) <->
    (P 0 1/\ P 1 2 /\ P 2 3/\ P 3 4/\ P 4 5/\ P 5 6/\ P 6 7/\ P 7 8/\ P 8 9/\ P 9 10/\
     P 10 11/\ P 11 12/\ P 12 13/\ P 13 14/\ P 14 15/\ P 15 16/\ P 16 17/\ P 17 18/\ P 18 19/\ P 19 20/\
     P 20 21/\ P 21 22/\ P 22 23/\ P 23 24/\ P 24 25/\ P 25 26/\ P 26 27/\ P 27 28/\ P 28 29/\ P 29 30/\
     P 30 31/\ P 31 32/\ P 32 33/\ P 33 34/\ P 34 35/\ P 35 36/\ P 36 37/\ P 37 38/\ P 38 39/\ P 39 40/\
     P 40 41/\ P 41 42/\ P 42 43/\ P 43 44/\ P 44 45/\ P 45 46 /\ P 46 47/\ P 47 48/\ P 48 49/\ P 49 50/\
     P 50 51/\ P 51 52/\ P 52 53/\ P 53 54/\ P 54 55/\ P 55 0).
Proof.
intros.
split.  
intros.
repeat split;match goal with |- P ?X ?Y   => rewrite <- PeanoNat.Nat.mod_small with (a:=X) (b:=56) by lia end; apply H.
intros.
destruct (modulo_prop n) as [p [Hp Hp']].
destruct (modulo_prop (S n)) as [q [Hq Hq']].
destruct (modulo_S n) as [HA | HB].
rewrite Hp' Hq' in HA.
rewrite Hp' Hq'.
apply n56_decomp in Hp.
apply n56_decomp in Hq.
clear Hp' Hq'.
rewrite HA in Hq.
rewrite HA.
clear n.
intuition; match goal with H:p=?i, H':S p=?j |- _ => rewrite H in H'; try solve [ discriminate | rewrite H; assumption] end.
destruct HB as [HB1 HB2].
rewrite HB1.
rewrite HB2. 
intuition.
Qed.

Lemma all_isomorphic_lemma :  forall t1 t2 : list Line, In t1 spreads -> In t2 spreads -> are_isomorphic t1 t2. 
Proof.
  apply all_equiv.
  simpl; lia.
  apply are_isomorphic_refl.
  apply are_isomorphic_trans.
  unfold all_iso_decomp.
  intros n.
  apply equiv'.
  repeat split.
  intros.
  exists fp0_1; exists fl0_1; split; [is_col |reflexivity].
  exists fp1_2; exists fl1_2; split; [is_col |reflexivity].
  exists fp2_3; exists fl2_3; split; [is_col |reflexivity].
  exists fp3_4; exists fl3_4; split; [is_col |reflexivity].
  exists fp4_5; exists fl4_5; split; [is_col |reflexivity].
  exists fp5_6; exists fl5_6; split; [is_col |reflexivity].
  exists fp6_7; exists fl6_7; split; [is_col |reflexivity].
  exists fp7_8; exists fl7_8; split; [is_col |reflexivity].
  exists fp8_9; exists fl8_9; split; [is_col |reflexivity].
  exists fp9_10; exists fl9_10; split; [is_col |reflexivity].
  
  exists fp10_11; exists fl10_11; split; [is_col |reflexivity].
  exists fp11_12; exists fl11_12; split; [is_col |reflexivity].
  exists fp12_13; exists fl12_13; split; [is_col |reflexivity].
  exists fp13_14; exists fl13_14; split; [is_col |reflexivity].
  exists fp14_15; exists fl14_15; split; [is_col |reflexivity].
  exists fp15_16; exists fl15_16; split; [is_col |reflexivity].
  exists fp16_17; exists fl16_17; split; [is_col |reflexivity].
  exists fp17_18; exists fl17_18; split; [is_col |reflexivity].
  exists fp18_19; exists fl18_19; split; [is_col |reflexivity].
  exists fp19_20; exists fl19_20; split; [is_col |reflexivity].
  
  exists fp20_21; exists fl20_21; split; [is_col |reflexivity].
  exists fp21_22; exists fl21_22; split; [is_col |reflexivity].
  exists fp22_23; exists fl22_23; split; [is_col |reflexivity].
  exists fp23_24; exists fl23_24; split; [is_col |reflexivity].
  exists fp24_25; exists fl24_25; split; [is_col |reflexivity].
  exists fp25_26; exists fl25_26; split; [is_col |reflexivity].
  exists fp26_27; exists fl26_27; split; [is_col |reflexivity].
  exists fp27_28; exists fl27_28; split; [is_col |reflexivity].
  exists fp28_29; exists fl28_29; split; [is_col |reflexivity].
  exists fp29_30; exists fl29_30; split; [is_col |reflexivity].
  
  exists fp30_31; exists fl30_31; split; [is_col |reflexivity].
  exists fp31_32; exists fl31_32; split; [is_col |reflexivity].
  exists fp32_33; exists fl32_33; split; [is_col |reflexivity].
  exists fp33_34; exists fl33_34; split; [is_col |reflexivity].
  exists fp34_35; exists fl34_35; split; [is_col |reflexivity].
  exists fp35_36; exists fl35_36; split; [is_col |reflexivity].
  exists fp36_37; exists fl36_37; split; [is_col |reflexivity].
  exists fp37_38; exists fl37_38; split; [is_col |reflexivity].
  exists fp38_39; exists fl38_39; split; [is_col |reflexivity].
  exists fp39_40; exists fl39_40; split; [is_col |reflexivity].
  
  exists fp40_41; exists fl40_41; split; [is_col |reflexivity].
  exists fp41_42; exists fl41_42; split; [is_col |reflexivity].
  exists fp42_43; exists fl42_43; split; [is_col |reflexivity].
  exists fp43_44; exists fl43_44; split; [is_col |reflexivity].
  exists fp44_45; exists fl44_45; split; [is_col |reflexivity].
  exists fp45_46; exists fl45_46; split; [is_col |reflexivity].
  exists fp46_47; exists fl46_47; split; [is_col |reflexivity].
  exists fp47_48; exists fl47_48; split; [is_col |reflexivity].
  exists fp48_49; exists fl48_49; split; [is_col |reflexivity].
  exists fp49_50; exists fl49_50; split; [is_col |reflexivity].
  
  exists fp50_51; exists fl50_51; split; [is_col |reflexivity].
  exists fp51_52; exists fl51_52; split; [is_col |reflexivity].
  exists fp52_53; exists fl52_53; split; [is_col |reflexivity].
  exists fp53_54; exists fl53_54; split; [is_col |reflexivity].
  exists fp54_55; exists fl54_55; split; [is_col |reflexivity].
  exists fp55_0; exists fl55_0; split; [is_col |reflexivity].
Qed. 

