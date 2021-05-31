Require Import ssreflect ssrfun ssrbool.
Require Import Generic.lemmas Generic.wlog.
Require Import PG32.pg32_inductive PG32.pg32_proofs.
(*
Inductive Point := | P0 | P1 | P2 | P3 | P4 | P5 | P6 | P7 | P8 | P9 | P10 | P11 | P12 | P13 | P14 .

Inductive Line := | L0 | L1 | L2 | L3 | L4 | L5 | L6 | L7 | L8 | L9 | L10 | L11 | L12 | L13 | L14 | L15 | L16 | L17 | L18 | L19 | L20 | L21 | L22 | L23 | L24 | L25 | L26 | L27 | L28 | L29 | L30 | L31 | L32 | L33 | L34 .
 *)

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

