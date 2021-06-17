Require Import ssreflect ssrfun ssrbool.
Require Import Generic.lemmas Generic.wlog.
Require Import PG32.pg32_inductive PG32.pg32_spreads_packings PG32.pg32_spreads_collineations.

Require Import Lia.

(* ~~~~~~~~~~ CLASS 0 ~~~~~~~~~~ *)
(* P0 : S0 S9 S19 S24 S36 S46 S53 -> 
   P3 : S0 S9 S20 S28 S35 S40 S55  *)
Definition fp0_3 (p:Point) := match p with P0 => P10 | P1 => P3 | P2 => P14 | P3 => P1 | P4 => P8 | P5 => P5 | P6 => P12 | P7 => P13 | P8 => P4 | P9 => P9 | P10 => P0 | P11 => P11 | P12 => P6 | P13 => P7 | P14 => P2 end.
Definition fl0_3 (l:Line) := match l with L0 => L19 | L1 => L8 | L2 => L30 | L3 => L25 | L4 => L4 | L5 => L34 | L6 => L13 | L7 => L20 | L8 => L1 | L9 => L15 | L10 => L21 | L11 => L22 | L12 => L12 | L13 => L6 | L14 => L14 | L15 => L9 | L16 => L31 | L17 => L27 | L18 => L23 | L19 => L0 | L20 => L7 | L21 => L10 | L22 => L11 | L23 => L18 | L24 => L24 | L25 => L3 | L26 => L32 | L27 => L17 | L28 => L28 | L29 => L29 | L30 => L2 | L31 => L16 | L32 => L26 | L33 => L33 | L34 => L5 end.

(* P3 : S0 S9 S20 S28 S35 S40 S55 -> 
   P5 : S0 S9 S22 S27 S38 S44 S49  *)
Definition fp3_5 (p:Point) := match p with P0 => P8 | P1 => P4 | P2 => P11 | P3 => P1 | P4 => P10 | P5 => P6 | P6 => P13 | P7 => P12 | P8 => P3 | P9 => P7 | P10 => P0 | P11 => P14 | P12 => P5 | P13 => P9 | P14 => P2 end.
Definition fl3_5 (l:Line) := match l with L0 => L24 | L1 => L8 | L2 => L32 | L3 => L20 | L4 => L3 | L5 => L27 | L6 => L18 | L7 => L25 | L8 => L1 | L9 => L17 | L10 => L26 | L11 => L23 | L12 => L7 | L13 => L5 | L14 => L14 | L15 => L11 | L16 => L29 | L17 => L34 | L18 => L22 | L19 => L0 | L20 => L12 | L21 => L10 | L22 => L9 | L23 => L13 | L24 => L19 | L25 => L4 | L26 => L30 | L27 => L15 | L28 => L33 | L29 => L31 | L30 => L2 | L31 => L16 | L32 => L21 | L33 => L28 | L34 => L6 end.

(* P5 : S0 S9 S22 S27 S38 S44 S49 -> 
   P6 : S0 S10 S16 S28 S33 S47 S53  *)
Definition fp5_6 (p:Point) := match p with P0 => P6 | P1 => P9 | P2 => P12 | P3 => P13 | P4 => P8 | P5 => P3 | P6 => P2 | P7 => P10 | P8 => P11 | P9 => P0 | P10 => P5 | P11 => P4 | P12 => P1 | P13 => P14 | P14 => P7 end.
Definition fl5_6 (l:Line) := match l with L0 => L33 | L1 => L32 | L2 => L15 | L3 => L34 | L4 => L2 | L5 => L7 | L6 => L31 | L7 => L18 | L8 => L29 | L9 => L10 | L10 => L4 | L11 => L23 | L12 => L21 | L13 => L30 | L14 => L26 | L15 => L16 | L16 => L9 | L17 => L20 | L18 => L5 | L19 => L28 | L20 => L11 | L21 => L6 | L22 => L25 | L23 => L3 | L24 => L24 | L25 => L27 | L26 => L8 | L27 => L22 | L28 => L19 | L29 => L1 | L30 => L12 | L31 => L13 | L32 => L14 | L33 => L0 | L34 => L17 end.

(* P6 : S0 S10 S16 S28 S33 S47 S53 -> 
   P9 : S0 S10 S17 S24 S37 S44 S55  *)
Definition fp6_9 (p:Point) := match p with P0 => P2 | P1 => P0 | P2 => P1 | P3 => P10 | P4 => P7 | P5 => P9 | P6 => P8 | P7 => P12 | P8 => P13 | P9 => P11 | P10 => P14 | P11 => P5 | P12 => P4 | P13 => P6 | P14 => P3 end.
Definition fl6_9 (l:Line) := match l with L0 => L0 | L1 => L13 | L2 => L18 | L3 => L16 | L4 => L14 | L5 => L17 | L6 => L15 | L7 => L3 | L8 => L6 | L9 => L1 | L10 => L5 | L11 => L2 | L12 => L4 | L13 => L9 | L14 => L12 | L15 => L8 | L16 => L7 | L17 => L10 | L18 => L11 | L19 => L19 | L20 => L25 | L21 => L34 | L22 => L30 | L23 => L22 | L24 => L28 | L25 => L31 | L26 => L26 | L27 => L21 | L28 => L33 | L29 => L29 | L30 => L23 | L31 => L20 | L32 => L32 | L33 => L24 | L34 => L27 end.

(* P9 : S0 S10 S17 S24 S37 S44 S55 -> 
   P11 : S0 S10 S20 S31 S36 S43 S49  *)
Definition fp9_11 (p:Point) := match p with P0 => P0 | P1 => P2 | P2 => P1 | P3 => P3 | P4 => P4 | P5 => P6 | P6 => P5 | P7 => P12 | P8 => P11 | P9 => P13 | P10 => P14 | P11 => P8 | P12 => P7 | P13 => P9 | P14 => P10 end.
Definition fl9_11 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L5 | L4 => L6 | L5 => L3 | L6 => L4 | L7 => L17 | L8 => L14 | L9 => L13 | L10 => L16 | L11 => L18 | L12 => L15 | L13 => L9 | L14 => L8 | L15 => L12 | L16 => L10 | L17 => L7 | L18 => L11 | L19 => L19 | L20 => L22 | L21 => L21 | L22 => L20 | L23 => L25 | L24 => L24 | L25 => L23 | L26 => L26 | L27 => L34 | L28 => L33 | L29 => L32 | L30 => L31 | L31 => L30 | L32 => L29 | L33 => L28 | L34 => L27 end.

(* P11 : S0 S10 S20 S31 S36 S43 S49 -> 
   P13 : S0 S12 S17 S27 S36 S47 S48  *)
Definition fp11_13 (p:Point) := match p with P0 => P5 | P1 => P7 | P2 => P13 | P3 => P12 | P4 => P10 | P5 => P4 | P6 => P2 | P7 => P8 | P8 => P14 | P9 => P0 | P10 => P6 | P11 => P3 | P12 => P1 | P13 => P11 | P14 => P9 end.
Definition fl11_13 (l:Line) := match l with L0 => L28 | L1 => L30 | L2 => L17 | L3 => L27 | L4 => L2 | L5 => L12 | L6 => L29 | L7 => L13 | L8 => L31 | L9 => L10 | L10 => L3 | L11 => L22 | L12 => L26 | L13 => L32 | L14 => L21 | L15 => L16 | L16 => L11 | L17 => L25 | L18 => L6 | L19 => L33 | L20 => L9 | L21 => L5 | L22 => L20 | L23 => L4 | L24 => L19 | L25 => L34 | L26 => L8 | L27 => L23 | L28 => L24 | L29 => L1 | L30 => L7 | L31 => L18 | L32 => L14 | L33 => L0 | L34 => L15 end.

(* P13 : S0 S12 S17 S27 S36 S47 S48 -> 
   P15 : S0 S12 S19 S31 S37 S40 S50  *)
Definition fp13_15 (p:Point) := match p with P0 => P4 | P1 => P8 | P2 => P11 | P3 => P0 | P4 => P3 | P5 => P7 | P6 => P12 | P7 => P13 | P8 => P10 | P9 => P6 | P10 => P1 | P11 => P14 | P12 => P9 | P13 => P5 | P14 => P2 end.
Definition fl13_15 (l:Line) := match l with L0 => L24 | L1 => L1 | L2 => L26 | L3 => L25 | L4 => L7 | L5 => L23 | L6 => L17 | L7 => L20 | L8 => L8 | L9 => L18 | L10 => L32 | L11 => L27 | L12 => L3 | L13 => L11 | L14 => L14 | L15 => L5 | L16 => L29 | L17 => L22 | L18 => L34 | L19 => L0 | L20 => L4 | L21 => L2 | L22 => L6 | L23 => L15 | L24 => L19 | L25 => L12 | L26 => L21 | L27 => L13 | L28 => L28 | L29 => L31 | L30 => L10 | L31 => L16 | L32 => L30 | L33 => L33 | L34 => L9 end.

(* P15 : S0 S12 S19 S31 S37 S40 S50 -> 
   P16 : S0 S12 S22 S26 S33 S43 S55  *)
Definition fp15_16 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P4 | P4 => P3 | P5 => P6 | P6 => P5 | P7 => P9 | P8 => P10 | P9 => P7 | P10 => P8 | P11 => P14 | P12 => P13 | P13 => P12 | P14 => P11 end.
Definition fl15_16 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L4 | L4 => L3 | L5 => L6 | L6 => L5 | L7 => L12 | L8 => L8 | L9 => L11 | L10 => L10 | L11 => L9 | L12 => L7 | L13 => L18 | L14 => L14 | L15 => L17 | L16 => L16 | L17 => L15 | L18 => L13 | L19 => L24 | L20 => L25 | L21 => L26 | L22 => L23 | L23 => L22 | L24 => L19 | L25 => L20 | L26 => L21 | L27 => L34 | L28 => L33 | L29 => L31 | L30 => L32 | L31 => L29 | L32 => L30 | L33 => L28 | L34 => L27 end.

(* P16 : S0 S12 S22 S26 S33 S43 S55 -> 
   P18 : S0 S13 S16 S26 S37 S46 S49  *)
Definition fp16_18 (p:Point) := match p with P0 => P13 | P1 => P5 | P2 => P7 | P3 => P2 | P4 => P12 | P5 => P4 | P6 => P10 | P7 => P8 | P8 => P6 | P9 => P14 | P10 => P0 | P11 => P9 | P12 => P3 | P13 => P11 | P14 => P1 end.
Definition fl16_18 (l:Line) := match l with L0 => L28 | L1 => L16 | L2 => L25 | L3 => L32 | L4 => L6 | L5 => L21 | L6 => L11 | L7 => L30 | L8 => L2 | L9 => L12 | L10 => L27 | L11 => L29 | L12 => L17 | L13 => L3 | L14 => L10 | L15 => L13 | L16 => L22 | L17 => L26 | L18 => L31 | L19 => L0 | L20 => L15 | L21 => L14 | L22 => L18 | L23 => L9 | L24 => L33 | L25 => L5 | L26 => L20 | L27 => L7 | L28 => L24 | L29 => L23 | L30 => L1 | L31 => L8 | L32 => L34 | L33 => L19 | L34 => L4 end.

(* P18 : S0 S13 S16 S26 S37 S46 S49 -> 
   P21 : S0 S13 S19 S28 S38 S43 S48  *)
Definition fp18_21 (p:Point) := match p with P0 => P5 | P1 => P13 | P2 => P7 | P3 => P8 | P4 => P14 | P5 => P6 | P6 => P0 | P7 => P12 | P8 => P10 | P9 => P2 | P10 => P4 | P11 => P3 | P12 => P1 | P13 => P9 | P14 => P11 end.
Definition fl18_21 (l:Line) := match l with L0 => L28 | L1 => L27 | L2 => L2 | L3 => L30 | L4 => L17 | L5 => L12 | L6 => L29 | L7 => L6 | L8 => L25 | L9 => L11 | L10 => L16 | L11 => L21 | L12 => L32 | L13 => L26 | L14 => L22 | L15 => L3 | L16 => L10 | L17 => L31 | L18 => L13 | L19 => L24 | L20 => L8 | L21 => L18 | L22 => L20 | L23 => L14 | L24 => L19 | L25 => L23 | L26 => L9 | L27 => L34 | L28 => L33 | L29 => L15 | L30 => L7 | L31 => L5 | L32 => L4 | L33 => L0 | L34 => L1 end.

(* P21 : S0 S13 S19 S28 S38 S43 S48 -> 
   P22 : S0 S13 S22 S24 S35 S47 S50  *)
Definition fp21_22 (p:Point) := match p with P0 => P5 | P1 => P13 | P2 => P7 | P3 => P8 | P4 => P14 | P5 => P6 | P6 => P0 | P7 => P12 | P8 => P10 | P9 => P2 | P10 => P4 | P11 => P3 | P12 => P1 | P13 => P9 | P14 => P11 end.
Definition fl21_22 (l:Line) := match l with L0 => L28 | L1 => L27 | L2 => L2 | L3 => L30 | L4 => L17 | L5 => L12 | L6 => L29 | L7 => L6 | L8 => L25 | L9 => L11 | L10 => L16 | L11 => L21 | L12 => L32 | L13 => L26 | L14 => L22 | L15 => L3 | L16 => L10 | L17 => L31 | L18 => L13 | L19 => L24 | L20 => L8 | L21 => L18 | L22 => L20 | L23 => L14 | L24 => L19 | L25 => L23 | L26 => L9 | L27 => L34 | L28 => L33 | L29 => L15 | L30 => L7 | L31 => L5 | L32 => L4 | L33 => L0 | L34 => L1 end.

(* P22 : S0 S13 S22 S24 S35 S47 S50 -> 
   P25 : S0 S15 S16 S31 S35 S44 S48  *)
Definition fp22_25 (p:Point) := match p with P0 => P13 | P1 => P5 | P2 => P7 | P3 => P11 | P4 => P1 | P5 => P9 | P6 => P3 | P7 => P12 | P8 => P2 | P9 => P10 | P10 => P4 | P11 => P0 | P12 => P14 | P13 => P6 | P14 => P8 end.
Definition fl22_25 (l:Line) := match l with L0 => L28 | L1 => L11 | L2 => L21 | L3 => L16 | L4 => L25 | L5 => L6 | L6 => L32 | L7 => L12 | L8 => L17 | L9 => L27 | L10 => L30 | L11 => L2 | L12 => L29 | L13 => L26 | L14 => L3 | L15 => L22 | L16 => L31 | L17 => L10 | L18 => L13 | L19 => L24 | L20 => L14 | L21 => L34 | L22 => L5 | L23 => L8 | L24 => L0 | L25 => L7 | L26 => L9 | L27 => L18 | L28 => L33 | L29 => L4 | L30 => L23 | L31 => L20 | L32 => L15 | L33 => L19 | L34 => L1 end.

(* P25 : S0 S15 S16 S31 S35 S44 S48 -> 
   P26 : S0 S15 S17 S26 S38 S40 S53  *)
Definition fp25_26 (p:Point) := match p with P0 => P8 | P1 => P4 | P2 => P11 | P3 => P9 | P4 => P2 | P5 => P14 | P6 => P5 | P7 => P10 | P8 => P1 | P9 => P13 | P10 => P6 | P11 => P0 | P12 => P7 | P13 => P3 | P14 => P12 end.
Definition fl25_26 (l:Line) := match l with L0 => L24 | L1 => L18 | L2 => L27 | L3 => L8 | L4 => L32 | L5 => L3 | L6 => L20 | L7 => L17 | L8 => L7 | L9 => L26 | L10 => L25 | L11 => L1 | L12 => L23 | L13 => L34 | L14 => L5 | L15 => L29 | L16 => L22 | L17 => L14 | L18 => L11 | L19 => L33 | L20 => L10 | L21 => L21 | L22 => L4 | L23 => L16 | L24 => L0 | L25 => L15 | L26 => L13 | L27 => L9 | L28 => L19 | L29 => L6 | L30 => L31 | L31 => L30 | L32 => L12 | L33 => L28 | L34 => L2 end.

(* P26 : S0 S15 S17 S26 S38 S40 S53 -> 
   P28 : S0 S15 S20 S27 S33 S46 S50  *)
Definition fp26_28 (p:Point) := match p with P0 => P0 | P1 => P2 | P2 => P1 | P3 => P3 | P4 => P4 | P5 => P6 | P6 => P5 | P7 => P12 | P8 => P11 | P9 => P13 | P10 => P14 | P11 => P8 | P12 => P7 | P13 => P9 | P14 => P10 end.
Definition fl26_28 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L5 | L4 => L6 | L5 => L3 | L6 => L4 | L7 => L17 | L8 => L14 | L9 => L13 | L10 => L16 | L11 => L18 | L12 => L15 | L13 => L9 | L14 => L8 | L15 => L12 | L16 => L10 | L17 => L7 | L18 => L11 | L19 => L19 | L20 => L22 | L21 => L21 | L22 => L20 | L23 => L25 | L24 => L24 | L25 => L23 | L26 => L26 | L27 => L34 | L28 => L33 | L29 => L32 | L30 => L31 | L31 => L30 | L32 => L29 | L33 => L28 | L34 => L27 end.

(* P28 : S0 S15 S20 S27 S33 S46 S50 -> 
   P31 : S1 S8 S18 S31 S37 S44 S49  *)
Definition fp28_31 (p:Point) := match p with P0 => P2 | P1 => P0 | P2 => P1 | P3 => P11 | P4 => P14 | P5 => P12 | P6 => P13 | P7 => P7 | P8 => P10 | P9 => P8 | P10 => P9 | P11 => P3 | P12 => P6 | P13 => P4 | P14 => P5 end.
Definition fl28_31 (l:Line) := match l with L0 => L0 | L1 => L14 | L2 => L16 | L3 => L13 | L4 => L18 | L5 => L15 | L6 => L17 | L7 => L6 | L8 => L4 | L9 => L2 | L10 => L3 | L11 => L1 | L12 => L5 | L13 => L10 | L14 => L12 | L15 => L11 | L16 => L7 | L17 => L9 | L18 => L8 | L19 => L29 | L20 => L34 | L21 => L24 | L22 => L22 | L23 => L27 | L24 => L19 | L25 => L23 | L26 => L31 | L27 => L30 | L28 => L26 | L29 => L20 | L30 => L33 | L31 => L28 | L32 => L25 | L33 => L32 | L34 => L21 end.

(* P31 : S1 S8 S18 S31 S37 S44 S49 -> 
   P32 : S1 S8 S19 S28 S39 S40 S53  *)
Definition fp31_32 (p:Point) := match p with P0 => P2 | P1 => P1 | P2 => P0 | P3 => P14 | P4 => P11 | P5 => P12 | P6 => P13 | P7 => P9 | P8 => P8 | P9 => P7 | P10 => P10 | P11 => P4 | P12 => P5 | P13 => P6 | P14 => P3 end.
Definition fl31_32 (l:Line) := match l with L0 => L0 | L1 => L14 | L2 => L16 | L3 => L18 | L4 => L13 | L5 => L17 | L6 => L15 | L7 => L11 | L8 => L8 | L9 => L12 | L10 => L10 | L11 => L7 | L12 => L9 | L13 => L4 | L14 => L1 | L15 => L6 | L16 => L2 | L17 => L5 | L18 => L3 | L19 => L19 | L20 => L27 | L21 => L31 | L22 => L23 | L23 => L22 | L24 => L24 | L25 => L34 | L26 => L29 | L27 => L20 | L28 => L33 | L29 => L26 | L30 => L30 | L31 => L21 | L32 => L32 | L33 => L28 | L34 => L25 end.

(* P32 : S1 S8 S19 S28 S39 S40 S53 -> 
   P34 : S1 S8 S22 S27 S33 S47 S52  *)
Definition fp32_34 (p:Point) := match p with P0 => P0 | P1 => P2 | P2 => P1 | P3 => P3 | P4 => P4 | P5 => P6 | P6 => P5 | P7 => P12 | P8 => P11 | P9 => P13 | P10 => P14 | P11 => P8 | P12 => P7 | P13 => P9 | P14 => P10 end.
Definition fl32_34 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L5 | L4 => L6 | L5 => L3 | L6 => L4 | L7 => L17 | L8 => L14 | L9 => L13 | L10 => L16 | L11 => L18 | L12 => L15 | L13 => L9 | L14 => L8 | L15 => L12 | L16 => L10 | L17 => L7 | L18 => L11 | L19 => L19 | L20 => L22 | L21 => L21 | L22 => L20 | L23 => L25 | L24 => L24 | L25 => L23 | L26 => L26 | L27 => L34 | L28 => L33 | L29 => L32 | L30 => L31 | L31 => L30 | L32 => L29 | L33 => L28 | L34 => L27 end.

(* P34 : S1 S8 S22 S27 S33 S47 S52 -> 
   P37 : S1 S11 S17 S30 S37 S40 S52  *)
Definition fp34_37 (p:Point) := match p with P0 => P9 | P1 => P11 | P2 => P5 | P3 => P8 | P4 => P2 | P5 => P4 | P6 => P14 | P7 => P0 | P8 => P10 | P9 => P12 | P10 => P6 | P11 => P7 | P12 => P1 | P13 => P3 | P14 => P13 end.
Definition fl34_37 (l:Line) := match l with L0 => L29 | L1 => L18 | L2 => L23 | L3 => L4 | L4 => L33 | L5 => L10 | L6 => L21 | L7 => L14 | L8 => L34 | L9 => L11 | L10 => L5 | L11 => L22 | L12 => L24 | L13 => L2 | L14 => L28 | L15 => L27 | L16 => L12 | L17 => L17 | L18 => L30 | L19 => L32 | L20 => L8 | L21 => L20 | L22 => L3 | L23 => L16 | L24 => L13 | L25 => L15 | L26 => L0 | L27 => L25 | L28 => L1 | L29 => L26 | L30 => L7 | L31 => L6 | L32 => L19 | L33 => L9 | L34 => L31 end.

(* P37 : S1 S11 S17 S30 S37 S40 S52 -> 
   P38 : S1 S11 S20 S28 S33 S43 S54  *)
Definition fp37_38 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P4 | P4 => P3 | P5 => P6 | P6 => P5 | P7 => P10 | P8 => P9 | P9 => P8 | P10 => P7 | P11 => P13 | P12 => P14 | P13 => P11 | P14 => P12 end.
Definition fl37_38 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L4 | L4 => L3 | L5 => L6 | L6 => L5 | L7 => L12 | L8 => L10 | L9 => L9 | L10 => L8 | L11 => L11 | L12 => L7 | L13 => L13 | L14 => L16 | L15 => L17 | L16 => L14 | L17 => L15 | L18 => L18 | L19 => L26 | L20 => L23 | L21 => L24 | L22 => L25 | L23 => L20 | L24 => L21 | L25 => L22 | L26 => L19 | L27 => L33 | L28 => L34 | L29 => L32 | L30 => L31 | L31 => L30 | L32 => L29 | L33 => L27 | L34 => L28 end.

(* P38 : S1 S11 S20 S28 S33 S43 S54 -> 
   P40 : S1 S11 S22 S24 S39 S44 S51  *)
Definition fp38_40 (p:Point) := match p with P0 => P3 | P1 => P14 | P2 => P10 | P3 => P4 | P4 => P0 | P5 => P9 | P6 => P13 | P7 => P2 | P8 => P6 | P9 => P11 | P10 => P7 | P11 => P5 | P12 => P1 | P13 => P8 | P14 => P12 end.
Definition fl38_40 (l:Line) := match l with L0 => L19 | L1 => L1 | L2 => L21 | L3 => L15 | L4 => L22 | L5 => L12 | L6 => L20 | L7 => L6 | L8 => L31 | L9 => L9 | L10 => L14 | L11 => L27 | L12 => L23 | L13 => L13 | L14 => L30 | L15 => L25 | L16 => L8 | L17 => L4 | L18 => L34 | L19 => L26 | L20 => L7 | L21 => L24 | L22 => L17 | L23 => L5 | L24 => L2 | L25 => L3 | L26 => L0 | L27 => L33 | L28 => L18 | L29 => L29 | L30 => L10 | L31 => L16 | L32 => L32 | L33 => L11 | L34 => L28 end.

(* P40 : S1 S11 S22 S24 S39 S44 S51 -> 
   P42 : S1 S13 S18 S28 S32 S47 S51  *)
Definition fp40_42 (p:Point) := match p with P0 => P14 | P1 => P10 | P2 => P3 | P3 => P8 | P4 => P5 | P5 => P1 | P6 => P12 | P7 => P9 | P8 => P4 | P9 => P0 | P10 => P13 | P11 => P2 | P12 => P11 | P13 => P7 | P14 => P6 end.
Definition fl40_42 (l:Line) := match l with L0 => L19 | L1 => L27 | L2 => L9 | L3 => L23 | L4 => L6 | L5 => L14 | L6 => L31 | L7 => L30 | L8 => L25 | L9 => L34 | L10 => L4 | L11 => L13 | L12 => L8 | L13 => L21 | L14 => L15 | L15 => L20 | L16 => L22 | L17 => L12 | L18 => L1 | L19 => L32 | L20 => L24 | L21 => L3 | L22 => L18 | L23 => L2 | L24 => L17 | L25 => L28 | L26 => L29 | L27 => L7 | L28 => L10 | L29 => L0 | L30 => L11 | L31 => L33 | L32 => L26 | L33 => L5 | L34 => L16 end.

(* P42 : S1 S13 S18 S28 S32 S47 S51 -> 
   P44 : S1 S13 S19 S24 S37 S42 S54  *)
Definition fp42_44 (p:Point) := match p with P0 => P12 | P1 => P7 | P2 => P4 | P3 => P13 | P4 => P2 | P5 => P5 | P6 => P10 | P7 => P1 | P8 => P14 | P9 => P9 | P10 => P6 | P11 => P11 | P12 => P0 | P13 => P3 | P14 => P8 end.
Definition fl42_44 (l:Line) := match l with L0 => L26 | L1 => L16 | L2 => L30 | L3 => L9 | L4 => L33 | L5 => L5 | L6 => L20 | L7 => L13 | L8 => L31 | L9 => L3 | L10 => L10 | L11 => L22 | L12 => L28 | L13 => L7 | L14 => L24 | L15 => L25 | L16 => L1 | L17 => L17 | L18 => L23 | L19 => L32 | L20 => L6 | L21 => L21 | L22 => L11 | L23 => L18 | L24 => L14 | L25 => L15 | L26 => L0 | L27 => L27 | L28 => L12 | L29 => L29 | L30 => L2 | L31 => L8 | L32 => L19 | L33 => L4 | L34 => L34 end.

(* P44 : S1 S13 S19 S24 S37 S42 S54 -> 
   P47 : S1 S13 S22 S30 S34 S43 S49  *)
Definition fp44_47 (p:Point) := match p with P0 => P0 | P1 => P2 | P2 => P1 | P3 => P3 | P4 => P4 | P5 => P6 | P6 => P5 | P7 => P12 | P8 => P11 | P9 => P13 | P10 => P14 | P11 => P8 | P12 => P7 | P13 => P9 | P14 => P10 end.
Definition fl44_47 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L5 | L4 => L6 | L5 => L3 | L6 => L4 | L7 => L17 | L8 => L14 | L9 => L13 | L10 => L16 | L11 => L18 | L12 => L15 | L13 => L9 | L14 => L8 | L15 => L12 | L16 => L10 | L17 => L7 | L18 => L11 | L19 => L19 | L20 => L22 | L21 => L21 | L22 => L20 | L23 => L25 | L24 => L24 | L25 => L23 | L26 => L26 | L27 => L34 | L28 => L33 | L29 => L32 | L30 => L31 | L31 => L30 | L32 => L29 | L33 => L28 | L34 => L27 end.

(* P47 : S1 S13 S22 S30 S34 S43 S49 -> 
   P48 : S1 S14 S17 S24 S34 S47 S53  *)
Definition fp47_48 (p:Point) := match p with P0 => P11 | P1 => P9 | P2 => P5 | P3 => P1 | P4 => P13 | P5 => P7 | P6 => P3 | P7 => P6 | P8 => P10 | P9 => P12 | P10 => P0 | P11 => P4 | P12 => P8 | P13 => P14 | P14 => P2 end.
Definition fl47_48 (l:Line) := match l with L0 => L29 | L1 => L11 | L2 => L22 | L3 => L34 | L4 => L5 | L5 => L24 | L6 => L14 | L7 => L21 | L8 => L4 | L9 => L18 | L10 => L33 | L11 => L23 | L12 => L10 | L13 => L2 | L14 => L17 | L15 => L12 | L16 => L27 | L17 => L28 | L18 => L30 | L19 => L0 | L20 => L8 | L21 => L9 | L22 => L7 | L23 => L16 | L24 => L25 | L25 => L6 | L26 => L32 | L27 => L13 | L28 => L31 | L29 => L26 | L30 => L3 | L31 => L15 | L32 => L19 | L33 => L20 | L34 => L1 end.

(* P48 : S1 S14 S17 S24 S34 S47 S53 -> 
   P51 : S1 S14 S19 S31 S32 S43 S52  *)
Definition fp48_51 (p:Point) := match p with P0 => P10 | P1 => P14 | P2 => P3 | P3 => P7 | P4 => P2 | P5 => P6 | P6 => P11 | P7 => P0 | P8 => P9 | P9 => P13 | P10 => P4 | P11 => P8 | P12 => P1 | P13 => P5 | P14 => P12 end.
Definition fl48_51 (l:Line) := match l with L0 => L19 | L1 => L13 | L2 => L34 | L3 => L4 | L4 => L25 | L5 => L8 | L6 => L30 | L7 => L14 | L8 => L23 | L9 => L9 | L10 => L6 | L11 => L27 | L12 => L31 | L13 => L1 | L14 => L20 | L15 => L22 | L16 => L12 | L17 => L15 | L18 => L21 | L19 => L26 | L20 => L10 | L21 => L28 | L22 => L3 | L23 => L16 | L24 => L18 | L25 => L17 | L26 => L0 | L27 => L33 | L28 => L2 | L29 => L32 | L30 => L7 | L31 => L5 | L32 => L29 | L33 => L11 | L34 => L24 end.

(* P51 : S1 S14 S19 S31 S32 S43 S52 -> 
   P52 : S1 S14 S20 S27 S39 S42 S49  *)
Definition fp51_52 (p:Point) := match p with P0 => P10 | P1 => P14 | P2 => P3 | P3 => P2 | P4 => P7 | P5 => P11 | P6 => P6 | P7 => P4 | P8 => P13 | P9 => P9 | P10 => P0 | P11 => P5 | P12 => P12 | P13 => P8 | P14 => P1 end.
Definition fl51_52 (l:Line) := match l with L0 => L19 | L1 => L13 | L2 => L34 | L3 => L25 | L4 => L4 | L5 => L30 | L6 => L8 | L7 => L31 | L8 => L6 | L9 => L9 | L10 => L23 | L11 => L27 | L12 => L14 | L13 => L1 | L14 => L12 | L15 => L15 | L16 => L20 | L17 => L22 | L18 => L21 | L19 => L0 | L20 => L16 | L21 => L18 | L22 => L17 | L23 => L10 | L24 => L28 | L25 => L3 | L26 => L26 | L27 => L11 | L28 => L24 | L29 => L29 | L30 => L5 | L31 => L7 | L32 => L32 | L33 => L33 | L34 => L2 end.

(* P52 : S1 S14 S20 S27 S39 S42 S49 -> 
   P54 : S1 S15 S17 S27 S32 S44 S54  *)
Definition fp52_54 (p:Point) := match p with P0 => P1 | P1 => P0 | P2 => P2 | P3 => P11 | P4 => P13 | P5 => P12 | P6 => P14 | P7 => P8 | P8 => P10 | P9 => P7 | P10 => P9 | P11 => P4 | P12 => P6 | P13 => P3 | P14 => P5 end.
Definition fl52_54 (l:Line) := match l with L0 => L0 | L1 => L11 | L2 => L9 | L3 => L8 | L4 => L10 | L5 => L7 | L6 => L12 | L7 => L6 | L8 => L4 | L9 => L2 | L10 => L3 | L11 => L1 | L12 => L5 | L13 => L18 | L14 => L17 | L15 => L14 | L16 => L15 | L17 => L16 | L18 => L13 | L19 => L29 | L20 => L34 | L21 => L22 | L22 => L24 | L23 => L28 | L24 => L25 | L25 => L21 | L26 => L32 | L27 => L30 | L28 => L20 | L29 => L26 | L30 => L33 | L31 => L27 | L32 => L19 | L33 => L31 | L34 => L23 end.

(* P54 : S1 S15 S17 S27 S32 S44 S54 -> 
   P56 : S1 S15 S18 S30 S33 S42 S53  *)
Definition fp54_56 (p:Point) := match p with P0 => P6 | P1 => P13 | P2 => P8 | P3 => P14 | P4 => P7 | P5 => P0 | P6 => P5 | P7 => P12 | P8 => P9 | P9 => P2 | P10 => P3 | P11 => P1 | P12 => P4 | P13 => P11 | P14 => P10 end.
Definition fl54_56 (l:Line) := match l with L0 => L32 | L1 => L31 | L2 => L2 | L3 => L33 | L4 => L15 | L5 => L7 | L6 => L34 | L7 => L28 | L8 => L21 | L9 => L25 | L10 => L16 | L11 => L11 | L12 => L6 | L13 => L20 | L14 => L8 | L15 => L27 | L16 => L24 | L17 => L3 | L18 => L18 | L19 => L19 | L20 => L23 | L21 => L14 | L22 => L9 | L23 => L13 | L24 => L10 | L25 => L22 | L26 => L26 | L27 => L4 | L28 => L5 | L29 => L0 | L30 => L1 | L31 => L30 | L32 => L29 | L33 => L17 | L34 => L12 end.

(* P56 : S1 S15 S18 S30 S33 S42 S53 -> 
   P59 : S1 S15 S20 S31 S34 S40 S51  *)
Definition fp56_59 (p:Point) := match p with P0 => P6 | P1 => P8 | P2 => P13 | P3 => P7 | P4 => P14 | P5 => P0 | P6 => P5 | P7 => P10 | P8 => P11 | P9 => P1 | P10 => P4 | P11 => P2 | P12 => P3 | P13 => P9 | P14 => P12 end.
Definition fl56_59 (l:Line) := match l with L0 => L32 | L1 => L31 | L2 => L2 | L3 => L34 | L4 => L7 | L5 => L15 | L6 => L33 | L7 => L27 | L8 => L24 | L9 => L20 | L10 => L8 | L11 => L18 | L12 => L3 | L13 => L25 | L14 => L16 | L15 => L28 | L16 => L21 | L17 => L6 | L18 => L11 | L19 => L26 | L20 => L22 | L21 => L10 | L22 => L13 | L23 => L9 | L24 => L14 | L25 => L23 | L26 => L19 | L27 => L5 | L28 => L4 | L29 => L0 | L30 => L1 | L31 => L30 | L32 => L29 | L33 => L12 | L34 => L17 end.

(* P59 : S1 S15 S20 S31 S34 S40 S51 -> 
   P61 : S2 S9 S18 S30 S36 S45 S49  *)
Definition fp59_61 (p:Point) := match p with P0 => P10 | P1 => P11 | P2 => P6 | P3 => P8 | P4 => P1 | P5 => P4 | P6 => P13 | P7 => P2 | P8 => P7 | P9 => P14 | P10 => P3 | P11 => P9 | P12 => P0 | P13 => P5 | P14 => P12 end.
Definition fl59_61 (l:Line) := match l with L0 => L34 | L1 => L8 | L2 => L25 | L3 => L13 | L4 => L19 | L5 => L4 | L6 => L30 | L7 => L11 | L8 => L22 | L9 => L5 | L10 => L14 | L11 => L29 | L12 => L24 | L13 => L15 | L14 => L33 | L15 => L32 | L16 => L2 | L17 => L7 | L18 => L31 | L19 => L20 | L20 => L3 | L21 => L27 | L22 => L18 | L23 => L9 | L24 => L10 | L25 => L12 | L26 => L0 | L27 => L26 | L28 => L17 | L29 => L23 | L30 => L1 | L31 => L16 | L32 => L28 | L33 => L6 | L34 => L21 end.

(* P61 : S2 S9 S18 S30 S36 S45 S49 -> 
   P63 : S2 S9 S19 S29 S38 S40 S52  *)
Definition fp61_63 (p:Point) := match p with P0 => P12 | P1 => P8 | P2 => P3 | P3 => P2 | P4 => P13 | P5 => P9 | P6 => P6 | P7 => P14 | P8 => P1 | P9 => P5 | P10 => P10 | P11 => P11 | P12 => P0 | P13 => P4 | P14 => P7 end.
Definition fl61_63 (l:Line) := match l with L0 => L20 | L1 => L16 | L2 => L33 | L3 => L9 | L4 => L30 | L5 => L5 | L6 => L26 | L7 => L32 | L8 => L8 | L9 => L3 | L10 => L27 | L11 => L24 | L12 => L18 | L13 => L19 | L14 => L22 | L15 => L15 | L16 => L1 | L17 => L21 | L18 => L12 | L19 => L13 | L20 => L0 | L21 => L17 | L22 => L14 | L23 => L28 | L24 => L11 | L25 => L25 | L26 => L6 | L27 => L10 | L28 => L23 | L29 => L29 | L30 => L4 | L31 => L31 | L32 => L7 | L33 => L2 | L34 => L34 end.

(* P63 : S2 S9 S19 S29 S38 S40 S52 -> 
   P64 : S2 S9 S23 S24 S35 S44 S54  *)
Definition fp63_64 (p:Point) := match p with P0 => P8 | P1 => P12 | P2 => P3 | P3 => P1 | P4 => P10 | P5 => P14 | P6 => P5 | P7 => P9 | P8 => P2 | P9 => P6 | P10 => P13 | P11 => P7 | P12 => P0 | P13 => P4 | P14 => P11 end.
Definition fl63_64 (l:Line) := match l with L0 => L20 | L1 => L8 | L2 => L27 | L3 => L18 | L4 => L32 | L5 => L3 | L6 => L24 | L7 => L30 | L8 => L16 | L9 => L5 | L10 => L33 | L11 => L26 | L12 => L9 | L13 => L21 | L14 => L22 | L15 => L12 | L16 => L1 | L17 => L19 | L18 => L15 | L19 => L11 | L20 => L0 | L21 => L7 | L22 => L10 | L23 => L34 | L24 => L13 | L25 => L25 | L26 => L4 | L27 => L14 | L28 => L23 | L29 => L31 | L30 => L6 | L31 => L29 | L32 => L17 | L33 => L2 | L34 => L28 end.

(* P64 : S2 S9 S23 S24 S35 S44 S54 -> 
   P67 : S2 S10 S16 S29 S39 S44 S49  *)
Definition fp64_67 (p:Point) := match p with P0 => P7 | P1 => P13 | P2 => P5 | P3 => P10 | P4 => P2 | P5 => P4 | P6 => P12 | P7 => P14 | P8 => P6 | P9 => P0 | P10 => P8 | P11 => P3 | P12 => P11 | P13 => P9 | P14 => P1 end.
Definition fl64_67 (l:Line) := match l with L0 => L28 | L1 => L13 | L2 => L26 | L3 => L31 | L4 => L3 | L5 => L22 | L6 => L10 | L7 => L16 | L8 => L32 | L9 => L11 | L10 => L6 | L11 => L21 | L12 => L25 | L13 => L27 | L14 => L12 | L15 => L30 | L16 => L29 | L17 => L17 | L18 => L2 | L19 => L8 | L20 => L34 | L21 => L4 | L22 => L19 | L23 => L0 | L24 => L15 | L25 => L18 | L26 => L14 | L27 => L7 | L28 => L23 | L29 => L1 | L30 => L24 | L31 => L9 | L32 => L33 | L33 => L5 | L34 => L20 end.

(* P67 : S2 S10 S16 S29 S39 S44 S49 -> 
   P68 : S2 S10 S21 S24 S36 S47 S51  *)
Definition fp67_68 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P4 | P4 => P3 | P5 => P6 | P6 => P5 | P7 => P10 | P8 => P9 | P9 => P8 | P10 => P7 | P11 => P13 | P12 => P14 | P13 => P11 | P14 => P12 end.
Definition fl67_68 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L4 | L4 => L3 | L5 => L6 | L6 => L5 | L7 => L12 | L8 => L10 | L9 => L9 | L10 => L8 | L11 => L11 | L12 => L7 | L13 => L13 | L14 => L16 | L15 => L17 | L16 => L14 | L17 => L15 | L18 => L18 | L19 => L26 | L20 => L23 | L21 => L24 | L22 => L25 | L23 => L20 | L24 => L21 | L25 => L22 | L26 => L19 | L27 => L33 | L28 => L34 | L29 => L32 | L30 => L31 | L31 => L30 | L32 => L29 | L33 => L27 | L34 => L28 end.

(* P68 : S2 S10 S21 S24 S36 S47 S51 -> 
   P71 : S2 S10 S23 S30 S33 S43 S52  *)
Definition fp68_71 (p:Point) := match p with P0 => P4 | P1 => P14 | P2 => P9 | P3 => P3 | P4 => P0 | P5 => P10 | P6 => P13 | P7 => P11 | P8 => P8 | P9 => P2 | P10 => P5 | P11 => P7 | P12 => P12 | P13 => P6 | P14 => P1 end.
Definition fl68_71 (l:Line) := match l with L0 => L23 | L1 => L1 | L2 => L25 | L3 => L24 | L4 => L17 | L5 => L26 | L6 => L7 | L7 => L6 | L8 => L27 | L9 => L9 | L10 => L14 | L11 => L31 | L12 => L19 | L13 => L29 | L14 => L10 | L15 => L21 | L16 => L33 | L17 => L4 | L18 => L18 | L19 => L12 | L20 => L20 | L21 => L15 | L22 => L22 | L23 => L0 | L24 => L3 | L25 => L2 | L26 => L5 | L27 => L8 | L28 => L34 | L29 => L13 | L30 => L30 | L31 => L11 | L32 => L32 | L33 => L16 | L34 => L28 end.

(* P71 : S2 S10 S23 S30 S33 S43 S52 -> 
   P73 : S2 S12 S18 S29 S33 S47 S50  *)
Definition fp71_73 (p:Point) := match p with P0 => P10 | P1 => P6 | P2 => P11 | P3 => P5 | P4 => P12 | P5 => P0 | P6 => P9 | P7 => P2 | P8 => P7 | P9 => P3 | P10 => P14 | P11 => P4 | P12 => P13 | P13 => P1 | P14 => P8 end.
Definition fl71_73 (l:Line) := match l with L0 => L34 | L1 => L30 | L2 => L4 | L3 => L13 | L4 => L19 | L5 => L25 | L6 => L8 | L7 => L33 | L8 => L31 | L9 => L32 | L10 => L15 | L11 => L7 | L12 => L2 | L13 => L14 | L14 => L24 | L15 => L29 | L16 => L11 | L17 => L5 | L18 => L22 | L19 => L27 | L20 => L28 | L21 => L12 | L22 => L17 | L23 => L20 | L24 => L26 | L25 => L9 | L26 => L16 | L27 => L3 | L28 => L0 | L29 => L1 | L30 => L6 | L31 => L18 | L32 => L10 | L33 => L21 | L34 => L23 end.

(* P73 : S2 S12 S18 S29 S33 S47 S50 -> 
   P74 : S2 S12 S19 S25 S36 S43 S54  *)
Definition fp73_74 (p:Point) := match p with P0 => P2 | P1 => P1 | P2 => P0 | P3 => P11 | P4 => P14 | P5 => P13 | P6 => P12 | P7 => P7 | P8 => P10 | P9 => P9 | P10 => P8 | P11 => P3 | P12 => P6 | P13 => P5 | P14 => P4 end.
Definition fl73_74 (l:Line) := match l with L0 => L0 | L1 => L14 | L2 => L16 | L3 => L13 | L4 => L18 | L5 => L15 | L6 => L17 | L7 => L9 | L8 => L8 | L9 => L7 | L10 => L10 | L11 => L12 | L12 => L11 | L13 => L3 | L14 => L1 | L15 => L5 | L16 => L2 | L17 => L6 | L18 => L4 | L19 => L24 | L20 => L34 | L21 => L29 | L22 => L22 | L23 => L23 | L24 => L19 | L25 => L27 | L26 => L31 | L27 => L25 | L28 => L28 | L29 => L21 | L30 => L32 | L31 => L26 | L32 => L30 | L33 => L33 | L34 => L20 end.

(* P74 : S2 S12 S19 S25 S36 S43 S54 -> 
   P77 : S2 S12 S23 S26 S39 S40 S51  *)
Definition fp74_77 (p:Point) := match p with P0 => P1 | P1 => P2 | P2 => P0 | P3 => P7 | P4 => P9 | P5 => P10 | P6 => P8 | P7 => P11 | P8 => P13 | P9 => P14 | P10 => P12 | P11 => P3 | P12 => P5 | P13 => P6 | P14 => P4 end.
Definition fl74_77 (l:Line) := match l with L0 => L0 | L1 => L10 | L2 => L8 | L3 => L11 | L4 => L9 | L5 => L12 | L6 => L7 | L7 => L18 | L8 => L16 | L9 => L17 | L10 => L14 | L11 => L15 | L12 => L13 | L13 => L5 | L14 => L1 | L15 => L3 | L16 => L2 | L17 => L4 | L18 => L6 | L19 => L26 | L20 => L28 | L21 => L31 | L22 => L22 | L23 => L23 | L24 => L21 | L25 => L33 | L26 => L29 | L27 => L25 | L28 => L34 | L29 => L19 | L30 => L30 | L31 => L24 | L32 => L32 | L33 => L27 | L34 => L20 end.

(* P77 : S2 S12 S23 S26 S39 S40 S51 -> 
   P78 : S2 S14 S16 S25 S35 S47 S52  *)
Definition fp77_78 (p:Point) := match p with P0 => P12 | P1 => P8 | P2 => P3 | P3 => P6 | P4 => P9 | P5 => P13 | P6 => P2 | P7 => P5 | P8 => P10 | P9 => P14 | P10 => P1 | P11 => P0 | P12 => P11 | P13 => P7 | P14 => P4 end.
Definition fl77_78 (l:Line) := match l with L0 => L20 | L1 => L33 | L2 => L16 | L3 => L30 | L4 => L9 | L5 => L5 | L6 => L26 | L7 => L18 | L8 => L8 | L9 => L24 | L10 => L27 | L11 => L3 | L12 => L32 | L13 => L12 | L14 => L1 | L15 => L15 | L16 => L22 | L17 => L21 | L18 => L19 | L19 => L7 | L20 => L34 | L21 => L31 | L22 => L2 | L23 => L23 | L24 => L4 | L25 => L10 | L26 => L29 | L27 => L25 | L28 => L28 | L29 => L6 | L30 => L11 | L31 => L17 | L32 => L13 | L33 => L14 | L34 => L0 end.

(* P78 : S2 S14 S16 S25 S35 S47 S52 -> 
   P80 : S2 S14 S19 S24 S39 S45 S50  *)
Definition fp78_80 (p:Point) := match p with P0 => P6 | P1 => P10 | P2 => P11 | P3 => P9 | P4 => P12 | P5 => P0 | P6 => P5 | P7 => P1 | P8 => P4 | P9 => P8 | P10 => P13 | P11 => P7 | P12 => P14 | P13 => P2 | P14 => P3 end.
Definition fl78_80 (l:Line) := match l with L0 => L34 | L1 => L33 | L2 => L2 | L3 => L7 | L4 => L32 | L5 => L31 | L6 => L15 | L7 => L30 | L8 => L25 | L9 => L19 | L10 => L8 | L11 => L13 | L12 => L4 | L13 => L11 | L14 => L22 | L15 => L29 | L16 => L14 | L17 => L5 | L18 => L24 | L19 => L21 | L20 => L23 | L21 => L18 | L22 => L10 | L23 => L20 | L24 => L26 | L25 => L16 | L26 => L9 | L27 => L1 | L28 => L0 | L29 => L3 | L30 => L6 | L31 => L12 | L32 => L17 | L33 => L27 | L34 => L28 end.

(* P80 : S2 S14 S19 S24 S39 S45 S50 -> 
   P83 : S2 S14 S21 S26 S38 S43 S49  *)
Definition fp80_83 (p:Point) := match p with P0 => P6 | P1 => P11 | P2 => P10 | P3 => P12 | P4 => P9 | P5 => P0 | P6 => P5 | P7 => P2 | P8 => P3 | P9 => P14 | P10 => P7 | P11 => P13 | P12 => P8 | P13 => P1 | P14 => P4 end.
Definition fl80_83 (l:Line) := match l with L0 => L34 | L1 => L33 | L2 => L2 | L3 => L15 | L4 => L31 | L5 => L32 | L6 => L7 | L7 => L29 | L8 => L22 | L9 => L24 | L10 => L14 | L11 => L11 | L12 => L5 | L13 => L13 | L14 => L25 | L15 => L30 | L16 => L8 | L17 => L4 | L18 => L19 | L19 => L26 | L20 => L20 | L21 => L9 | L22 => L16 | L23 => L23 | L24 => L21 | L25 => L10 | L26 => L18 | L27 => L1 | L28 => L0 | L29 => L6 | L30 => L3 | L31 => L17 | L32 => L12 | L33 => L27 | L34 => L28 end.

(* P83 : S2 S14 S21 S26 S38 S43 S49 -> 
   P85 : S2 S15 S16 S26 S33 S45 S54  *)
Definition fp83_85 (p:Point) := match p with P0 => P1 | P1 => P0 | P2 => P2 | P3 => P11 | P4 => P13 | P5 => P12 | P6 => P14 | P7 => P8 | P8 => P10 | P9 => P7 | P10 => P9 | P11 => P4 | P12 => P6 | P13 => P3 | P14 => P5 end.
Definition fl83_85 (l:Line) := match l with L0 => L0 | L1 => L11 | L2 => L9 | L3 => L8 | L4 => L10 | L5 => L7 | L6 => L12 | L7 => L6 | L8 => L4 | L9 => L2 | L10 => L3 | L11 => L1 | L12 => L5 | L13 => L18 | L14 => L17 | L15 => L14 | L16 => L15 | L17 => L16 | L18 => L13 | L19 => L29 | L20 => L34 | L21 => L22 | L22 => L24 | L23 => L28 | L24 => L25 | L25 => L21 | L26 => L32 | L27 => L30 | L28 => L20 | L29 => L26 | L30 => L33 | L31 => L27 | L32 => L19 | L33 => L31 | L34 => L23 end.

(* P85 : S2 S15 S16 S26 S33 S45 S54 -> 
   P86 : S2 S15 S18 S25 S38 S44 S51  *)
Definition fp85_86 (p:Point) := match p with P0 => P9 | P1 => P14 | P2 => P4 | P3 => P8 | P4 => P2 | P5 => P5 | P6 => P11 | P7 => P13 | P8 => P3 | P9 => P0 | P10 => P10 | P11 => P6 | P12 => P12 | P13 => P7 | P14 => P1 end.
Definition fl85_86 (l:Line) := match l with L0 => L23 | L1 => L18 | L2 => L29 | L3 => L21 | L4 => L4 | L5 => L33 | L6 => L10 | L7 => L14 | L8 => L19 | L9 => L9 | L10 => L6 | L11 => L31 | L12 => L27 | L13 => L25 | L14 => L7 | L15 => L24 | L16 => L26 | L17 => L17 | L18 => L1 | L19 => L8 | L20 => L20 | L21 => L3 | L22 => L32 | L23 => L0 | L24 => L15 | L25 => L13 | L26 => L16 | L27 => L12 | L28 => L28 | L29 => L2 | L30 => L30 | L31 => L11 | L32 => L22 | L33 => L5 | L34 => L34 end.

(* P86 : S2 S15 S18 S25 S38 S44 S51 -> 
   P89 : S2 S15 S21 S30 S35 S40 S50  *)
Definition fp86_89 (p:Point) := match p with P0 => P8 | P1 => P12 | P2 => P3 | P3 => P9 | P4 => P2 | P5 => P6 | P6 => P13 | P7 => P11 | P8 => P4 | P9 => P0 | P10 => P7 | P11 => P5 | P12 => P14 | P13 => P10 | P14 => P1 end.
Definition fl86_89 (l:Line) := match l with L0 => L20 | L1 => L18 | L2 => L32 | L3 => L24 | L4 => L3 | L5 => L27 | L6 => L8 | L7 => L16 | L8 => L26 | L9 => L9 | L10 => L5 | L11 => L30 | L12 => L33 | L13 => L22 | L14 => L12 | L15 => L21 | L16 => L19 | L17 => L15 | L18 => L1 | L19 => L10 | L20 => L23 | L21 => L4 | L22 => L29 | L23 => L0 | L24 => L17 | L25 => L13 | L26 => L14 | L27 => L7 | L28 => L34 | L29 => L2 | L30 => L31 | L31 => L11 | L32 => L25 | L33 => L6 | L34 => L28 end.

(* P89 : S2 S15 S21 S30 S35 S40 S50 -> 
   P90 : S3 S8 S18 S28 S33 S45 S55  *)
Definition fp89_90 (p:Point) := match p with P0 => P0 | P1 => P2 | P2 => P1 | P3 => P3 | P4 => P4 | P5 => P6 | P6 => P5 | P7 => P7 | P8 => P8 | P9 => P10 | P10 => P9 | P11 => P11 | P12 => P12 | P13 => P14 | P14 => P13 end.
Definition fl89_90 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L3 | L4 => L4 | L5 => L5 | L6 => L6 | L7 => L17 | L8 => L18 | L9 => L16 | L10 => L13 | L11 => L14 | L12 => L15 | L13 => L10 | L14 => L11 | L15 => L12 | L16 => L9 | L17 => L7 | L18 => L8 | L19 => L21 | L20 => L20 | L21 => L19 | L22 => L22 | L23 => L25 | L24 => L24 | L25 => L23 | L26 => L26 | L27 => L32 | L28 => L31 | L29 => L34 | L30 => L33 | L31 => L28 | L32 => L27 | L33 => L30 | L34 => L29 end.

(* P90 : S3 S8 S18 S28 S33 S45 S55 -> 
   P92 : S3 S8 S21 S27 S36 S46 S49  *)
Definition fp90_92 (p:Point) := match p with P0 => P10 | P1 => P4 | P2 => P13 | P3 => P1 | P4 => P8 | P5 => P6 | P6 => P11 | P7 => P9 | P8 => P0 | P9 => P14 | P10 => P3 | P11 => P7 | P12 => P2 | P13 => P12 | P14 => P5 end.
Definition fl90_92 (l:Line) := match l with L0 => L25 | L1 => L8 | L2 => L34 | L3 => L4 | L4 => L19 | L5 => L13 | L6 => L30 | L7 => L24 | L8 => L1 | L9 => L17 | L10 => L23 | L11 => L26 | L12 => L7 | L13 => L21 | L14 => L28 | L15 => L11 | L16 => L16 | L17 => L32 | L18 => L6 | L19 => L12 | L20 => L0 | L21 => L9 | L22 => L10 | L23 => L27 | L24 => L3 | L25 => L20 | L26 => L18 | L27 => L2 | L28 => L33 | L29 => L31 | L30 => L15 | L31 => L29 | L32 => L5 | L33 => L14 | L34 => L22 end.

(* P92 : S3 S8 S21 S27 S36 S46 S49 -> 
   P95 : S3 S8 S23 S31 S35 S40 S52  *)
Definition fp92_95 (p:Point) := match p with P0 => P10 | P1 => P4 | P2 => P13 | P3 => P8 | P4 => P1 | P5 => P11 | P6 => P6 | P7 => P14 | P8 => P3 | P9 => P9 | P10 => P0 | P11 => P5 | P12 => P12 | P13 => P2 | P14 => P7 end.
Definition fl92_95 (l:Line) := match l with L0 => L25 | L1 => L8 | L2 => L34 | L3 => L19 | L4 => L4 | L5 => L30 | L6 => L13 | L7 => L7 | L8 => L1 | L9 => L26 | L10 => L23 | L11 => L17 | L12 => L24 | L13 => L6 | L14 => L28 | L15 => L32 | L16 => L16 | L17 => L11 | L18 => L21 | L19 => L3 | L20 => L20 | L21 => L18 | L22 => L27 | L23 => L10 | L24 => L12 | L25 => L0 | L26 => L9 | L27 => L22 | L28 => L14 | L29 => L29 | L30 => L5 | L31 => L31 | L32 => L15 | L33 => L33 | L34 => L2 end.

(* P95 : S3 S8 S23 S31 S35 S40 S52 -> 
   P97 : S3 S11 S16 S29 S33 S46 S52  *)
Definition fp95_97 (p:Point) := match p with P0 => P10 | P1 => P13 | P2 => P4 | P3 => P6 | P4 => P11 | P5 => P8 | P6 => P1 | P7 => P2 | P8 => P7 | P9 => P12 | P10 => P5 | P11 => P3 | P12 => P14 | P13 => P9 | P14 => P0 end.
Definition fl95_97 (l:Line) := match l with L0 => L25 | L1 => L34 | L2 => L8 | L3 => L13 | L4 => L30 | L5 => L19 | L6 => L4 | L7 => L11 | L8 => L28 | L9 => L6 | L10 => L16 | L11 => L21 | L12 => L32 | L13 => L17 | L14 => L1 | L15 => L7 | L16 => L23 | L17 => L24 | L18 => L26 | L19 => L2 | L20 => L31 | L21 => L33 | L22 => L15 | L23 => L5 | L24 => L22 | L25 => L29 | L26 => L14 | L27 => L3 | L28 => L18 | L29 => L20 | L30 => L27 | L31 => L0 | L32 => L10 | L33 => L9 | L34 => L12 end.

(* P97 : S3 S11 S16 S29 S33 S46 S52 -> 
   P98 : S3 S11 S17 S24 S36 S45 S54  *)
Definition fp97_98 (p:Point) := match p with P0 => P12 | P1 => P8 | P2 => P3 | P3 => P1 | P4 => P14 | P5 => P10 | P6 => P5 | P7 => P11 | P8 => P0 | P9 => P4 | P10 => P7 | P11 => P13 | P12 => P2 | P13 => P6 | P14 => P9 end.
Definition fl97_98 (l:Line) := match l with L0 => L20 | L1 => L9 | L2 => L30 | L3 => L5 | L4 => L26 | L5 => L16 | L6 => L33 | L7 => L27 | L8 => L3 | L9 => L18 | L10 => L24 | L11 => L32 | L12 => L8 | L13 => L22 | L14 => L21 | L15 => L12 | L16 => L15 | L17 => L19 | L18 => L1 | L19 => L10 | L20 => L0 | L21 => L7 | L22 => L11 | L23 => L23 | L24 => L6 | L25 => L31 | L26 => L14 | L27 => L4 | L28 => L34 | L29 => L25 | L30 => L13 | L31 => L29 | L32 => L2 | L33 => L17 | L34 => L28 end.

(* P98 : S3 S11 S17 S24 S36 S45 S54 -> 
   P101 : S3 S11 S21 S28 S38 S40 S51  *)
Definition fp98_101 (p:Point) := match p with P0 => P12 | P1 => P3 | P2 => P8 | P3 => P1 | P4 => P14 | P5 => P5 | P6 => P10 | P7 => P13 | P8 => P2 | P9 => P9 | P10 => P6 | P11 => P11 | P12 => P0 | P13 => P7 | P14 => P4 end.
Definition fl98_101 (l:Line) := match l with L0 => L20 | L1 => L9 | L2 => L30 | L3 => L16 | L4 => L33 | L5 => L5 | L6 => L26 | L7 => L19 | L8 => L15 | L9 => L1 | L10 => L21 | L11 => L22 | L12 => L12 | L13 => L32 | L14 => L24 | L15 => L8 | L16 => L3 | L17 => L27 | L18 => L18 | L19 => L7 | L20 => L0 | L21 => L10 | L22 => L11 | L23 => L23 | L24 => L14 | L25 => L31 | L26 => L6 | L27 => L17 | L28 => L28 | L29 => L29 | L30 => L2 | L31 => L25 | L32 => L13 | L33 => L4 | L34 => L34 end.

(* P101 : S3 S11 S21 S28 S38 S40 S51 -> 
   P103 : S3 S12 S17 S29 S34 S40 S55  *)
Definition fp101_103 (p:Point) := match p with P0 => P13 | P1 => P4 | P2 => P10 | P3 => P8 | P4 => P6 | P5 => P11 | P6 => P1 | P7 => P2 | P8 => P12 | P9 => P5 | P10 => P7 | P11 => P9 | P12 => P3 | P13 => P14 | P14 => P0 end.
Definition fl101_103 (l:Line) := match l with L0 => L25 | L1 => L32 | L2 => L11 | L3 => L16 | L4 => L28 | L5 => L21 | L6 => L6 | L7 => L7 | L8 => L26 | L9 => L1 | L10 => L17 | L11 => L23 | L12 => L24 | L13 => L13 | L14 => L4 | L15 => L8 | L16 => L19 | L17 => L34 | L18 => L30 | L19 => L3 | L20 => L20 | L21 => L27 | L22 => L18 | L23 => L2 | L24 => L33 | L25 => L31 | L26 => L15 | L27 => L5 | L28 => L14 | L29 => L29 | L30 => L22 | L31 => L0 | L32 => L9 | L33 => L12 | L34 => L10 end.

(* P103 : S3 S12 S17 S29 S34 S40 S55 -> 
   P105 : S3 S12 S18 S31 S36 S41 S51  *)
Definition fp103_105 (p:Point) := match p with P0 => P5 | P1 => P9 | P2 => P11 | P3 => P12 | P4 => P10 | P5 => P6 | P6 => P0 | P7 => P1 | P8 => P3 | P9 => P7 | P10 => P13 | P11 => P14 | P12 => P8 | P13 => P4 | P14 => P2 end.
Definition fl103_105 (l:Line) := match l with L0 => L29 | L1 => L30 | L2 => L2 | L3 => L12 | L4 => L28 | L5 => L27 | L6 => L17 | L7 => L4 | L8 => L21 | L9 => L18 | L10 => L10 | L11 => L23 | L12 => L33 | L13 => L11 | L14 => L14 | L15 => L5 | L16 => L24 | L17 => L34 | L18 => L22 | L19 => L16 | L20 => L20 | L21 => L26 | L22 => L9 | L23 => L13 | L24 => L19 | L25 => L25 | L26 => L8 | L27 => L15 | L28 => L7 | L29 => L31 | L30 => L32 | L31 => L0 | L32 => L1 | L33 => L3 | L34 => L6 end.

(* P105 : S3 S12 S18 S31 S36 S41 S51 -> 
   P106 : S3 S12 S23 S27 S33 S42 S54  *)
Definition fp105_106 (p:Point) := match p with P0 => P5 | P1 => P11 | P2 => P9 | P3 => P10 | P4 => P12 | P5 => P6 | P6 => P0 | P7 => P2 | P8 => P4 | P9 => P14 | P10 => P8 | P11 => P7 | P12 => P13 | P13 => P3 | P14 => P1 end.
Definition fl105_106 (l:Line) := match l with L0 => L29 | L1 => L30 | L2 => L2 | L3 => L17 | L4 => L27 | L5 => L28 | L6 => L12 | L7 => L5 | L8 => L24 | L9 => L11 | L10 => L14 | L11 => L22 | L12 => L34 | L13 => L18 | L14 => L10 | L15 => L4 | L16 => L21 | L17 => L33 | L18 => L23 | L19 => L8 | L20 => L25 | L21 => L19 | L22 => L13 | L23 => L9 | L24 => L26 | L25 => L20 | L26 => L16 | L27 => L7 | L28 => L15 | L29 => L31 | L30 => L32 | L31 => L0 | L32 => L1 | L33 => L6 | L34 => L3 end.

(* P106 : S3 S12 S23 S27 S33 S42 S54 -> 
   P108 : S3 S13 S16 S28 S35 S41 S54  *)
Definition fp106_108 (p:Point) := match p with P0 => P8 | P1 => P3 | P2 => P12 | P3 => P14 | P4 => P5 | P5 => P10 | P6 => P1 | P7 => P0 | P8 => P7 | P9 => P4 | P10 => P11 | P11 => P13 | P12 => P6 | P13 => P9 | P14 => P2 end.
Definition fl106_108 (l:Line) := match l with L0 => L20 | L1 => L27 | L2 => L8 | L3 => L3 | L4 => L24 | L5 => L32 | L6 => L18 | L7 => L12 | L8 => L22 | L9 => L15 | L10 => L1 | L11 => L21 | L12 => L19 | L13 => L5 | L14 => L16 | L15 => L9 | L16 => L33 | L17 => L30 | L18 => L26 | L19 => L14 | L20 => L31 | L21 => L23 | L22 => L6 | L23 => L17 | L24 => L28 | L25 => L29 | L26 => L2 | L27 => L13 | L28 => L4 | L29 => L25 | L30 => L34 | L31 => L0 | L32 => L10 | L33 => L7 | L34 => L11 end.

(* P108 : S3 S13 S16 S28 S35 S41 S54 -> 
   P111 : S3 S13 S18 S29 S38 S42 S49  *)
Definition fp108_111 (p:Point) := match p with P0 => P4 | P1 => P10 | P2 => P13 | P3 => P3 | P4 => P0 | P5 => P14 | P6 => P9 | P7 => P11 | P8 => P8 | P9 => P6 | P10 => P1 | P11 => P7 | P12 => P12 | P13 => P2 | P14 => P5 end.
Definition fl108_111 (l:Line) := match l with L0 => L25 | L1 => L1 | L2 => L23 | L3 => L24 | L4 => L7 | L5 => L26 | L6 => L17 | L7 => L4 | L8 => L8 | L9 => L30 | L10 => L34 | L11 => L13 | L12 => L19 | L13 => L11 | L14 => L28 | L15 => L21 | L16 => L16 | L17 => L6 | L18 => L32 | L19 => L12 | L20 => L20 | L21 => L15 | L22 => L22 | L23 => L2 | L24 => L3 | L25 => L0 | L26 => L5 | L27 => L27 | L28 => L14 | L29 => L31 | L30 => L9 | L31 => L29 | L32 => L18 | L33 => L33 | L34 => L10 end.

(* P111 : S3 S13 S18 S29 S38 S42 S49 -> 
   P112 : S3 S13 S23 S24 S34 S46 S51  *)
Definition fp111_112 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P4 | P4 => P3 | P5 => P6 | P6 => P5 | P7 => P9 | P8 => P10 | P9 => P7 | P10 => P8 | P11 => P14 | P12 => P13 | P13 => P12 | P14 => P11 end.
Definition fl111_112 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L4 | L4 => L3 | L5 => L6 | L6 => L5 | L7 => L12 | L8 => L8 | L9 => L11 | L10 => L10 | L11 => L9 | L12 => L7 | L13 => L18 | L14 => L14 | L15 => L17 | L16 => L16 | L17 => L15 | L18 => L13 | L19 => L24 | L20 => L25 | L21 => L26 | L22 => L23 | L23 => L22 | L24 => L19 | L25 => L20 | L26 => L21 | L27 => L34 | L28 => L33 | L29 => L31 | L30 => L32 | L31 => L29 | L32 => L30 | L33 => L28 | L34 => L27 end.

(* P112 : S3 S13 S23 S24 S34 S46 S51 -> 
   P114 : S3 S14 S16 S31 S34 S45 S49  *)
Definition fp112_114 (p:Point) := match p with P0 => P8 | P1 => P3 | P2 => P12 | P3 => P14 | P4 => P5 | P5 => P10 | P6 => P1 | P7 => P0 | P8 => P7 | P9 => P4 | P10 => P11 | P11 => P13 | P12 => P6 | P13 => P9 | P14 => P2 end.
Definition fl112_114 (l:Line) := match l with L0 => L20 | L1 => L27 | L2 => L8 | L3 => L3 | L4 => L24 | L5 => L32 | L6 => L18 | L7 => L12 | L8 => L22 | L9 => L15 | L10 => L1 | L11 => L21 | L12 => L19 | L13 => L5 | L14 => L16 | L15 => L9 | L16 => L33 | L17 => L30 | L18 => L26 | L19 => L14 | L20 => L31 | L21 => L23 | L22 => L6 | L23 => L17 | L24 => L28 | L25 => L29 | L26 => L2 | L27 => L13 | L28 => L4 | L29 => L25 | L30 => L34 | L31 => L0 | L32 => L10 | L33 => L7 | L34 => L11 end.

(* P114 : S3 S14 S16 S31 S34 S45 S49 -> 
   P117 : S3 S14 S17 S27 S38 S41 S52  *)
Definition fp114_117 (p:Point) := match p with P0 => P1 | P1 => P2 | P2 => P0 | P3 => P11 | P4 => P13 | P5 => P14 | P6 => P12 | P7 => P3 | P8 => P5 | P9 => P6 | P10 => P4 | P11 => P7 | P12 => P9 | P13 => P10 | P14 => P8 end.
Definition fl114_117 (l:Line) := match l with L0 => L0 | L1 => L11 | L2 => L9 | L3 => L12 | L4 => L7 | L5 => L10 | L6 => L8 | L7 => L16 | L8 => L17 | L9 => L18 | L10 => L15 | L11 => L13 | L12 => L14 | L13 => L1 | L14 => L3 | L15 => L5 | L16 => L4 | L17 => L6 | L18 => L2 | L19 => L24 | L20 => L29 | L21 => L34 | L22 => L22 | L23 => L32 | L24 => L28 | L25 => L25 | L26 => L21 | L27 => L27 | L28 => L19 | L29 => L31 | L30 => L23 | L31 => L20 | L32 => L30 | L33 => L33 | L34 => L26 end.

(* P117 : S3 S14 S17 S27 S38 S41 S52 -> 
   P118 : S3 S14 S21 S24 S35 S42 S55  *)
Definition fp117_118 (p:Point) := match p with P0 => P1 | P1 => P0 | P2 => P2 | P3 => P11 | P4 => P13 | P5 => P12 | P6 => P14 | P7 => P7 | P8 => P9 | P9 => P8 | P10 => P10 | P11 => P3 | P12 => P5 | P13 => P4 | P14 => P6 end.
Definition fl117_118 (l:Line) := match l with L0 => L0 | L1 => L11 | L2 => L9 | L3 => L10 | L4 => L8 | L5 => L12 | L6 => L7 | L7 => L6 | L8 => L4 | L9 => L2 | L10 => L3 | L11 => L1 | L12 => L5 | L13 => L13 | L14 => L15 | L15 => L14 | L16 => L17 | L17 => L16 | L18 => L18 | L19 => L34 | L20 => L29 | L21 => L24 | L22 => L22 | L23 => L32 | L24 => L21 | L25 => L25 | L26 => L28 | L27 => L33 | L28 => L26 | L29 => L20 | L30 => L30 | L31 => L31 | L32 => L23 | L33 => L27 | L34 => L19 end.

(* P118 : S3 S14 S21 S24 S35 S42 S55 -> 
   P121 : S4 S8 S19 S31 S36 S45 S48  *)
Definition fp118_121 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P14 | P8 => P13 | P9 => P12 | P10 => P11 | P11 => P10 | P12 => P9 | P13 => P8 | P14 => P7 end.
Definition fl118_121 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L6 | L4 => L5 | L5 => L4 | L6 => L3 | L7 => L7 | L8 => L11 | L9 => L10 | L10 => L9 | L11 => L8 | L12 => L12 | L13 => L14 | L14 => L13 | L15 => L15 | L16 => L18 | L17 => L17 | L18 => L16 | L19 => L22 | L20 => L21 | L21 => L20 | L22 => L19 | L23 => L26 | L24 => L25 | L25 => L24 | L26 => L23 | L27 => L28 | L28 => L27 | L29 => L30 | L30 => L29 | L31 => L31 | L32 => L32 | L33 => L33 | L34 => L34 end.

(* P121 : S4 S8 S19 S31 S36 S45 S48 -> 
   P122 : S4 S8 S22 S25 S35 S44 S55  *)
Definition fp121_122 (p:Point) := match p with P0 => P0 | P1 => P2 | P2 => P1 | P3 => P3 | P4 => P4 | P5 => P6 | P6 => P5 | P7 => P12 | P8 => P11 | P9 => P13 | P10 => P14 | P11 => P8 | P12 => P7 | P13 => P9 | P14 => P10 end.
Definition fl121_122 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L5 | L4 => L6 | L5 => L3 | L6 => L4 | L7 => L17 | L8 => L14 | L9 => L13 | L10 => L16 | L11 => L18 | L12 => L15 | L13 => L9 | L14 => L8 | L15 => L12 | L16 => L10 | L17 => L7 | L18 => L11 | L19 => L19 | L20 => L22 | L21 => L21 | L22 => L20 | L23 => L25 | L24 => L24 | L25 => L23 | L26 => L26 | L27 => L34 | L28 => L33 | L29 => L32 | L30 => L31 | L31 => L30 | L32 => L29 | L33 => L28 | L34 => L27 end.

(* P122 : S4 S8 S22 S25 S35 S44 S55 -> 
   P124 : S4 S8 S23 S26 S33 S46 S53  *)
Definition fp122_124 (p:Point) := match p with P0 => P11 | P1 => P8 | P2 => P4 | P3 => P14 | P4 => P2 | P5 => P5 | P6 => P9 | P7 => P13 | P8 => P1 | P9 => P6 | P10 => P10 | P11 => P0 | P12 => P12 | P13 => P7 | P14 => P3 end.
Definition fl122_124 (l:Line) := match l with L0 => L24 | L1 => L14 | L2 => L29 | L3 => L11 | L4 => L34 | L5 => L5 | L6 => L22 | L7 => L18 | L8 => L8 | L9 => L20 | L10 => L32 | L11 => L3 | L12 => L27 | L13 => L25 | L14 => L1 | L15 => L23 | L16 => L26 | L17 => L17 | L18 => L7 | L19 => L19 | L20 => L9 | L21 => L31 | L22 => L6 | L23 => L15 | L24 => L0 | L25 => L13 | L26 => L16 | L27 => L12 | L28 => L28 | L29 => L2 | L30 => L30 | L31 => L21 | L32 => L10 | L33 => L33 | L34 => L4 end.

(* P124 : S4 S8 S23 S26 S33 S46 S53 -> 
   P127 : S4 S10 S17 S30 S36 S41 S53  *)
Definition fp124_127 (p:Point) := match p with P0 => P13 | P1 => P3 | P2 => P9 | P3 => P6 | P4 => P8 | P5 => P2 | P6 => P12 | P7 => P10 | P8 => P4 | P9 => P14 | P10 => P0 | P11 => P11 | P12 => P1 | P13 => P7 | P14 => P5 end.
Definition fl124_127 (l:Line) := match l with L0 => L21 | L1 => L32 | L2 => L16 | L3 => L25 | L4 => L6 | L5 => L11 | L6 => L28 | L7 => L20 | L8 => L1 | L9 => L12 | L10 => L19 | L11 => L22 | L12 => L15 | L13 => L4 | L14 => L29 | L15 => L33 | L16 => L10 | L17 => L18 | L18 => L23 | L19 => L2 | L20 => L7 | L21 => L31 | L22 => L34 | L23 => L27 | L24 => L24 | L25 => L3 | L26 => L8 | L27 => L17 | L28 => L13 | L29 => L14 | L30 => L0 | L31 => L30 | L32 => L26 | L33 => L9 | L34 => L5 end.

(* P127 : S4 S10 S17 S30 S36 S41 S53 -> 
   P128 : S4 S10 S20 S29 S33 S42 S55  *)
Definition fp127_128 (p:Point) := match p with P0 => P6 | P1 => P7 | P2 => P14 | P3 => P8 | P4 => P13 | P5 => P0 | P6 => P5 | P7 => P12 | P8 => P9 | P9 => P4 | P10 => P1 | P11 => P3 | P12 => P2 | P13 => P11 | P14 => P10 end.
Definition fl127_128 (l:Line) := match l with L0 => L31 | L1 => L32 | L2 => L2 | L3 => L33 | L4 => L7 | L5 => L15 | L6 => L34 | L7 => L28 | L8 => L10 | L9 => L13 | L10 => L26 | L11 => L22 | L12 => L3 | L13 => L9 | L14 => L19 | L15 => L27 | L16 => L14 | L17 => L6 | L18 => L23 | L19 => L8 | L20 => L18 | L21 => L24 | L22 => L20 | L23 => L25 | L24 => L21 | L25 => L11 | L26 => L16 | L27 => L4 | L28 => L5 | L29 => L1 | L30 => L0 | L31 => L30 | L32 => L29 | L33 => L17 | L34 => L12 end.

(* P128 : S4 S10 S20 S29 S33 S42 S55 -> 
   P131 : S4 S10 S23 S31 S32 S44 S51  *)
Definition fp128_131 (p:Point) := match p with P0 => P6 | P1 => P14 | P2 => P7 | P3 => P13 | P4 => P8 | P5 => P0 | P6 => P5 | P7 => P10 | P8 => P11 | P9 => P3 | P10 => P2 | P11 => P4 | P12 => P1 | P13 => P9 | P14 => P12 end.
Definition fl128_131 (l:Line) := match l with L0 => L31 | L1 => L32 | L2 => L2 | L3 => L34 | L4 => L15 | L5 => L7 | L6 => L33 | L7 => L27 | L8 => L14 | L9 => L9 | L10 => L19 | L11 => L23 | L12 => L6 | L13 => L13 | L14 => L26 | L15 => L28 | L16 => L10 | L17 => L3 | L18 => L22 | L19 => L16 | L20 => L11 | L21 => L21 | L22 => L25 | L23 => L20 | L24 => L24 | L25 => L18 | L26 => L8 | L27 => L5 | L28 => L4 | L29 => L1 | L30 => L0 | L31 => L30 | L32 => L29 | L33 => L12 | L34 => L17 end.

(* P131 : S4 S10 S23 S31 S32 S44 S51 -> 
   P132 : S4 S11 S17 S29 S38 S44 S48  *)
Definition fp131_132 (p:Point) := match p with P0 => P13 | P1 => P3 | P2 => P9 | P3 => P7 | P4 => P5 | P5 => P11 | P6 => P1 | P7 => P2 | P8 => P12 | P9 => P6 | P10 => P8 | P11 => P10 | P12 => P4 | P13 => P14 | P14 => P0 end.
Definition fl131_132 (l:Line) := match l with L0 => L21 | L1 => L28 | L2 => L11 | L3 => L16 | L4 => L32 | L5 => L25 | L6 => L6 | L7 => L12 | L8 => L20 | L9 => L1 | L10 => L15 | L11 => L19 | L12 => L22 | L13 => L18 | L14 => L4 | L15 => L10 | L16 => L23 | L17 => L29 | L18 => L33 | L19 => L3 | L20 => L26 | L21 => L31 | L22 => L13 | L23 => L2 | L24 => L30 | L25 => L27 | L26 => L17 | L27 => L5 | L28 => L14 | L29 => L34 | L30 => L24 | L31 => L0 | L32 => L9 | L33 => L7 | L34 => L8 end.

(* P132 : S4 S11 S17 S29 S38 S44 S48 -> 
   P134 : S4 S11 S20 S25 S36 S46 S51  *)
Definition fp132_134 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P4 | P4 => P3 | P5 => P6 | P6 => P5 | P7 => P10 | P8 => P9 | P9 => P8 | P10 => P7 | P11 => P13 | P12 => P14 | P13 => P11 | P14 => P12 end.
Definition fl132_134 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L4 | L4 => L3 | L5 => L6 | L6 => L5 | L7 => L12 | L8 => L10 | L9 => L9 | L10 => L8 | L11 => L11 | L12 => L7 | L13 => L13 | L14 => L16 | L15 => L17 | L16 => L14 | L17 => L15 | L18 => L18 | L19 => L26 | L20 => L23 | L21 => L24 | L22 => L25 | L23 => L20 | L24 => L21 | L25 => L22 | L26 => L19 | L27 => L33 | L28 => L34 | L29 => L32 | L30 => L31 | L31 => L30 | L32 => L29 | L33 => L27 | L34 => L28 end.

(* P134 : S4 S11 S20 S25 S36 S46 S51 -> 
   P137 : S4 S11 S22 S30 S33 S45 S50  *)
Definition fp134_137 (p:Point) := match p with P0 => P9 | P1 => P13 | P2 => P3 | P3 => P8 | P4 => P2 | P5 => P6 | P6 => P12 | P7 => P10 | P8 => P0 | P9 => P4 | P10 => P14 | P11 => P1 | P12 => P7 | P13 => P11 | P14 => P5 end.
Definition fl134_137 (l:Line) := match l with L0 => L21 | L1 => L18 | L2 => L33 | L3 => L4 | L4 => L23 | L5 => L10 | L6 => L29 | L7 => L16 | L8 => L6 | L9 => L28 | L10 => L25 | L11 => L11 | L12 => L32 | L13 => L19 | L14 => L12 | L15 => L20 | L16 => L22 | L17 => L15 | L18 => L1 | L19 => L27 | L20 => L3 | L21 => L24 | L22 => L8 | L23 => L17 | L24 => L0 | L25 => L14 | L26 => L13 | L27 => L2 | L28 => L34 | L29 => L7 | L30 => L31 | L31 => L30 | L32 => L5 | L33 => L26 | L34 => L9 end.

(* P137 : S4 S11 S22 S30 S33 S45 S50 -> 
   P138 : S4 S13 S19 S29 S32 S46 S50  *)
Definition fp137_138 (p:Point) := match p with P0 => P6 | P1 => P7 | P2 => P14 | P3 => P11 | P4 => P10 | P5 => P3 | P6 => P2 | P7 => P0 | P8 => P5 | P9 => P8 | P10 => P13 | P11 => P12 | P12 => P9 | P13 => P4 | P14 => P1 end.
Definition fl137_138 (l:Line) := match l with L0 => L31 | L1 => L34 | L2 => L15 | L3 => L2 | L4 => L32 | L5 => L33 | L6 => L7 | L7 => L13 | L8 => L28 | L9 => L10 | L10 => L3 | L11 => L26 | L12 => L22 | L13 => L6 | L14 => L9 | L15 => L14 | L16 => L23 | L17 => L19 | L18 => L27 | L19 => L11 | L20 => L29 | L21 => L24 | L22 => L5 | L23 => L8 | L24 => L30 | L25 => L25 | L26 => L4 | L27 => L12 | L28 => L1 | L29 => L20 | L30 => L21 | L31 => L0 | L32 => L17 | L33 => L18 | L34 => L16 end.

(* P138 : S4 S13 S19 S29 S32 S46 S50 -> 
   P140 : S4 S13 S22 S26 S38 S41 S51  *)
Definition fp138_140 (p:Point) := match p with P0 => P0 | P1 => P2 | P2 => P1 | P3 => P3 | P4 => P4 | P5 => P6 | P6 => P5 | P7 => P12 | P8 => P11 | P9 => P13 | P10 => P14 | P11 => P8 | P12 => P7 | P13 => P9 | P14 => P10 end.
Definition fl138_140 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L5 | L4 => L6 | L5 => L3 | L6 => L4 | L7 => L17 | L8 => L14 | L9 => L13 | L10 => L16 | L11 => L18 | L12 => L15 | L13 => L9 | L14 => L8 | L15 => L12 | L16 => L10 | L17 => L7 | L18 => L11 | L19 => L19 | L20 => L22 | L21 => L21 | L22 => L20 | L23 => L25 | L24 => L24 | L25 => L23 | L26 => L26 | L27 => L34 | L28 => L33 | L29 => L32 | L30 => L31 | L31 => L30 | L32 => L29 | L33 => L28 | L34 => L27 end.

(* P140 : S4 S13 S22 S26 S38 S41 S51 -> 
   P143 : S4 S13 S23 S30 S35 S42 S48  *)
Definition fp140_143 (p:Point) := match p with P0 => P2 | P1 => P1 | P2 => P0 | P3 => P13 | P4 => P12 | P5 => P11 | P6 => P14 | P7 => P7 | P8 => P10 | P9 => P9 | P10 => P8 | P11 => P5 | P12 => P4 | P13 => P3 | P14 => P6 end.
Definition fl140_143 (l:Line) := match l with L0 => L0 | L1 => L16 | L2 => L14 | L3 => L13 | L4 => L18 | L5 => L17 | L6 => L15 | L7 => L9 | L8 => L8 | L9 => L7 | L10 => L10 | L11 => L12 | L12 => L11 | L13 => L3 | L14 => L2 | L15 => L6 | L16 => L1 | L17 => L5 | L18 => L4 | L19 => L32 | L20 => L25 | L21 => L21 | L22 => L28 | L23 => L33 | L24 => L30 | L25 => L20 | L26 => L26 | L27 => L34 | L28 => L22 | L29 => L29 | L30 => L24 | L31 => L31 | L32 => L19 | L33 => L23 | L34 => L27 end.

(* P143 : S4 S13 S23 S30 S35 S42 S48 -> 
   P144 : S4 S14 S17 S26 S32 S45 S55  *)
Definition fp143_144 (p:Point) := match p with P0 => P14 | P1 => P6 | P2 => P7 | P3 => P5 | P4 => P8 | P5 => P0 | P6 => P13 | P7 => P9 | P8 => P4 | P9 => P12 | P10 => P1 | P11 => P11 | P12 => P2 | P13 => P10 | P14 => P3 end.
Definition fl143_144 (l:Line) := match l with L0 => L31 | L1 => L27 | L2 => L6 | L3 => L23 | L4 => L9 | L5 => L14 | L6 => L19 | L7 => L32 | L8 => L7 | L9 => L15 | L10 => L33 | L11 => L34 | L12 => L2 | L13 => L10 | L14 => L22 | L15 => L28 | L16 => L13 | L17 => L3 | L18 => L26 | L19 => L12 | L20 => L17 | L21 => L30 | L22 => L29 | L23 => L20 | L24 => L24 | L25 => L8 | L26 => L18 | L27 => L1 | L28 => L4 | L29 => L5 | L30 => L0 | L31 => L21 | L32 => L25 | L33 => L16 | L34 => L11 end.

(* P144 : S4 S14 S17 S26 S32 S45 S55 -> 
   P146 : S4 S14 S19 S25 S38 S42 S53  *)
Definition fp144_146 (p:Point) := match p with P0 => P3 | P1 => P13 | P2 => P9 | P3 => P4 | P4 => P0 | P5 => P10 | P6 => P14 | P7 => P6 | P8 => P2 | P9 => P8 | P10 => P12 | P11 => P1 | P12 => P5 | P13 => P11 | P14 => P7 end.
Definition fl144_146 (l:Line) := match l with L0 => L21 | L1 => L1 | L2 => L19 | L3 => L15 | L4 => L20 | L5 => L12 | L6 => L22 | L7 => L6 | L8 => L16 | L9 => L28 | L10 => L32 | L11 => L11 | L12 => L25 | L13 => L33 | L14 => L10 | L15 => L23 | L16 => L29 | L17 => L4 | L18 => L18 | L19 => L26 | L20 => L17 | L21 => L24 | L22 => L7 | L23 => L3 | L24 => L0 | L25 => L5 | L26 => L2 | L27 => L13 | L28 => L34 | L29 => L8 | L30 => L30 | L31 => L31 | L32 => L14 | L33 => L27 | L34 => L9 end.

(* P146 : S4 S14 S19 S25 S38 S42 S53 -> 
   P149 : S4 S14 S20 S31 S35 S41 S50  *)
Definition fp146_149 (p:Point) := match p with P0 => P3 | P1 => P13 | P2 => P9 | P3 => P0 | P4 => P4 | P5 => P14 | P6 => P10 | P7 => P12 | P8 => P8 | P9 => P2 | P10 => P6 | P11 => P11 | P12 => P7 | P13 => P1 | P14 => P5 end.
Definition fl146_149 (l:Line) := match l with L0 => L21 | L1 => L1 | L2 => L19 | L3 => L20 | L4 => L15 | L5 => L22 | L6 => L12 | L7 => L25 | L8 => L32 | L9 => L28 | L10 => L16 | L11 => L11 | L12 => L6 | L13 => L33 | L14 => L29 | L15 => L4 | L16 => L10 | L17 => L23 | L18 => L18 | L19 => L2 | L20 => L3 | L21 => L0 | L22 => L5 | L23 => L17 | L24 => L24 | L25 => L7 | L26 => L26 | L27 => L27 | L28 => L9 | L29 => L14 | L30 => L31 | L31 => L30 | L32 => L8 | L33 => L13 | L34 => L34 end.

(* P149 : S4 S14 S20 S31 S35 S41 S50 -> 
   P150 : S5 S8 S19 S25 S37 S46 S52  *)
Definition fp149_150 (p:Point) := match p with P0 => P2 | P1 => P1 | P2 => P0 | P3 => P11 | P4 => P14 | P5 => P13 | P6 => P12 | P7 => P4 | P8 => P5 | P9 => P6 | P10 => P3 | P11 => P8 | P12 => P9 | P13 => P10 | P14 => P7 end.
Definition fl149_150 (l:Line) := match l with L0 => L0 | L1 => L14 | L2 => L16 | L3 => L17 | L4 => L15 | L5 => L18 | L6 => L13 | L7 => L9 | L8 => L12 | L9 => L10 | L10 => L7 | L11 => L8 | L12 => L11 | L13 => L1 | L14 => L3 | L15 => L5 | L16 => L4 | L17 => L6 | L18 => L2 | L19 => L22 | L20 => L29 | L21 => L34 | L22 => L24 | L23 => L31 | L24 => L27 | L25 => L19 | L26 => L23 | L27 => L28 | L28 => L25 | L29 => L32 | L30 => L21 | L31 => L26 | L32 => L30 | L33 => L33 | L34 => L20 end.

(* P150 : S5 S8 S19 S25 S37 S46 S52 -> 
   P153 : S5 S8 S21 S28 S35 S47 S48  *)
Definition fp150_153 (p:Point) := match p with P0 => P5 | P1 => P8 | P2 => P14 | P3 => P13 | P4 => P7 | P5 => P6 | P6 => P0 | P7 => P12 | P8 => P10 | P9 => P3 | P10 => P1 | P11 => P2 | P12 => P4 | P13 => P9 | P14 => P11 end.
Definition fl150_153 (l:Line) := match l with L0 => L27 | L1 => L28 | L2 => L2 | L3 => L30 | L4 => L12 | L5 => L17 | L6 => L29 | L7 => L3 | L8 => L8 | L9 => L24 | L10 => L20 | L11 => L18 | L12 => L32 | L13 => L9 | L14 => L14 | L15 => L6 | L16 => L23 | L17 => L31 | L18 => L19 | L19 => L11 | L20 => L25 | L21 => L21 | L22 => L16 | L23 => L22 | L24 => L13 | L25 => L10 | L26 => L26 | L27 => L34 | L28 => L33 | L29 => L15 | L30 => L7 | L31 => L5 | L32 => L4 | L33 => L1 | L34 => L0 end.

(* P153 : S5 S8 S21 S28 S35 S47 S48 -> 
   P155 : S5 S8 S22 S26 S39 S45 S49  *)
Definition fp153_155 (p:Point) := match p with P0 => P5 | P1 => P14 | P2 => P8 | P3 => P7 | P4 => P13 | P5 => P6 | P6 => P0 | P7 => P9 | P8 => P11 | P9 => P4 | P10 => P2 | P11 => P1 | P12 => P3 | P13 => P12 | P14 => P10 end.
Definition fl153_155 (l:Line) := match l with L0 => L27 | L1 => L28 | L2 => L2 | L3 => L29 | L4 => L17 | L5 => L12 | L6 => L30 | L7 => L6 | L8 => L14 | L9 => L19 | L10 => L23 | L11 => L9 | L12 => L31 | L13 => L18 | L14 => L8 | L15 => L3 | L16 => L20 | L17 => L32 | L18 => L24 | L19 => L13 | L20 => L22 | L21 => L26 | L22 => L10 | L23 => L25 | L24 => L11 | L25 => L16 | L26 => L21 | L27 => L34 | L28 => L33 | L29 => L7 | L30 => L15 | L31 => L4 | L32 => L5 | L33 => L1 | L34 => L0 end.

(* P155 : S5 S8 S22 S26 S39 S45 S49 -> 
   P156 : S5 S9 S19 S28 S32 S45 S54  *)
Definition fp155_156 (p:Point) := match p with P0 => P7 | P1 => P4 | P2 => P12 | P3 => P14 | P4 => P6 | P5 => P9 | P6 => P1 | P7 => P11 | P8 => P3 | P9 => P8 | P10 => P0 | P11 => P2 | P12 => P10 | P13 => P5 | P14 => P13 end.
Definition fl155_156 (l:Line) := match l with L0 => L26 | L1 => L31 | L2 => L10 | L3 => L22 | L4 => L3 | L5 => L13 | L6 => L28 | L7 => L7 | L8 => L1 | L9 => L25 | L10 => L24 | L11 => L17 | L12 => L23 | L13 => L5 | L14 => L16 | L15 => L9 | L16 => L30 | L17 => L33 | L18 => L20 | L19 => L6 | L20 => L19 | L21 => L27 | L22 => L14 | L23 => L32 | L24 => L15 | L25 => L2 | L26 => L34 | L27 => L21 | L28 => L29 | L29 => L18 | L30 => L4 | L31 => L11 | L32 => L12 | L33 => L8 | L34 => L0 end.

(* P156 : S5 S9 S19 S28 S32 S45 S54 -> 
   P159 : S5 S9 S20 S29 S34 S46 S49  *)
Definition fp156_159 (p:Point) := match p with P0 => P3 | P1 => P9 | P2 => P13 | P3 => P0 | P4 => P4 | P5 => P10 | P6 => P14 | P7 => P7 | P8 => P11 | P9 => P1 | P10 => P5 | P11 => P8 | P12 => P12 | P13 => P2 | P14 => P6 end.
Definition fl156_159 (l:Line) := match l with L0 => L21 | L1 => L1 | L2 => L19 | L3 => L22 | L4 => L12 | L5 => L20 | L6 => L15 | L7 => L23 | L8 => L29 | L9 => L33 | L10 => L10 | L11 => L18 | L12 => L4 | L13 => L28 | L14 => L32 | L15 => L6 | L16 => L16 | L17 => L25 | L18 => L11 | L19 => L2 | L20 => L5 | L21 => L0 | L22 => L3 | L23 => L7 | L24 => L24 | L25 => L17 | L26 => L26 | L27 => L34 | L28 => L13 | L29 => L8 | L30 => L30 | L31 => L31 | L32 => L14 | L33 => L9 | L34 => L27 end.

(* P159 : S5 S9 S20 S29 S34 S46 S49 -> 
   P161 : S5 S9 S22 S30 S35 S41 S52  *)
Definition fp159_161 (p:Point) := match p with P0 => P4 | P1 => P7 | P2 => P12 | P3 => P0 | P4 => P3 | P5 => P8 | P6 => P11 | P7 => P9 | P8 => P14 | P9 => P1 | P10 => P6 | P11 => P10 | P12 => P13 | P13 => P2 | P14 => P5 end.
Definition fl159_161 (l:Line) := match l with L0 => L26 | L1 => L1 | L2 => L24 | L3 => L23 | L4 => L7 | L5 => L25 | L6 => L17 | L7 => L22 | L8 => L31 | L9 => L28 | L10 => L10 | L11 => L13 | L12 => L3 | L13 => L33 | L14 => L30 | L15 => L5 | L16 => L16 | L17 => L20 | L18 => L9 | L19 => L2 | L20 => L6 | L21 => L0 | L22 => L4 | L23 => L12 | L24 => L19 | L25 => L15 | L26 => L21 | L27 => L27 | L28 => L18 | L29 => L8 | L30 => L32 | L31 => L29 | L32 => L14 | L33 => L11 | L34 => L34 end.

(* P161 : S5 S9 S22 S30 S35 S41 S52 -> 
   P162 : S5 S10 S17 S29 S32 S47 S52  *)
Definition fp161_162 (p:Point) := match p with P0 => P13 | P1 => P3 | P2 => P9 | P3 => P6 | P4 => P8 | P5 => P2 | P6 => P12 | P7 => P14 | P8 => P0 | P9 => P10 | P10 => P4 | P11 => P7 | P12 => P5 | P13 => P11 | P14 => P1 end.
Definition fl161_162 (l:Line) := match l with L0 => L21 | L1 => L32 | L2 => L16 | L3 => L6 | L4 => L25 | L5 => L28 | L6 => L11 | L7 => L20 | L8 => L1 | L9 => L12 | L10 => L19 | L11 => L22 | L12 => L15 | L13 => L23 | L14 => L10 | L15 => L33 | L16 => L29 | L17 => L18 | L18 => L4 | L19 => L7 | L20 => L2 | L21 => L34 | L22 => L31 | L23 => L8 | L24 => L3 | L25 => L24 | L26 => L27 | L27 => L0 | L28 => L14 | L29 => L13 | L30 => L17 | L31 => L9 | L32 => L5 | L33 => L30 | L34 => L26 end.

(* P162 : S5 S10 S17 S29 S32 S47 S52 -> 
   P164 : S5 S10 S20 S28 S39 S41 S51  *)
Definition fp162_164 (p:Point) := match p with P0 => P0 | P1 => P2 | P2 => P1 | P3 => P3 | P4 => P4 | P5 => P6 | P6 => P5 | P7 => P12 | P8 => P11 | P9 => P13 | P10 => P14 | P11 => P8 | P12 => P7 | P13 => P9 | P14 => P10 end.
Definition fl162_164 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L5 | L4 => L6 | L5 => L3 | L6 => L4 | L7 => L17 | L8 => L14 | L9 => L13 | L10 => L16 | L11 => L18 | L12 => L15 | L13 => L9 | L14 => L8 | L15 => L12 | L16 => L10 | L17 => L7 | L18 => L11 | L19 => L19 | L20 => L22 | L21 => L21 | L22 => L20 | L23 => L25 | L24 => L24 | L25 => L23 | L26 => L26 | L27 => L34 | L28 => L33 | L29 => L32 | L30 => L31 | L31 => L30 | L32 => L29 | L33 => L28 | L34 => L27 end.

(* P164 : S5 S10 S20 S28 S39 S41 S51 -> 
   P167 : S5 S10 S21 S30 S37 S42 S49  *)
Definition fp164_167 (p:Point) := match p with P0 => P12 | P1 => P7 | P2 => P4 | P3 => P14 | P4 => P1 | P5 => P6 | P6 => P9 | P7 => P0 | P8 => P11 | P9 => P8 | P10 => P3 | P11 => P13 | P12 => P2 | P13 => P5 | P14 => P10 end.
Definition fl164_167 (l:Line) := match l with L0 => L26 | L1 => L9 | L2 => L33 | L3 => L5 | L4 => L20 | L5 => L16 | L6 => L30 | L7 => L10 | L8 => L22 | L9 => L13 | L10 => L3 | L11 => L28 | L12 => L31 | L13 => L1 | L14 => L25 | L15 => L23 | L16 => L17 | L17 => L7 | L18 => L24 | L19 => L19 | L20 => L14 | L21 => L27 | L22 => L6 | L23 => L8 | L24 => L11 | L25 => L12 | L26 => L0 | L27 => L34 | L28 => L2 | L29 => L32 | L30 => L15 | L31 => L4 | L32 => L29 | L33 => L18 | L34 => L21 end.

(* P167 : S5 S10 S21 S30 S37 S42 S49 -> 
   P168 : S5 S12 S17 S26 S37 S41 S54  *)
Definition fp167_168 (p:Point) := match p with P0 => P11 | P1 => P6 | P2 => P10 | P3 => P2 | P4 => P14 | P5 => P3 | P6 => P7 | P7 => P5 | P8 => P9 | P9 => P0 | P10 => P12 | P11 => P4 | P12 => P8 | P13 => P1 | P14 => P13 end.
Definition fl167_168 (l:Line) := match l with L0 => L34 | L1 => L14 | L2 => L22 | L3 => L29 | L4 => L5 | L5 => L24 | L6 => L11 | L7 => L31 | L8 => L33 | L9 => L32 | L10 => L2 | L11 => L7 | L12 => L15 | L13 => L30 | L14 => L25 | L15 => L13 | L16 => L8 | L17 => L19 | L18 => L4 | L19 => L16 | L20 => L18 | L21 => L0 | L22 => L17 | L23 => L6 | L24 => L23 | L25 => L9 | L26 => L27 | L27 => L21 | L28 => L12 | L29 => L1 | L30 => L20 | L31 => L28 | L32 => L10 | L33 => L3 | L34 => L26 end.

(* P168 : S5 S12 S17 S26 S37 S41 S54 -> 
   P171 : S5 S12 S19 S29 S39 S42 S48  *)
Definition fp168_171 (p:Point) := match p with P0 => P7 | P1 => P4 | P2 => P12 | P3 => P1 | P4 => P9 | P5 => P6 | P6 => P14 | P7 => P3 | P8 => P11 | P9 => P0 | P10 => P8 | P11 => P5 | P12 => P13 | P13 => P2 | P14 => P10 end.
Definition fl168_171 (l:Line) := match l with L0 => L26 | L1 => L10 | L2 => L31 | L3 => L22 | L4 => L3 | L5 => L28 | L6 => L13 | L7 => L23 | L8 => L24 | L9 => L25 | L10 => L1 | L11 => L17 | L12 => L7 | L13 => L20 | L14 => L30 | L15 => L9 | L16 => L16 | L17 => L33 | L18 => L5 | L19 => L8 | L20 => L11 | L21 => L0 | L22 => L12 | L23 => L4 | L24 => L29 | L25 => L18 | L26 => L21 | L27 => L34 | L28 => L15 | L29 => L2 | L30 => L32 | L31 => L19 | L32 => L14 | L33 => L6 | L34 => L27 end.

(* P171 : S5 S12 S19 S29 S39 S42 S48 -> 
   P172 : S5 S12 S22 S25 S34 S47 S51  *)
Definition fp171_172 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P4 | P4 => P3 | P5 => P6 | P6 => P5 | P7 => P9 | P8 => P10 | P9 => P7 | P10 => P8 | P11 => P14 | P12 => P13 | P13 => P12 | P14 => P11 end.
Definition fl171_172 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L4 | L4 => L3 | L5 => L6 | L6 => L5 | L7 => L12 | L8 => L8 | L9 => L11 | L10 => L10 | L11 => L9 | L12 => L7 | L13 => L18 | L14 => L14 | L15 => L17 | L16 => L16 | L17 => L15 | L18 => L13 | L19 => L24 | L20 => L25 | L21 => L26 | L22 => L23 | L23 => L22 | L24 => L19 | L25 => L20 | L26 => L21 | L27 => L34 | L28 => L33 | L29 => L31 | L30 => L32 | L31 => L29 | L32 => L30 | L33 => L28 | L34 => L27 end.

(* P172 : S5 S12 S22 S25 S34 S47 S51 -> 
   P175 : S5 S15 S17 S30 S34 S45 S48  *)
Definition fp172_175 (p:Point) := match p with P0 => P12 | P1 => P7 | P2 => P4 | P3 => P10 | P4 => P5 | P5 => P2 | P6 => P13 | P7 => P14 | P8 => P1 | P9 => P6 | P10 => P9 | P11 => P3 | P12 => P8 | P13 => P11 | P14 => P0 end.
Definition fl172_175 (l:Line) := match l with L0 => L26 | L1 => L30 | L2 => L16 | L3 => L9 | L4 => L33 | L5 => L20 | L6 => L5 | L7 => L28 | L8 => L10 | L9 => L3 | L10 => L31 | L11 => L22 | L12 => L13 | L13 => L23 | L14 => L1 | L15 => L25 | L16 => L24 | L17 => L17 | L18 => L7 | L19 => L4 | L20 => L8 | L21 => L34 | L22 => L19 | L23 => L2 | L24 => L12 | L25 => L29 | L26 => L27 | L27 => L0 | L28 => L14 | L29 => L15 | L30 => L18 | L31 => L6 | L32 => L11 | L33 => L32 | L34 => L21 end.

(* P175 : S5 S15 S17 S30 S34 S45 S48 -> 
   P177 : S5 S15 S20 S25 S35 S42 S54  *)
Definition fp175_177 (p:Point) := match p with P0 => P0 | P1 => P2 | P2 => P1 | P3 => P3 | P4 => P4 | P5 => P6 | P6 => P5 | P7 => P12 | P8 => P11 | P9 => P13 | P10 => P14 | P11 => P8 | P12 => P7 | P13 => P9 | P14 => P10 end.
Definition fl175_177 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L5 | L4 => L6 | L5 => L3 | L6 => L4 | L7 => L17 | L8 => L14 | L9 => L13 | L10 => L16 | L11 => L18 | L12 => L15 | L13 => L9 | L14 => L8 | L15 => L12 | L16 => L10 | L17 => L7 | L18 => L11 | L19 => L19 | L20 => L22 | L21 => L21 | L22 => L20 | L23 => L25 | L24 => L24 | L25 => L23 | L26 => L26 | L27 => L34 | L28 => L33 | L29 => L32 | L30 => L31 | L31 => L30 | L32 => L29 | L33 => L28 | L34 => L27 end.

(* P177 : S5 S15 S20 S25 S35 S42 S54 -> 
   P178 : S5 S15 S21 S26 S32 S46 S51  *)
Definition fp177_178 (p:Point) := match p with P0 => P1 | P1 => P2 | P2 => P0 | P3 => P13 | P4 => P11 | P5 => P12 | P6 => P14 | P7 => P6 | P8 => P4 | P9 => P3 | P10 => P5 | P11 => P8 | P12 => P10 | P13 => P9 | P14 => P7 end.
Definition fl177_178 (l:Line) := match l with L0 => L0 | L1 => L11 | L2 => L9 | L3 => L7 | L4 => L12 | L5 => L8 | L6 => L10 | L7 => L14 | L8 => L17 | L9 => L13 | L10 => L15 | L11 => L18 | L12 => L16 | L13 => L2 | L14 => L3 | L15 => L6 | L16 => L4 | L17 => L5 | L18 => L1 | L19 => L28 | L20 => L25 | L21 => L21 | L22 => L32 | L23 => L22 | L24 => L24 | L25 => L29 | L26 => L34 | L27 => L26 | L28 => L33 | L29 => L20 | L30 => L30 | L31 => L31 | L32 => L23 | L33 => L19 | L34 => L27 end.

(* P178 : S5 S15 S21 S26 S32 S46 S51 -> 
   P180 : S6 S8 S18 S25 S36 S47 S53  *)
Definition fp178_180 (p:Point) := match p with P0 => P13 | P1 => P8 | P2 => P6 | P3 => P5 | P4 => P7 | P5 => P14 | P6 => P0 | P7 => P3 | P8 => P9 | P9 => P12 | P10 => P2 | P11 => P1 | P12 => P11 | P13 => P10 | P14 => P4 end.
Definition fl178_180 (l:Line) := match l with L0 => L32 | L1 => L28 | L2 => L6 | L3 => L21 | L4 => L16 | L5 => L11 | L6 => L25 | L7 => L3 | L8 => L18 | L9 => L24 | L10 => L20 | L11 => L8 | L12 => L27 | L13 => L15 | L14 => L7 | L15 => L2 | L16 => L34 | L17 => L31 | L18 => L33 | L19 => L17 | L20 => L29 | L21 => L30 | L22 => L12 | L23 => L26 | L24 => L10 | L25 => L13 | L26 => L22 | L27 => L23 | L28 => L19 | L29 => L9 | L30 => L14 | L31 => L1 | L32 => L4 | L33 => L5 | L34 => L0 end.

(* P180 : S6 S8 S18 S25 S36 S47 S53 -> 
   P182 : S6 S8 S21 S26 S37 S40 S55  *)
Definition fp180_182 (p:Point) := match p with P0 => P4 | P1 => P9 | P2 => P14 | P3 => P0 | P4 => P3 | P5 => P10 | P6 => P13 | P7 => P1 | P8 => P6 | P9 => P7 | P10 => P12 | P11 => P2 | P12 => P5 | P13 => P8 | P14 => P11 end.
Definition fl180_182 (l:Line) := match l with L0 => L23 | L1 => L1 | L2 => L25 | L3 => L7 | L4 => L26 | L5 => L17 | L6 => L24 | L7 => L21 | L8 => L33 | L9 => L29 | L10 => L10 | L11 => L18 | L12 => L4 | L13 => L9 | L14 => L14 | L15 => L6 | L16 => L27 | L17 => L19 | L18 => L31 | L19 => L5 | L20 => L2 | L21 => L3 | L22 => L0 | L23 => L22 | L24 => L15 | L25 => L20 | L26 => L12 | L27 => L34 | L28 => L8 | L29 => L13 | L30 => L30 | L31 => L11 | L32 => L32 | L33 => L28 | L34 => L16 end.

(* P182 : S6 S8 S21 S26 S37 S40 S55 -> 
   P185 : S6 S8 S23 S27 S39 S44 S48  *)
Definition fp182_185 (p:Point) := match p with P0 => P4 | P1 => P9 | P2 => P14 | P3 => P3 | P4 => P0 | P5 => P13 | P6 => P10 | P7 => P7 | P8 => P12 | P9 => P1 | P10 => P6 | P11 => P11 | P12 => P8 | P13 => P5 | P14 => P2 end.
Definition fl182_185 (l:Line) := match l with L0 => L23 | L1 => L1 | L2 => L25 | L3 => L26 | L4 => L7 | L5 => L24 | L6 => L17 | L7 => L4 | L8 => L33 | L9 => L18 | L10 => L10 | L11 => L29 | L12 => L21 | L13 => L31 | L14 => L14 | L15 => L19 | L16 => L27 | L17 => L6 | L18 => L9 | L19 => L15 | L20 => L20 | L21 => L12 | L22 => L22 | L23 => L0 | L24 => L5 | L25 => L2 | L26 => L3 | L27 => L16 | L28 => L28 | L29 => L11 | L30 => L32 | L31 => L13 | L32 => L30 | L33 => L8 | L34 => L34 end.

(* P185 : S6 S8 S23 S27 S39 S44 S48 -> 
   P186 : S6 S9 S18 S29 S32 S44 S55  *)
Definition fp185_186 (p:Point) := match p with P0 => P10 | P1 => P5 | P2 => P12 | P3 => P1 | P4 => P8 | P5 => P3 | P6 => P14 | P7 => P0 | P8 => P9 | P9 => P6 | P10 => P11 | P11 => P2 | P12 => P7 | P13 => P4 | P14 => P13 end.
Definition fl185_186 (l:Line) := match l with L0 => L30 | L1 => L8 | L2 => L19 | L3 => L4 | L4 => L34 | L5 => L13 | L6 => L25 | L7 => L27 | L8 => L29 | L9 => L28 | L10 => L2 | L11 => L17 | L12 => L12 | L13 => L5 | L14 => L16 | L15 => L9 | L16 => L26 | L17 => L20 | L18 => L33 | L19 => L11 | L20 => L10 | L21 => L7 | L22 => L0 | L23 => L32 | L24 => L18 | L25 => L24 | L26 => L3 | L27 => L21 | L28 => L1 | L29 => L15 | L30 => L22 | L31 => L6 | L32 => L23 | L33 => L31 | L34 => L14 end.

(* P186 : S6 S9 S18 S29 S32 S44 S55 -> 
   P188 : S6 S9 S20 S27 S36 S41 S54  *)
Definition fp186_188 (p:Point) := match p with P0 => P5 | P1 => P12 | P2 => P10 | P3 => P9 | P4 => P11 | P5 => P6 | P6 => P0 | P7 => P4 | P8 => P2 | P9 => P7 | P10 => P13 | P11 => P14 | P12 => P8 | P13 => P1 | P14 => P3 end.
Definition fl186_188 (l:Line) := match l with L0 => L30 | L1 => L29 | L2 => L2 | L3 => L17 | L4 => L28 | L5 => L27 | L6 => L12 | L7 => L5 | L8 => L16 | L9 => L20 | L10 => L26 | L11 => L9 | L12 => L33 | L13 => L25 | L14 => L19 | L15 => L4 | L16 => L8 | L17 => L34 | L18 => L13 | L19 => L21 | L20 => L18 | L21 => L10 | L22 => L23 | L23 => L22 | L24 => L14 | L25 => L11 | L26 => L24 | L27 => L15 | L28 => L7 | L29 => L31 | L30 => L32 | L31 => L1 | L32 => L0 | L33 => L3 | L34 => L6 end.

(* P188 : S6 S9 S20 S27 S36 S41 S54 -> 
   P191 : S6 S9 S23 S30 S34 S40 S53  *)
Definition fp188_191 (p:Point) := match p with P0 => P5 | P1 => P10 | P2 => P12 | P3 => P11 | P4 => P9 | P5 => P6 | P6 => P0 | P7 => P3 | P8 => P1 | P9 => P14 | P10 => P8 | P11 => P7 | P12 => P13 | P13 => P2 | P14 => P4 end.
Definition fl188_191 (l:Line) := match l with L0 => L30 | L1 => L29 | L2 => L2 | L3 => L12 | L4 => L27 | L5 => L28 | L6 => L17 | L7 => L4 | L8 => L8 | L9 => L25 | L10 => L19 | L11 => L13 | L12 => L34 | L13 => L20 | L14 => L26 | L15 => L5 | L16 => L16 | L17 => L33 | L18 => L9 | L19 => L24 | L20 => L11 | L21 => L14 | L22 => L22 | L23 => L23 | L24 => L10 | L25 => L18 | L26 => L21 | L27 => L7 | L28 => L15 | L29 => L31 | L30 => L32 | L31 => L1 | L32 => L0 | L33 => L6 | L34 => L3 end.

(* P191 : S6 S9 S23 S30 S34 S40 S53 -> 
   P192 : S6 S11 S16 S25 S37 S44 S54  *)
Definition fp191_192 (p:Point) := match p with P0 => P3 | P1 => P7 | P2 => P11 | P3 => P4 | P4 => P0 | P5 => P12 | P6 => P8 | P7 => P9 | P8 => P13 | P9 => P1 | P10 => P5 | P11 => P14 | P12 => P10 | P13 => P6 | P14 => P2 end.
Definition fl191_192 (l:Line) := match l with L0 => L22 | L1 => L1 | L2 => L20 | L3 => L21 | L4 => L12 | L5 => L19 | L6 => L15 | L7 => L3 | L8 => L28 | L9 => L13 | L10 => L10 | L11 => L31 | L12 => L26 | L13 => L29 | L14 => L14 | L15 => L24 | L16 => L34 | L17 => L5 | L18 => L11 | L19 => L17 | L20 => L25 | L21 => L7 | L22 => L23 | L23 => L0 | L24 => L6 | L25 => L2 | L26 => L4 | L27 => L16 | L28 => L33 | L29 => L9 | L30 => L30 | L31 => L18 | L32 => L32 | L33 => L8 | L34 => L27 end.

(* P192 : S6 S11 S16 S25 S37 S44 S54 -> 
   P195 : S6 S11 S20 S29 S39 S40 S50  *)
Definition fp192_195 (p:Point) := match p with P0 => P1 | P1 => P0 | P2 => P2 | P3 => P12 | P4 => P14 | P5 => P11 | P6 => P13 | P7 => P10 | P8 => P8 | P9 => P9 | P10 => P7 | P11 => P5 | P12 => P3 | P13 => P6 | P14 => P4 end.
Definition fl192_195 (l:Line) := match l with L0 => L0 | L1 => L9 | L2 => L11 | L3 => L8 | L4 => L10 | L5 => L12 | L6 => L7 | L7 => L6 | L8 => L3 | L9 => L1 | L10 => L4 | L11 => L2 | L12 => L5 | L13 => L13 | L14 => L17 | L15 => L16 | L16 => L15 | L17 => L14 | L18 => L18 | L19 => L26 | L20 => L20 | L21 => L33 | L22 => L30 | L23 => L23 | L24 => L27 | L25 => L31 | L26 => L19 | L27 => L24 | L28 => L34 | L29 => L29 | L30 => L22 | L31 => L25 | L32 => L32 | L33 => L21 | L34 => L28 end.

(* P195 : S6 S11 S20 S29 S39 S40 S50 -> 
   P196 : S6 S11 S21 S30 S36 S43 S48  *)
Definition fp195_196 (p:Point) := match p with P0 => P2 | P1 => P0 | P2 => P1 | P3 => P8 | P4 => P9 | P5 => P7 | P6 => P10 | P7 => P13 | P8 => P12 | P9 => P14 | P10 => P11 | P11 => P6 | P12 => P3 | P13 => P5 | P14 => P4 end.
Definition fl195_196 (l:Line) := match l with L0 => L0 | L1 => L18 | L2 => L13 | L3 => L16 | L4 => L14 | L5 => L15 | L6 => L17 | L7 => L4 | L8 => L5 | L9 => L1 | L10 => L6 | L11 => L2 | L12 => L3 | L13 => L11 | L14 => L7 | L15 => L8 | L16 => L12 | L17 => L10 | L18 => L9 | L19 => L24 | L20 => L20 | L21 => L27 | L22 => L32 | L23 => L23 | L24 => L33 | L25 => L29 | L26 => L21 | L27 => L26 | L28 => L28 | L29 => L31 | L30 => L22 | L31 => L25 | L32 => L30 | L33 => L19 | L34 => L34 end.

(* P196 : S6 S11 S21 S30 S36 S43 S48 -> 
   P199 : S6 S13 S16 S29 S34 S47 S48  *)
Definition fp196_199 (p:Point) := match p with P0 => P8 | P1 => P6 | P2 => P13 | P3 => P14 | P4 => P5 | P5 => P7 | P6 => P0 | P7 => P9 | P8 => P2 | P9 => P12 | P10 => P3 | P11 => P4 | P12 => P11 | P13 => P1 | P14 => P10 end.
Definition fl196_199 (l:Line) := match l with L0 => L32 | L1 => L27 | L2 => L3 | L3 => L18 | L4 => L20 | L5 => L24 | L6 => L8 | L7 => L2 | L8 => L15 | L9 => L34 | L10 => L33 | L11 => L7 | L12 => L31 | L13 => L21 | L14 => L25 | L15 => L6 | L16 => L11 | L17 => L28 | L18 => L16 | L19 => L19 | L20 => L14 | L21 => L9 | L22 => L23 | L23 => L30 | L24 => L17 | L25 => L12 | L26 => L29 | L27 => L13 | L28 => L10 | L29 => L26 | L30 => L22 | L31 => L4 | L32 => L0 | L33 => L5 | L34 => L1 end.

(* P199 : S6 S13 S16 S29 S34 S47 S48 -> 
   P201 : S6 S13 S18 S30 S37 S41 S50  *)
Definition fp199_201 (p:Point) := match p with P0 => P9 | P1 => P4 | P2 => P14 | P3 => P7 | P4 => P1 | P5 => P12 | P6 => P6 | P7 => P3 | P8 => P13 | P9 => P0 | P10 => P10 | P11 => P11 | P12 => P5 | P13 => P8 | P14 => P2 end.
Definition fl199_201 (l:Line) := match l with L0 => L23 | L1 => L10 | L2 => L33 | L3 => L21 | L4 => L4 | L5 => L29 | L6 => L18 | L7 => L7 | L8 => L25 | L9 => L17 | L10 => L1 | L11 => L24 | L12 => L26 | L13 => L19 | L14 => L14 | L15 => L31 | L16 => L27 | L17 => L9 | L18 => L6 | L19 => L13 | L20 => L28 | L21 => L3 | L22 => L22 | L23 => L0 | L24 => L11 | L25 => L8 | L26 => L12 | L27 => L16 | L28 => L20 | L29 => L5 | L30 => L30 | L31 => L15 | L32 => L32 | L33 => L2 | L34 => L34 end.

(* P201 : S6 S13 S18 S30 S37 S41 S50 -> 
   P202 : S6 S13 S23 S26 S32 S43 S54  *)
Definition fp201_202 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P4 | P4 => P3 | P5 => P6 | P6 => P5 | P7 => P9 | P8 => P10 | P9 => P7 | P10 => P8 | P11 => P14 | P12 => P13 | P13 => P12 | P14 => P11 end.
Definition fl201_202 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L4 | L4 => L3 | L5 => L6 | L6 => L5 | L7 => L12 | L8 => L8 | L9 => L11 | L10 => L10 | L11 => L9 | L12 => L7 | L13 => L18 | L14 => L14 | L15 => L17 | L16 => L16 | L17 => L15 | L18 => L13 | L19 => L24 | L20 => L25 | L21 => L26 | L22 => L23 | L23 => L22 | L24 => L19 | L25 => L20 | L26 => L21 | L27 => L34 | L28 => L33 | L29 => L31 | L30 => L32 | L31 => L29 | L32 => L30 | L33 => L28 | L34 => L27 end.

(* P202 : S6 S13 S23 S26 S32 S43 S54 -> 
   P205 : S6 S14 S16 S26 S39 S41 S53  *)
Definition fp202_205 (p:Point) := match p with P0 => P14 | P1 => P9 | P2 => P4 | P3 => P8 | P4 => P5 | P5 => P2 | P6 => P11 | P7 => P6 | P8 => P7 | P9 => P12 | P10 => P1 | P11 => P13 | P12 => P0 | P13 => P3 | P14 => P10 end.
Definition fl202_205 (l:Line) := match l with L0 => L23 | L1 => L27 | L2 => L14 | L3 => L31 | L4 => L9 | L5 => L6 | L6 => L19 | L7 => L29 | L8 => L10 | L9 => L4 | L10 => L33 | L11 => L21 | L12 => L18 | L13 => L7 | L14 => L25 | L15 => L24 | L16 => L1 | L17 => L17 | L18 => L26 | L19 => L8 | L20 => L3 | L21 => L20 | L22 => L32 | L23 => L30 | L24 => L28 | L25 => L12 | L26 => L2 | L27 => L13 | L28 => L15 | L29 => L16 | L30 => L0 | L31 => L34 | L32 => L22 | L33 => L5 | L34 => L11 end.

(* P205 : S6 S14 S16 S26 S39 S41 S53 -> 
   P206 : S6 S14 S20 S25 S34 S43 S55  *)
Definition fp205_206 (p:Point) := match p with P0 => P11 | P1 => P3 | P2 => P7 | P3 => P1 | P4 => P13 | P5 => P5 | P6 => P9 | P7 => P2 | P8 => P14 | P9 => P6 | P10 => P10 | P11 => P0 | P12 => P12 | P13 => P4 | P14 => P8 end.
Definition fl205_206 (l:Line) := match l with L0 => L22 | L1 => L11 | L2 => L29 | L3 => L14 | L4 => L34 | L5 => L5 | L6 => L24 | L7 => L21 | L8 => L19 | L9 => L20 | L10 => L15 | L11 => L1 | L12 => L12 | L13 => L13 | L14 => L3 | L15 => L10 | L16 => L26 | L17 => L28 | L18 => L31 | L19 => L8 | L20 => L9 | L21 => L7 | L22 => L0 | L23 => L32 | L24 => L6 | L25 => L25 | L26 => L16 | L27 => L27 | L28 => L17 | L29 => L2 | L30 => L30 | L31 => L18 | L32 => L23 | L33 => L33 | L34 => L4 end.

(* P206 : S6 S14 S20 S25 S34 S43 S55 -> 
   P209 : S6 S14 S21 S27 S32 S47 S50  *)
Definition fp206_209 (p:Point) := match p with P0 => P7 | P1 => P3 | P2 => P11 | P3 => P2 | P4 => P10 | P5 => P6 | P6 => P14 | P7 => P1 | P8 => P9 | P9 => P5 | P10 => P13 | P11 => P0 | P12 => P8 | P13 => P4 | P14 => P12 end.
Definition fl206_209 (l:Line) := match l with L0 => L22 | L1 => L13 | L2 => L31 | L3 => L10 | L4 => L28 | L5 => L3 | L6 => L26 | L7 => L19 | L8 => L21 | L9 => L20 | L10 => L12 | L11 => L1 | L12 => L15 | L13 => L11 | L14 => L5 | L15 => L14 | L16 => L24 | L17 => L34 | L18 => L29 | L19 => L16 | L20 => L18 | L21 => L17 | L22 => L0 | L23 => L30 | L24 => L4 | L25 => L25 | L26 => L8 | L27 => L33 | L28 => L7 | L29 => L2 | L30 => L32 | L31 => L9 | L32 => L23 | L33 => L27 | L34 => L6 end.

(* P209 : S6 S14 S21 S27 S32 S47 S50 -> 
   P211 : S7 S9 S18 S28 S38 S41 S53  *)
Definition fp209_211 (p:Point) := match p with P0 => P0 | P1 => P2 | P2 => P1 | P3 => P4 | P4 => P3 | P5 => P5 | P6 => P6 | P7 => P10 | P8 => P9 | P9 => P7 | P10 => P8 | P11 => P13 | P12 => P14 | P13 => P12 | P14 => P11 end.
Definition fl209_211 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L4 | L4 => L3 | L5 => L6 | L6 => L5 | L7 => L15 | L8 => L18 | L9 => L14 | L10 => L13 | L11 => L16 | L12 => L17 | L13 => L8 | L14 => L11 | L15 => L7 | L16 => L9 | L17 => L12 | L18 => L10 | L19 => L24 | L20 => L23 | L21 => L26 | L22 => L25 | L23 => L22 | L24 => L21 | L25 => L20 | L26 => L19 | L27 => L29 | L28 => L30 | L29 => L28 | L30 => L27 | L31 => L34 | L32 => L33 | L33 => L31 | L34 => L32 end.

(* P211 : S7 S9 S18 S28 S38 S41 S53 -> 
   P212 : S7 S9 S22 S24 S34 S45 S55  *)
Definition fp211_212 (p:Point) := match p with P0 => P2 | P1 => P0 | P2 => P1 | P3 => P12 | P4 => P13 | P5 => P11 | P6 => P14 | P7 => P6 | P8 => P3 | P9 => P5 | P10 => P4 | P11 => P9 | P12 => P8 | P13 => P10 | P14 => P7 end.
Definition fl211_212 (l:Line) := match l with L0 => L0 | L1 => L16 | L2 => L14 | L3 => L15 | L4 => L17 | L5 => L18 | L6 => L13 | L7 => L6 | L8 => L1 | L9 => L3 | L10 => L2 | L11 => L4 | L12 => L5 | L13 => L7 | L14 => L10 | L15 => L9 | L16 => L8 | L17 => L11 | L18 => L12 | L19 => L26 | L20 => L20 | L21 => L30 | L22 => L33 | L23 => L28 | L24 => L21 | L25 => L25 | L26 => L32 | L27 => L22 | L28 => L34 | L29 => L29 | L30 => L24 | L31 => L31 | L32 => L19 | L33 => L27 | L34 => L23 end.

(* P212 : S7 S9 S22 S24 S34 S45 S55 -> 
   P215 : S7 S9 S23 S27 S32 S46 S52  *)
Definition fp212_215 (p:Point) := match p with P0 => P2 | P1 => P1 | P2 => P0 | P3 => P12 | P4 => P13 | P5 => P14 | P6 => P11 | P7 => P9 | P8 => P8 | P9 => P7 | P10 => P10 | P11 => P6 | P12 => P3 | P13 => P4 | P14 => P5 end.
Definition fl212_215 (l:Line) := match l with L0 => L0 | L1 => L16 | L2 => L14 | L3 => L18 | L4 => L13 | L5 => L15 | L6 => L17 | L7 => L11 | L8 => L8 | L9 => L12 | L10 => L10 | L11 => L7 | L12 => L9 | L13 => L4 | L14 => L2 | L15 => L5 | L16 => L1 | L17 => L6 | L18 => L3 | L19 => L30 | L20 => L20 | L21 => L26 | L22 => L33 | L23 => L28 | L24 => L32 | L25 => L25 | L26 => L21 | L27 => L27 | L28 => L23 | L29 => L31 | L30 => L19 | L31 => L29 | L32 => L24 | L33 => L22 | L34 => L34 end.

(* P215 : S7 S9 S23 S27 S32 S46 S52 -> 
   P217 : S7 S10 S16 S31 S37 S41 S52  *)
Definition fp215_217 (p:Point) := match p with P0 => P12 | P1 => P6 | P2 => P9 | P3 => P1 | P4 => P14 | P5 => P4 | P6 => P7 | P7 => P2 | P8 => P13 | P9 => P3 | P10 => P8 | P11 => P0 | P12 => P11 | P13 => P5 | P14 => P10 end.
Definition fl215_217 (l:Line) := match l with L0 => L33 | L1 => L9 | L2 => L26 | L3 => L16 | L4 => L20 | L5 => L5 | L6 => L30 | L7 => L31 | L8 => L32 | L9 => L34 | L10 => L15 | L11 => L2 | L12 => L7 | L13 => L18 | L14 => L4 | L15 => L10 | L16 => L29 | L17 => L23 | L18 => L21 | L19 => L8 | L20 => L11 | L21 => L12 | L22 => L0 | L23 => L19 | L24 => L6 | L25 => L27 | L26 => L14 | L27 => L25 | L28 => L17 | L29 => L1 | L30 => L24 | L31 => L13 | L32 => L28 | L33 => L22 | L34 => L3 end.

(* P217 : S7 S10 S16 S31 S37 S41 S52 -> 
   P219 : S7 S10 S21 S28 S32 S43 S55  *)
Definition fp217_219 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P4 | P4 => P3 | P5 => P6 | P6 => P5 | P7 => P10 | P8 => P9 | P9 => P8 | P10 => P7 | P11 => P13 | P12 => P14 | P13 => P11 | P14 => P12 end.
Definition fl217_219 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L4 | L4 => L3 | L5 => L6 | L6 => L5 | L7 => L12 | L8 => L10 | L9 => L9 | L10 => L8 | L11 => L11 | L12 => L7 | L13 => L13 | L14 => L16 | L15 => L17 | L16 => L14 | L17 => L15 | L18 => L18 | L19 => L26 | L20 => L23 | L21 => L24 | L22 => L25 | L23 => L20 | L24 => L21 | L25 => L22 | L26 => L19 | L27 => L33 | L28 => L34 | L29 => L32 | L30 => L31 | L31 => L30 | L32 => L29 | L33 => L27 | L34 => L28 end.

(* P219 : S7 S10 S21 S28 S32 S43 S55 -> 
   P220 : S7 S10 S23 S24 S39 S42 S53  *)
Definition fp219_220 (p:Point) := match p with P0 => P10 | P1 => P13 | P2 => P4 | P3 => P7 | P4 => P2 | P5 => P5 | P6 => P12 | P7 => P3 | P8 => P14 | P9 => P9 | P10 => P0 | P11 => P11 | P12 => P6 | P13 => P1 | P14 => P8 end.
Definition fl219_220 (l:Line) := match l with L0 => L25 | L1 => L13 | L2 => L30 | L3 => L19 | L4 => L4 | L5 => L34 | L6 => L8 | L7 => L16 | L8 => L6 | L9 => L32 | L10 => L21 | L11 => L11 | L12 => L28 | L13 => L1 | L14 => L24 | L15 => L26 | L16 => L7 | L17 => L17 | L18 => L23 | L19 => L3 | L20 => L31 | L21 => L10 | L22 => L22 | L23 => L18 | L24 => L14 | L25 => L0 | L26 => L15 | L27 => L27 | L28 => L12 | L29 => L29 | L30 => L2 | L31 => L20 | L32 => L9 | L33 => L33 | L34 => L5 end.

(* P220 : S7 S10 S23 S24 S39 S42 S53 -> 
   P223 : S7 S11 S16 S28 S39 S45 S48  *)
Definition fp220_223 (p:Point) := match p with P0 => P9 | P1 => P6 | P2 => P12 | P3 => P8 | P4 => P2 | P5 => P13 | P6 => P3 | P7 => P14 | P8 => P4 | P9 => P7 | P10 => P1 | P11 => P5 | P12 => P11 | P13 => P0 | P14 => P10 end.
Definition fl220_223 (l:Line) := match l with L0 => L33 | L1 => L18 | L2 => L21 | L3 => L23 | L4 => L10 | L5 => L29 | L6 => L4 | L7 => L15 | L8 => L7 | L9 => L34 | L10 => L31 | L11 => L2 | L12 => L32 | L13 => L9 | L14 => L30 | L15 => L20 | L16 => L5 | L17 => L16 | L18 => L26 | L19 => L8 | L20 => L24 | L21 => L3 | L22 => L27 | L23 => L13 | L24 => L17 | L25 => L0 | L26 => L14 | L27 => L25 | L28 => L6 | L29 => L28 | L30 => L11 | L31 => L19 | L32 => L1 | L33 => L22 | L34 => L12 end.

(* P223 : S7 S11 S16 S28 S39 S45 S48 -> 
   P224 : S7 S11 S21 S24 S37 S46 S50  *)
Definition fp223_224 (p:Point) := match p with P0 => P6 | P1 => P9 | P2 => P12 | P3 => P10 | P4 => P11 | P5 => P0 | P6 => P5 | P7 => P4 | P8 => P1 | P9 => P14 | P10 => P7 | P11 => P13 | P12 => P8 | P13 => P3 | P14 => P2 end.
Definition fl223_224 (l:Line) := match l with L0 => L33 | L1 => L34 | L2 => L2 | L3 => L7 | L4 => L31 | L5 => L32 | L6 => L15 | L7 => L29 | L8 => L10 | L9 => L18 | L10 => L23 | L11 => L21 | L12 => L4 | L13 => L26 | L14 => L16 | L15 => L30 | L16 => L20 | L17 => L5 | L18 => L9 | L19 => L13 | L20 => L8 | L21 => L19 | L22 => L25 | L23 => L14 | L24 => L11 | L25 => L22 | L26 => L24 | L27 => L0 | L28 => L1 | L29 => L6 | L30 => L3 | L31 => L17 | L32 => L12 | L33 => L27 | L34 => L28 end.

(* P224 : S7 S11 S21 S24 S37 S46 S50 -> 
   P227 : S7 S11 S22 S25 S38 S43 S52  *)
Definition fp224_227 (p:Point) := match p with P0 => P6 | P1 => P9 | P2 => P12 | P3 => P10 | P4 => P11 | P5 => P0 | P6 => P5 | P7 => P4 | P8 => P1 | P9 => P14 | P10 => P7 | P11 => P13 | P12 => P8 | P13 => P3 | P14 => P2 end.
Definition fl224_227 (l:Line) := match l with L0 => L33 | L1 => L34 | L2 => L2 | L3 => L7 | L4 => L31 | L5 => L32 | L6 => L15 | L7 => L29 | L8 => L10 | L9 => L18 | L10 => L23 | L11 => L21 | L12 => L4 | L13 => L26 | L14 => L16 | L15 => L30 | L16 => L20 | L17 => L5 | L18 => L9 | L19 => L13 | L20 => L8 | L21 => L19 | L22 => L25 | L23 => L14 | L24 => L11 | L25 => L22 | L26 => L24 | L27 => L0 | L28 => L1 | L29 => L6 | L30 => L3 | L31 => L17 | L32 => L12 | L33 => L27 | L34 => L28 end.

(* P227 : S7 S11 S22 S25 S38 S43 S52 -> 
   P228 : S7 S12 S18 S25 S37 S42 S55  *)
Definition fp227_228 (p:Point) := match p with P0 => P9 | P1 => P12 | P2 => P6 | P3 => P7 | P4 => P1 | P5 => P4 | P6 => P14 | P7 => P3 | P8 => P13 | P9 => P8 | P10 => P2 | P11 => P11 | P12 => P5 | P13 => P0 | P14 => P10 end.
Definition fl227_228 (l:Line) := match l with L0 => L33 | L1 => L10 | L2 => L23 | L3 => L21 | L4 => L18 | L5 => L29 | L6 => L4 | L7 => L9 | L8 => L16 | L9 => L30 | L10 => L20 | L11 => L5 | L12 => L26 | L13 => L15 | L14 => L34 | L15 => L31 | L16 => L2 | L17 => L7 | L18 => L32 | L19 => L13 | L20 => L28 | L21 => L3 | L22 => L22 | L23 => L8 | L24 => L11 | L25 => L0 | L26 => L12 | L27 => L25 | L28 => L1 | L29 => L24 | L30 => L17 | L31 => L19 | L32 => L6 | L33 => L27 | L34 => L14 end.

(* P228 : S7 S12 S18 S25 S37 S42 S55 -> 
   P231 : S7 S12 S22 S27 S39 S41 S50  *)
Definition fp228_231 (p:Point) := match p with P0 => P11 | P1 => P3 | P2 => P7 | P3 => P2 | P4 => P14 | P5 => P6 | P6 => P10 | P7 => P0 | P8 => P12 | P9 => P4 | P10 => P8 | P11 => P1 | P12 => P13 | P13 => P5 | P14 => P9 end.
Definition fl228_231 (l:Line) := match l with L0 => L22 | L1 => L14 | L2 => L34 | L3 => L5 | L4 => L24 | L5 => L11 | L6 => L29 | L7 => L19 | L8 => L20 | L9 => L21 | L10 => L1 | L11 => L12 | L12 => L15 | L13 => L3 | L14 => L10 | L15 => L13 | L16 => L28 | L17 => L31 | L18 => L26 | L19 => L18 | L20 => L16 | L21 => L17 | L22 => L0 | L23 => L23 | L24 => L9 | L25 => L27 | L26 => L6 | L27 => L33 | L28 => L2 | L29 => L7 | L30 => L32 | L31 => L4 | L32 => L30 | L33 => L25 | L34 => L8 end.

(* P231 : S7 S12 S22 S27 S39 S41 S50 -> 
   P233 : S7 S12 S23 S31 S34 S43 S48  *)
Definition fp231_233 (p:Point) := match p with P0 => P11 | P1 => P7 | P2 => P3 | P3 => P2 | P4 => P14 | P5 => P10 | P6 => P6 | P7 => P1 | P8 => P13 | P9 => P9 | P10 => P5 | P11 => P0 | P12 => P12 | P13 => P8 | P14 => P4 end.
Definition fl231_233 (l:Line) := match l with L0 => L22 | L1 => L14 | L2 => L34 | L3 => L11 | L4 => L29 | L5 => L5 | L6 => L24 | L7 => L31 | L8 => L28 | L9 => L26 | L10 => L10 | L11 => L3 | L12 => L13 | L13 => L12 | L14 => L1 | L15 => L15 | L16 => L20 | L17 => L19 | L18 => L21 | L19 => L17 | L20 => L16 | L21 => L18 | L22 => L0 | L23 => L23 | L24 => L6 | L25 => L27 | L26 => L9 | L27 => L25 | L28 => L8 | L29 => L4 | L30 => L30 | L31 => L7 | L32 => L32 | L33 => L33 | L34 => L2 end.

(* P233 : S7 S12 S23 S31 S34 S43 S48 -> 
   P234 : S7 S15 S16 S25 S34 S46 S53  *)
Definition fp233_234 (p:Point) := match p with P0 => P9 | P1 => P6 | P2 => P12 | P3 => P8 | P4 => P2 | P5 => P13 | P6 => P3 | P7 => P14 | P8 => P4 | P9 => P7 | P10 => P1 | P11 => P5 | P12 => P11 | P13 => P0 | P14 => P10 end.
Definition fl233_234 (l:Line) := match l with L0 => L33 | L1 => L18 | L2 => L21 | L3 => L23 | L4 => L10 | L5 => L29 | L6 => L4 | L7 => L15 | L8 => L7 | L9 => L34 | L10 => L31 | L11 => L2 | L12 => L32 | L13 => L9 | L14 => L30 | L15 => L20 | L16 => L5 | L17 => L16 | L18 => L26 | L19 => L8 | L20 => L24 | L21 => L3 | L22 => L27 | L23 => L13 | L24 => L17 | L25 => L0 | L26 => L14 | L27 => L25 | L28 => L6 | L29 => L28 | L30 => L11 | L31 => L19 | L32 => L1 | L33 => L22 | L34 => L12 end.

(* P234 : S7 S15 S16 S25 S34 S46 S53 -> 
   P237 : S7 S15 S18 S31 S32 S45 S50  *)
Definition fp234_237 (p:Point) := match p with P0 => P4 | P1 => P13 | P2 => P10 | P3 => P3 | P4 => P0 | P5 => P9 | P6 => P14 | P7 => P7 | P8 => P12 | P9 => P5 | P10 => P2 | P11 => P11 | P12 => P8 | P13 => P1 | P14 => P6 end.
Definition fl234_237 (l:Line) := match l with L0 => L25 | L1 => L1 | L2 => L23 | L3 => L26 | L4 => L17 | L5 => L24 | L6 => L7 | L7 => L6 | L8 => L16 | L9 => L32 | L10 => L28 | L11 => L11 | L12 => L21 | L13 => L13 | L14 => L34 | L15 => L19 | L16 => L8 | L17 => L4 | L18 => L30 | L19 => L15 | L20 => L20 | L21 => L12 | L22 => L22 | L23 => L2 | L24 => L5 | L25 => L0 | L26 => L3 | L27 => L33 | L28 => L10 | L29 => L29 | L30 => L18 | L31 => L31 | L32 => L9 | L33 => L27 | L34 => L14 end.

(* P237 : S7 S15 S18 S31 S32 S45 S50 -> 
   P239 : S7 S15 S21 S27 S38 S42 S48  *)
Definition fp237_239 (p:Point) := match p with P0 => P3 | P1 => P11 | P2 => P7 | P3 => P4 | P4 => P0 | P5 => P8 | P6 => P12 | P7 => P10 | P8 => P14 | P9 => P6 | P10 => P2 | P11 => P13 | P12 => P9 | P13 => P1 | P14 => P5 end.
Definition fl237_239 (l:Line) := match l with L0 => L22 | L1 => L1 | L2 => L20 | L3 => L19 | L4 => L15 | L5 => L21 | L6 => L12 | L7 => L5 | L8 => L14 | L9 => L29 | L10 => L34 | L11 => L11 | L12 => L24 | L13 => L13 | L14 => L28 | L15 => L26 | L16 => L10 | L17 => L3 | L18 => L31 | L19 => L17 | L20 => L23 | L21 => L7 | L22 => L25 | L23 => L2 | L24 => L6 | L25 => L0 | L26 => L4 | L27 => L27 | L28 => L8 | L29 => L32 | L30 => L18 | L31 => L30 | L32 => L9 | L33 => L33 | L34 => L16 end.

(* P239 : S7 S15 S21 S27 S38 S42 S48 -> 
   P0 : S0 S9 S19 S24 S36 S46 S53  *)
Definition fp239_0 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P14 | P8 => P13 | P9 => P12 | P10 => P11 | P11 => P10 | P12 => P9 | P13 => P8 | P14 => P7 end.
Definition fl239_0 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L6 | L4 => L5 | L5 => L4 | L6 => L3 | L7 => L7 | L8 => L11 | L9 => L10 | L10 => L9 | L11 => L8 | L12 => L12 | L13 => L14 | L14 => L13 | L15 => L15 | L16 => L18 | L17 => L17 | L18 => L16 | L19 => L22 | L20 => L21 | L21 => L20 | L22 => L19 | L23 => L26 | L24 => L25 | L25 => L24 | L26 => L23 | L27 => L28 | L28 => L27 | L29 => L30 | L30 => L29 | L31 => L31 | L32 => L32 | L33 => L33 | L34 => L34 end.

(* ~~~~~~~~~~ CLASS 1 ~~~~~~~~~~ *)
(* P1 : S0 S9 S19 S28 S38 S40 S53 -> 
   P2 : S0 S9 S20 S27 S36 S46 S49  *)
Definition fp1_2 (p:Point) := match p with P0 => P3 | P1 => P10 | P2 => P14 | P3 => P4 | P4 => P0 | P5 => P13 | P6 => P9 | P7 => P5 | P8 => P1 | P9 => P12 | P10 => P8 | P11 => P2 | P12 => P6 | P13 => P7 | P14 => P11 end.
Definition fl1_2 (l:Line) := match l with L0 => L19 | L1 => L1 | L2 => L21 | L3 => L12 | L4 => L20 | L5 => L15 | L6 => L22 | L7 => L4 | L8 => L8 | L9 => L34 | L10 => L30 | L11 => L13 | L12 => L25 | L13 => L27 | L14 => L14 | L15 => L23 | L16 => L31 | L17 => L6 | L18 => L9 | L19 => L24 | L20 => L7 | L21 => L26 | L22 => L17 | L23 => L5 | L24 => L0 | L25 => L3 | L26 => L2 | L27 => L11 | L28 => L28 | L29 => L16 | L30 => L32 | L31 => L29 | L32 => L10 | L33 => L33 | L34 => L18 end.

(* P2 : S0 S9 S20 S27 S36 S46 S49 -> 
   P4 : S0 S9 S22 S24 S35 S44 S55  *)
Definition fp2_4 (p:Point) := match p with P0 => P3 | P1 => P10 | P2 => P14 | P3 => P0 | P4 => P4 | P5 => P9 | P6 => P13 | P7 => P12 | P8 => P8 | P9 => P5 | P10 => P1 | P11 => P11 | P12 => P7 | P13 => P6 | P14 => P2 end.
Definition fl2_4 (l:Line) := match l with L0 => L19 | L1 => L1 | L2 => L21 | L3 => L20 | L4 => L12 | L5 => L22 | L6 => L15 | L7 => L25 | L8 => L8 | L9 => L13 | L10 => L30 | L11 => L34 | L12 => L4 | L13 => L9 | L14 => L14 | L15 => L6 | L16 => L31 | L17 => L23 | L18 => L27 | L19 => L0 | L20 => L3 | L21 => L2 | L22 => L5 | L23 => L17 | L24 => L24 | L25 => L7 | L26 => L26 | L27 => L18 | L28 => L33 | L29 => L29 | L30 => L10 | L31 => L16 | L32 => L32 | L33 => L28 | L34 => L11 end.

(* P4 : S0 S9 S22 S24 S35 S44 S55 -> 
   P7 : S0 S10 S16 S31 S37 S44 S49  *)
Definition fp4_7 (p:Point) := match p with P0 => P5 | P1 => P13 | P2 => P7 | P3 => P11 | P4 => P9 | P5 => P1 | P6 => P3 | P7 => P0 | P8 => P6 | P9 => P14 | P10 => P8 | P11 => P12 | P12 => P10 | P13 => P2 | P14 => P4 end.
Definition fl4_7 (l:Line) := match l with L0 => L28 | L1 => L29 | L2 => L12 | L3 => L2 | L4 => L27 | L5 => L30 | L6 => L17 | L7 => L21 | L8 => L32 | L9 => L25 | L10 => L6 | L11 => L16 | L12 => L11 | L13 => L3 | L14 => L26 | L15 => L22 | L16 => L13 | L17 => L10 | L18 => L31 | L19 => L24 | L20 => L34 | L21 => L14 | L22 => L5 | L23 => L23 | L24 => L33 | L25 => L18 | L26 => L4 | L27 => L7 | L28 => L0 | L29 => L9 | L30 => L8 | L31 => L1 | L32 => L15 | L33 => L19 | L34 => L20 end.

(* P7 : S0 S10 S16 S31 S37 S44 S49 -> 
   P8 : S0 S10 S17 S24 S36 S47 S53  *)
Definition fp7_8 (p:Point) := match p with P0 => P14 | P1 => P10 | P2 => P3 | P3 => P1 | P4 => P12 | P5 => P8 | P6 => P5 | P7 => P4 | P8 => P9 | P9 => P13 | P10 => P0 | P11 => P6 | P12 => P7 | P13 => P11 | P14 => P2 end.
Definition fl7_8 (l:Line) := match l with L0 => L19 | L1 => L9 | L2 => L27 | L3 => L23 | L4 => L6 | L5 => L31 | L6 => L14 | L7 => L30 | L8 => L4 | L9 => L13 | L10 => L25 | L11 => L34 | L12 => L8 | L13 => L1 | L14 => L15 | L15 => L12 | L16 => L22 | L17 => L20 | L18 => L21 | L19 => L0 | L20 => L10 | L21 => L11 | L22 => L7 | L23 => L16 | L24 => L33 | L25 => L5 | L26 => L26 | L27 => L18 | L28 => L24 | L29 => L32 | L30 => L3 | L31 => L17 | L32 => L29 | L33 => L28 | L34 => L2 end.

(* P8 : S0 S10 S17 S24 S36 S47 S53 -> 
   P10 : S0 S10 S20 S28 S33 S43 S55  *)
Definition fp8_10 (p:Point) := match p with P0 => P0 | P1 => P2 | P2 => P1 | P3 => P3 | P4 => P4 | P5 => P6 | P6 => P5 | P7 => P12 | P8 => P11 | P9 => P13 | P10 => P14 | P11 => P8 | P12 => P7 | P13 => P9 | P14 => P10 end.
Definition fl8_10 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L5 | L4 => L6 | L5 => L3 | L6 => L4 | L7 => L17 | L8 => L14 | L9 => L13 | L10 => L16 | L11 => L18 | L12 => L15 | L13 => L9 | L14 => L8 | L15 => L12 | L16 => L10 | L17 => L7 | L18 => L11 | L19 => L19 | L20 => L22 | L21 => L21 | L22 => L20 | L23 => L25 | L24 => L24 | L25 => L23 | L26 => L26 | L27 => L34 | L28 => L33 | L29 => L32 | L30 => L31 | L31 => L30 | L32 => L29 | L33 => L28 | L34 => L27 end.

(* P10 : S0 S10 S20 S28 S33 S43 S55 -> 
   P12 : S0 S12 S17 S26 S37 S40 S55  *)
Definition fp10_12 (p:Point) := match p with P0 => P6 | P1 => P12 | P2 => P9 | P3 => P13 | P4 => P8 | P5 => P2 | P6 => P3 | P7 => P1 | P8 => P4 | P9 => P14 | P10 => P7 | P11 => P11 | P12 => P10 | P13 => P0 | P14 => P5 end.
Definition fl10_12 (l:Line) := match l with L0 => L33 | L1 => L32 | L2 => L15 | L3 => L7 | L4 => L31 | L5 => L34 | L6 => L2 | L7 => L20 | L8 => L26 | L9 => L30 | L10 => L9 | L11 => L5 | L12 => L16 | L13 => L10 | L14 => L29 | L15 => L21 | L16 => L4 | L17 => L18 | L18 => L23 | L19 => L28 | L20 => L25 | L21 => L6 | L22 => L11 | L23 => L27 | L24 => L24 | L25 => L3 | L26 => L8 | L27 => L17 | L28 => L0 | L29 => L14 | L30 => L13 | L31 => L12 | L32 => L1 | L33 => L19 | L34 => L22 end.

(* P12 : S0 S12 S17 S26 S37 S40 S55 -> 
   P14 : S0 S12 S19 S31 S36 S43 S48  *)
Definition fp12_14 (p:Point) := match p with P0 => P14 | P1 => P10 | P2 => P3 | P3 => P11 | P4 => P2 | P5 => P6 | P6 => P7 | P7 => P12 | P8 => P1 | P9 => P5 | P10 => P8 | P11 => P0 | P12 => P13 | P13 => P9 | P14 => P4 end.
Definition fl12_14 (l:Line) := match l with L0 => L19 | L1 => L14 | L2 => L31 | L3 => L9 | L4 => L27 | L5 => L6 | L6 => L23 | L7 => L13 | L8 => L8 | L9 => L25 | L10 => L30 | L11 => L4 | L12 => L34 | L13 => L20 | L14 => L1 | L15 => L22 | L16 => L21 | L17 => L15 | L18 => L12 | L19 => L24 | L20 => L11 | L21 => L29 | L22 => L5 | L23 => L17 | L24 => L0 | L25 => L18 | L26 => L16 | L27 => L7 | L28 => L33 | L29 => L2 | L30 => L32 | L31 => L26 | L32 => L10 | L33 => L28 | L34 => L3 end.

(* P14 : S0 S12 S19 S31 S36 S43 S48 -> 
   P17 : S0 S12 S22 S27 S33 S47 S50  *)
Definition fp14_17 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P4 | P4 => P3 | P5 => P6 | P6 => P5 | P7 => P9 | P8 => P10 | P9 => P7 | P10 => P8 | P11 => P14 | P12 => P13 | P13 => P12 | P14 => P11 end.
Definition fl14_17 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L4 | L4 => L3 | L5 => L6 | L6 => L5 | L7 => L12 | L8 => L8 | L9 => L11 | L10 => L10 | L11 => L9 | L12 => L7 | L13 => L18 | L14 => L14 | L15 => L17 | L16 => L16 | L17 => L15 | L18 => L13 | L19 => L24 | L20 => L25 | L21 => L26 | L22 => L23 | L23 => L22 | L24 => L19 | L25 => L20 | L26 => L21 | L27 => L34 | L28 => L33 | L29 => L31 | L30 => L32 | L31 => L29 | L32 => L30 | L33 => L28 | L34 => L27 end.

(* P17 : S0 S12 S22 S27 S33 S47 S50 -> 
   P19 : S0 S13 S16 S28 S35 S47 S48  *)
Definition fp17_19 (p:Point) := match p with P0 => P9 | P1 => P6 | P2 => P12 | P3 => P7 | P4 => P1 | P5 => P14 | P6 => P4 | P7 => P10 | P8 => P0 | P9 => P11 | P10 => P5 | P11 => P2 | P12 => P8 | P13 => P3 | P14 => P13 end.
Definition fl17_19 (l:Line) := match l with L0 => L33 | L1 => L10 | L2 => L23 | L3 => L4 | L4 => L29 | L5 => L18 | L6 => L21 | L7 => L7 | L8 => L2 | L9 => L32 | L10 => L34 | L11 => L15 | L12 => L31 | L13 => L30 | L14 => L16 | L15 => L26 | L16 => L20 | L17 => L9 | L18 => L5 | L19 => L28 | L20 => L3 | L21 => L22 | L22 => L13 | L23 => L11 | L24 => L0 | L25 => L12 | L26 => L8 | L27 => L6 | L28 => L19 | L29 => L14 | L30 => L27 | L31 => L25 | L32 => L1 | L33 => L24 | L34 => L17 end.

(* P19 : S0 S13 S16 S28 S35 S47 S48 -> 
   P20 : S0 S13 S19 S24 S37 S46 S50  *)
Definition fp19_20 (p:Point) := match p with P0 => P5 | P1 => P13 | P2 => P7 | P3 => P8 | P4 => P14 | P5 => P6 | P6 => P0 | P7 => P12 | P8 => P10 | P9 => P2 | P10 => P4 | P11 => P3 | P12 => P1 | P13 => P9 | P14 => P11 end.
Definition fl19_20 (l:Line) := match l with L0 => L28 | L1 => L27 | L2 => L2 | L3 => L30 | L4 => L17 | L5 => L12 | L6 => L29 | L7 => L6 | L8 => L25 | L9 => L11 | L10 => L16 | L11 => L21 | L12 => L32 | L13 => L26 | L14 => L22 | L15 => L3 | L16 => L10 | L17 => L31 | L18 => L13 | L19 => L24 | L20 => L8 | L21 => L18 | L22 => L20 | L23 => L14 | L24 => L19 | L25 => L23 | L26 => L9 | L27 => L34 | L28 => L33 | L29 => L15 | L30 => L7 | L31 => L5 | L32 => L4 | L33 => L0 | L34 => L1 end.

(* P20 : S0 S13 S19 S24 S37 S46 S50 -> 
   P23 : S0 S13 S22 S26 S38 S43 S49  *)
Definition fp20_23 (p:Point) := match p with P0 => P5 | P1 => P7 | P2 => P13 | P3 => P14 | P4 => P8 | P5 => P6 | P6 => P0 | P7 => P9 | P8 => P11 | P9 => P1 | P10 => P3 | P11 => P4 | P12 => P2 | P13 => P12 | P14 => P10 end.
Definition fl20_23 (l:Line) := match l with L0 => L28 | L1 => L27 | L2 => L2 | L3 => L29 | L4 => L12 | L5 => L17 | L6 => L30 | L7 => L3 | L8 => L22 | L9 => L13 | L10 => L10 | L11 => L26 | L12 => L31 | L13 => L21 | L14 => L25 | L15 => L6 | L16 => L16 | L17 => L32 | L18 => L11 | L19 => L19 | L20 => L14 | L21 => L9 | L22 => L23 | L23 => L8 | L24 => L24 | L25 => L20 | L26 => L18 | L27 => L34 | L28 => L33 | L29 => L7 | L30 => L15 | L31 => L4 | L32 => L5 | L33 => L0 | L34 => L1 end.

(* P23 : S0 S13 S22 S26 S38 S43 S49 -> 
   P24 : S0 S15 S16 S26 S33 S46 S53  *)
Definition fp23_24 (p:Point) := match p with P0 => P9 | P1 => P12 | P2 => P6 | P3 => P2 | P4 => P8 | P5 => P13 | P6 => P3 | P7 => P5 | P8 => P11 | P9 => P10 | P10 => P0 | P11 => P4 | P12 => P14 | P13 => P7 | P14 => P1 end.
Definition fl23_24 (l:Line) := match l with L0 => L33 | L1 => L18 | L2 => L21 | L3 => L29 | L4 => L4 | L5 => L23 | L6 => L10 | L7 => L20 | L8 => L5 | L9 => L9 | L10 => L30 | L11 => L26 | L12 => L16 | L13 => L2 | L14 => L7 | L15 => L15 | L16 => L31 | L17 => L32 | L18 => L34 | L19 => L0 | L20 => L14 | L21 => L13 | L22 => L17 | L23 => L8 | L24 => L24 | L25 => L3 | L26 => L27 | L27 => L11 | L28 => L28 | L29 => L25 | L30 => L6 | L31 => L12 | L32 => L22 | L33 => L19 | L34 => L1 end.

(* P24 : S0 S15 S16 S26 S33 S46 S53 -> 
   P27 : S0 S15 S17 S27 S38 S44 S48  *)
Definition fp24_27 (p:Point) := match p with P0 => P1 | P1 => P0 | P2 => P2 | P3 => P13 | P4 => P11 | P5 => P14 | P6 => P12 | P7 => P10 | P8 => P8 | P9 => P9 | P10 => P7 | P11 => P4 | P12 => P6 | P13 => P3 | P14 => P5 end.
Definition fl24_27 (l:Line) := match l with L0 => L0 | L1 => L11 | L2 => L9 | L3 => L8 | L4 => L10 | L5 => L7 | L6 => L12 | L7 => L5 | L8 => L3 | L9 => L2 | L10 => L4 | L11 => L1 | L12 => L6 | L13 => L13 | L14 => L17 | L15 => L16 | L16 => L15 | L17 => L14 | L18 => L18 | L19 => L28 | L20 => L32 | L21 => L21 | L22 => L25 | L23 => L29 | L24 => L24 | L25 => L22 | L26 => L34 | L27 => L27 | L28 => L19 | L29 => L23 | L30 => L31 | L31 => L30 | L32 => L20 | L33 => L33 | L34 => L26 end.

(* P27 : S0 S15 S17 S27 S38 S44 S48 -> 
   P29 : S0 S15 S20 S31 S35 S40 S50  *)
Definition fp27_29 (p:Point) := match p with P0 => P0 | P1 => P2 | P2 => P1 | P3 => P3 | P4 => P4 | P5 => P6 | P6 => P5 | P7 => P12 | P8 => P11 | P9 => P13 | P10 => P14 | P11 => P8 | P12 => P7 | P13 => P9 | P14 => P10 end.
Definition fl27_29 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L5 | L4 => L6 | L5 => L3 | L6 => L4 | L7 => L17 | L8 => L14 | L9 => L13 | L10 => L16 | L11 => L18 | L12 => L15 | L13 => L9 | L14 => L8 | L15 => L12 | L16 => L10 | L17 => L7 | L18 => L11 | L19 => L19 | L20 => L22 | L21 => L21 | L22 => L20 | L23 => L25 | L24 => L24 | L25 => L23 | L26 => L26 | L27 => L34 | L28 => L33 | L29 => L32 | L30 => L31 | L31 => L30 | L32 => L29 | L33 => L28 | L34 => L27 end.

(* P29 : S0 S15 S20 S31 S35 S40 S50 -> 
   P30 : S1 S8 S18 S28 S33 S47 S53  *)
Definition fp29_30 (p:Point) := match p with P0 => P10 | P1 => P14 | P2 => P3 | P3 => P8 | P4 => P1 | P5 => P5 | P6 => P12 | P7 => P9 | P8 => P0 | P9 => P4 | P10 => P13 | P11 => P2 | P12 => P7 | P13 => P11 | P14 => P6 end.
Definition fl29_30 (l:Line) := match l with L0 => L19 | L1 => L8 | L2 => L30 | L3 => L4 | L4 => L25 | L5 => L13 | L6 => L34 | L7 => L9 | L8 => L6 | L9 => L31 | L10 => L23 | L11 => L14 | L12 => L27 | L13 => L21 | L14 => L15 | L15 => L20 | L16 => L22 | L17 => L12 | L18 => L1 | L19 => L32 | L20 => L3 | L21 => L24 | L22 => L18 | L23 => L7 | L24 => L0 | L25 => L11 | L26 => L10 | L27 => L2 | L28 => L29 | L29 => L17 | L30 => L28 | L31 => L33 | L32 => L5 | L33 => L26 | L34 => L16 end.

(* P30 : S1 S8 S18 S28 S33 S47 S53 -> 
   P33 : S1 S8 S19 S31 S37 S40 S52  *)
Definition fp30_33 (p:Point) := match p with P0 => P10 | P1 => P3 | P2 => P14 | P3 => P1 | P4 => P8 | P5 => P5 | P6 => P12 | P7 => P13 | P8 => P4 | P9 => P9 | P10 => P0 | P11 => P11 | P12 => P6 | P13 => P7 | P14 => P2 end.
Definition fl30_33 (l:Line) := match l with L0 => L19 | L1 => L8 | L2 => L30 | L3 => L25 | L4 => L4 | L5 => L34 | L6 => L13 | L7 => L20 | L8 => L1 | L9 => L15 | L10 => L21 | L11 => L22 | L12 => L12 | L13 => L6 | L14 => L14 | L15 => L9 | L16 => L31 | L17 => L27 | L18 => L23 | L19 => L0 | L20 => L7 | L21 => L10 | L22 => L11 | L23 => L18 | L24 => L24 | L25 => L3 | L26 => L32 | L27 => L17 | L28 => L28 | L29 => L29 | L30 => L2 | L31 => L16 | L32 => L26 | L33 => L33 | L34 => L5 end.

(* P33 : S1 S8 S19 S31 S37 S40 S52 -> 
   P35 : S1 S8 S22 S27 S39 S44 S49  *)
Definition fp33_35 (p:Point) := match p with P0 => P0 | P1 => P2 | P2 => P1 | P3 => P3 | P4 => P4 | P5 => P6 | P6 => P5 | P7 => P12 | P8 => P11 | P9 => P13 | P10 => P14 | P11 => P8 | P12 => P7 | P13 => P9 | P14 => P10 end.
Definition fl33_35 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L5 | L4 => L6 | L5 => L3 | L6 => L4 | L7 => L17 | L8 => L14 | L9 => L13 | L10 => L16 | L11 => L18 | L12 => L15 | L13 => L9 | L14 => L8 | L15 => L12 | L16 => L10 | L17 => L7 | L18 => L11 | L19 => L19 | L20 => L22 | L21 => L21 | L22 => L20 | L23 => L25 | L24 => L24 | L25 => L23 | L26 => L26 | L27 => L34 | L28 => L33 | L29 => L32 | L30 => L31 | L31 => L30 | L32 => L29 | L33 => L28 | L34 => L27 end.

(* P35 : S1 S8 S22 S27 S39 S44 S49 -> 
   P36 : S1 S11 S17 S24 S37 S44 S54  *)
Definition fp35_36 (p:Point) := match p with P0 => P9 | P1 => P11 | P2 => P5 | P3 => P8 | P4 => P2 | P5 => P4 | P6 => P14 | P7 => P0 | P8 => P10 | P9 => P12 | P10 => P6 | P11 => P7 | P12 => P1 | P13 => P3 | P14 => P13 end.
Definition fl35_36 (l:Line) := match l with L0 => L29 | L1 => L18 | L2 => L23 | L3 => L4 | L4 => L33 | L5 => L10 | L6 => L21 | L7 => L14 | L8 => L34 | L9 => L11 | L10 => L5 | L11 => L22 | L12 => L24 | L13 => L2 | L14 => L28 | L15 => L27 | L16 => L12 | L17 => L17 | L18 => L30 | L19 => L32 | L20 => L8 | L21 => L20 | L22 => L3 | L23 => L16 | L24 => L13 | L25 => L15 | L26 => L0 | L27 => L25 | L28 => L1 | L29 => L26 | L30 => L7 | L31 => L6 | L32 => L19 | L33 => L9 | L34 => L31 end.

(* P36 : S1 S11 S17 S24 S37 S44 S54 -> 
   P39 : S1 S11 S20 S28 S39 S40 S51  *)
Definition fp36_39 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P4 | P4 => P3 | P5 => P6 | P6 => P5 | P7 => P10 | P8 => P9 | P9 => P8 | P10 => P7 | P11 => P13 | P12 => P14 | P13 => P11 | P14 => P12 end.
Definition fl36_39 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L4 | L4 => L3 | L5 => L6 | L6 => L5 | L7 => L12 | L8 => L10 | L9 => L9 | L10 => L8 | L11 => L11 | L12 => L7 | L13 => L13 | L14 => L16 | L15 => L17 | L16 => L14 | L17 => L15 | L18 => L18 | L19 => L26 | L20 => L23 | L21 => L24 | L22 => L25 | L23 => L20 | L24 => L21 | L25 => L22 | L26 => L19 | L27 => L33 | L28 => L34 | L29 => L32 | L30 => L31 | L31 => L30 | L32 => L29 | L33 => L27 | L34 => L28 end.

(* P39 : S1 S11 S20 S28 S39 S40 S51 -> 
   P41 : S1 S11 S22 S30 S33 S43 S52  *)
Definition fp39_41 (p:Point) := match p with P0 => P12 | P1 => P4 | P2 => P7 | P3 => P1 | P4 => P14 | P5 => P6 | P6 => P9 | P7 => P10 | P8 => P5 | P9 => P13 | P10 => P2 | P11 => P8 | P12 => P3 | P13 => P11 | P14 => P0 end.
Definition fl39_41 (l:Line) := match l with L0 => L26 | L1 => L9 | L2 => L33 | L3 => L30 | L4 => L16 | L5 => L20 | L6 => L5 | L7 => L23 | L8 => L17 | L9 => L1 | L10 => L25 | L11 => L24 | L12 => L7 | L13 => L13 | L14 => L3 | L15 => L10 | L16 => L22 | L17 => L31 | L18 => L28 | L19 => L0 | L20 => L12 | L21 => L11 | L22 => L8 | L23 => L6 | L24 => L27 | L25 => L14 | L26 => L19 | L27 => L2 | L28 => L34 | L29 => L32 | L30 => L15 | L31 => L4 | L32 => L29 | L33 => L21 | L34 => L18 end.

(* P41 : S1 S11 S22 S30 S33 S43 S52 -> 
   P43 : S1 S13 S18 S30 S37 S42 S49  *)
Definition fp41_43 (p:Point) := match p with P0 => P10 | P1 => P14 | P2 => P3 | P3 => P11 | P4 => P6 | P5 => P2 | P6 => P7 | P7 => P13 | P8 => P4 | P9 => P0 | P10 => P9 | P11 => P1 | P12 => P8 | P13 => P12 | P14 => P5 end.
Definition fl41_43 (l:Line) := match l with L0 => L19 | L1 => L34 | L2 => L13 | L3 => L25 | L4 => L4 | L5 => L8 | L6 => L30 | L7 => L31 | L8 => L23 | L9 => L27 | L10 => L6 | L11 => L9 | L12 => L14 | L13 => L21 | L14 => L12 | L15 => L22 | L16 => L20 | L17 => L15 | L18 => L1 | L19 => L29 | L20 => L24 | L21 => L5 | L22 => L11 | L23 => L2 | L24 => L7 | L25 => L33 | L26 => L32 | L27 => L17 | L28 => L16 | L29 => L0 | L30 => L18 | L31 => L28 | L32 => L26 | L33 => L3 | L34 => L10 end.

(* P43 : S1 S13 S18 S30 S37 S42 S49 -> 
   P45 : S1 S13 S19 S28 S32 S43 S54  *)
Definition fp43_45 (p:Point) := match p with P0 => P1 | P1 => P2 | P2 => P0 | P3 => P9 | P4 => P7 | P5 => P8 | P6 => P10 | P7 => P12 | P8 => P14 | P9 => P13 | P10 => P11 | P11 => P6 | P12 => P4 | P13 => P3 | P14 => P5 end.
Definition fl43_45 (l:Line) := match l with L0 => L0 | L1 => L10 | L2 => L8 | L3 => L9 | L4 => L11 | L5 => L7 | L6 => L12 | L7 => L13 | L8 => L14 | L9 => L17 | L10 => L16 | L11 => L15 | L12 => L18 | L13 => L5 | L14 => L2 | L15 => L4 | L16 => L1 | L17 => L3 | L18 => L6 | L19 => L29 | L20 => L23 | L21 => L21 | L22 => L33 | L23 => L28 | L24 => L31 | L25 => L22 | L26 => L26 | L27 => L27 | L28 => L20 | L29 => L32 | L30 => L24 | L31 => L30 | L32 => L19 | L33 => L25 | L34 => L34 end.

(* P45 : S1 S13 S19 S28 S32 S43 S54 -> 
   P46 : S1 S13 S22 S24 S34 S47 S51  *)
Definition fp45_46 (p:Point) := match p with P0 => P0 | P1 => P2 | P2 => P1 | P3 => P3 | P4 => P4 | P5 => P6 | P6 => P5 | P7 => P12 | P8 => P11 | P9 => P13 | P10 => P14 | P11 => P8 | P12 => P7 | P13 => P9 | P14 => P10 end.
Definition fl45_46 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L5 | L4 => L6 | L5 => L3 | L6 => L4 | L7 => L17 | L8 => L14 | L9 => L13 | L10 => L16 | L11 => L18 | L12 => L15 | L13 => L9 | L14 => L8 | L15 => L12 | L16 => L10 | L17 => L7 | L18 => L11 | L19 => L19 | L20 => L22 | L21 => L21 | L22 => L20 | L23 => L25 | L24 => L24 | L25 => L23 | L26 => L26 | L27 => L34 | L28 => L33 | L29 => L32 | L30 => L31 | L31 => L30 | L32 => L29 | L33 => L28 | L34 => L27 end.

(* P46 : S1 S13 S22 S24 S34 S47 S51 -> 
   P49 : S1 S14 S17 S27 S32 S47 S52  *)
Definition fp46_49 (p:Point) := match p with P0 => P11 | P1 => P9 | P2 => P5 | P3 => P1 | P4 => P13 | P5 => P7 | P6 => P3 | P7 => P6 | P8 => P10 | P9 => P12 | P10 => P0 | P11 => P4 | P12 => P8 | P13 => P14 | P14 => P2 end.
Definition fl46_49 (l:Line) := match l with L0 => L29 | L1 => L11 | L2 => L22 | L3 => L34 | L4 => L5 | L5 => L24 | L6 => L14 | L7 => L21 | L8 => L4 | L9 => L18 | L10 => L33 | L11 => L23 | L12 => L10 | L13 => L2 | L14 => L17 | L15 => L12 | L16 => L27 | L17 => L28 | L18 => L30 | L19 => L0 | L20 => L8 | L21 => L9 | L22 => L7 | L23 => L16 | L24 => L25 | L25 => L6 | L26 => L32 | L27 => L13 | L28 => L31 | L29 => L26 | L30 => L3 | L31 => L15 | L32 => L19 | L33 => L20 | L34 => L1 end.

(* P49 : S1 S14 S17 S27 S32 S47 S52 -> 
   P50 : S1 S14 S19 S24 S39 S42 S53  *)
Definition fp49_50 (p:Point) := match p with P0 => P3 | P1 => P14 | P2 => P10 | P3 => P0 | P4 => P4 | P5 => P13 | P6 => P9 | P7 => P7 | P8 => P11 | P9 => P6 | P10 => P2 | P11 => P8 | P12 => P12 | P13 => P5 | P14 => P1 end.
Definition fl49_50 (l:Line) := match l with L0 => L19 | L1 => L1 | L2 => L21 | L3 => L22 | L4 => L15 | L5 => L20 | L6 => L12 | L7 => L23 | L8 => L14 | L9 => L9 | L10 => L31 | L11 => L27 | L12 => L6 | L13 => L13 | L14 => L8 | L15 => L4 | L16 => L30 | L17 => L25 | L18 => L34 | L19 => L0 | L20 => L5 | L21 => L2 | L22 => L3 | L23 => L7 | L24 => L24 | L25 => L17 | L26 => L26 | L27 => L11 | L28 => L28 | L29 => L32 | L30 => L16 | L31 => L10 | L32 => L29 | L33 => L33 | L34 => L18 end.

(* P50 : S1 S14 S19 S24 S39 S42 S53 -> 
   P53 : S1 S14 S20 S31 S34 S43 S49  *)
Definition fp50_53 (p:Point) := match p with P0 => P4 | P1 => P12 | P2 => P7 | P3 => P0 | P4 => P3 | P5 => P11 | P6 => P8 | P7 => P10 | P8 => P13 | P9 => P5 | P10 => P2 | P11 => P9 | P12 => P14 | P13 => P6 | P14 => P1 end.
Definition fl50_53 (l:Line) := match l with L0 => L26 | L1 => L1 | L2 => L24 | L3 => L25 | L4 => L17 | L5 => L23 | L6 => L7 | L7 => L20 | L8 => L16 | L9 => L9 | L10 => L30 | L11 => L33 | L12 => L5 | L13 => L13 | L14 => L10 | L15 => L3 | L16 => L31 | L17 => L22 | L18 => L28 | L19 => L0 | L20 => L6 | L21 => L2 | L22 => L4 | L23 => L12 | L24 => L21 | L25 => L15 | L26 => L19 | L27 => L11 | L28 => L34 | L29 => L29 | L30 => L14 | L31 => L8 | L32 => L32 | L33 => L27 | L34 => L18 end.

(* P53 : S1 S14 S20 S31 S34 S43 S49 -> 
   P55 : S1 S15 S17 S30 S34 S40 S53  *)
Definition fp53_55 (p:Point) := match p with P0 => P13 | P1 => P6 | P2 => P8 | P3 => P1 | P4 => P11 | P5 => P4 | P6 => P10 | P7 => P9 | P8 => P3 | P9 => P12 | P10 => P2 | P11 => P7 | P12 => P5 | P13 => P14 | P14 => P0 end.
Definition fl53_55 (l:Line) := match l with L0 => L32 | L1 => L11 | L2 => L25 | L3 => L21 | L4 => L16 | L5 => L28 | L6 => L6 | L7 => L34 | L8 => L15 | L9 => L2 | L10 => L33 | L11 => L31 | L12 => L7 | L13 => L18 | L14 => L3 | L15 => L8 | L16 => L27 | L17 => L24 | L18 => L20 | L19 => L0 | L20 => L12 | L21 => L9 | L22 => L10 | L23 => L5 | L24 => L22 | L25 => L14 | L26 => L29 | L27 => L1 | L28 => L23 | L29 => L26 | L30 => L17 | L31 => L4 | L32 => L19 | L33 => L30 | L34 => L13 end.

(* P55 : S1 S15 S17 S30 S34 S40 S53 -> 
   P57 : S1 S15 S18 S31 S32 S44 S51  *)
Definition fp55_57 (p:Point) := match p with P0 => P6 | P1 => P8 | P2 => P13 | P3 => P7 | P4 => P14 | P5 => P0 | P6 => P5 | P7 => P10 | P8 => P11 | P9 => P1 | P10 => P4 | P11 => P2 | P12 => P3 | P13 => P9 | P14 => P12 end.
Definition fl55_57 (l:Line) := match l with L0 => L32 | L1 => L31 | L2 => L2 | L3 => L34 | L4 => L7 | L5 => L15 | L6 => L33 | L7 => L27 | L8 => L24 | L9 => L20 | L10 => L8 | L11 => L18 | L12 => L3 | L13 => L25 | L14 => L16 | L15 => L28 | L16 => L21 | L17 => L6 | L18 => L11 | L19 => L26 | L20 => L22 | L21 => L10 | L22 => L13 | L23 => L9 | L24 => L14 | L25 => L23 | L26 => L19 | L27 => L5 | L28 => L4 | L29 => L0 | L30 => L1 | L31 => L30 | L32 => L29 | L33 => L12 | L34 => L17 end.

(* P57 : S1 S15 S18 S31 S32 S44 S51 -> 
   P58 : S1 S15 S20 S27 S33 S42 S54  *)
Definition fp57_58 (p:Point) := match p with P0 => P6 | P1 => P8 | P2 => P13 | P3 => P7 | P4 => P14 | P5 => P0 | P6 => P5 | P7 => P10 | P8 => P11 | P9 => P1 | P10 => P4 | P11 => P2 | P12 => P3 | P13 => P9 | P14 => P12 end.
Definition fl57_58 (l:Line) := match l with L0 => L32 | L1 => L31 | L2 => L2 | L3 => L34 | L4 => L7 | L5 => L15 | L6 => L33 | L7 => L27 | L8 => L24 | L9 => L20 | L10 => L8 | L11 => L18 | L12 => L3 | L13 => L25 | L14 => L16 | L15 => L28 | L16 => L21 | L17 => L6 | L18 => L11 | L19 => L26 | L20 => L22 | L21 => L10 | L22 => L13 | L23 => L9 | L24 => L14 | L25 => L23 | L26 => L19 | L27 => L5 | L28 => L4 | L29 => L0 | L30 => L1 | L31 => L30 | L32 => L29 | L33 => L12 | L34 => L17 end.

(* P58 : S1 S15 S20 S27 S33 S42 S54 -> 
   P60 : S2 S9 S18 S29 S38 S44 S49  *)
Definition fp58_60 (p:Point) := match p with P0 => P4 | P1 => P14 | P2 => P9 | P3 => P0 | P4 => P3 | P5 => P13 | P6 => P10 | P7 => P8 | P8 => P11 | P9 => P5 | P10 => P2 | P11 => P7 | P12 => P12 | P13 => P6 | P14 => P1 end.
Definition fl58_60 (l:Line) := match l with L0 => L23 | L1 => L1 | L2 => L25 | L3 => L24 | L4 => L17 | L5 => L26 | L6 => L7 | L7 => L19 | L8 => L14 | L9 => L9 | L10 => L27 | L11 => L31 | L12 => L6 | L13 => L18 | L14 => L10 | L15 => L4 | L16 => L33 | L17 => L21 | L18 => L29 | L19 => L0 | L20 => L5 | L21 => L2 | L22 => L3 | L23 => L12 | L24 => L22 | L25 => L15 | L26 => L20 | L27 => L11 | L28 => L32 | L29 => L28 | L30 => L16 | L31 => L8 | L32 => L34 | L33 => L30 | L34 => L13 end.

(* P60 : S2 S9 S18 S29 S38 S44 S49 -> 
   P62 : S2 S9 S19 S24 S36 S45 S54  *)
Definition fp60_62 (p:Point) := match p with P0 => P2 | P1 => P0 | P2 => P1 | P3 => P12 | P4 => P13 | P5 => P11 | P6 => P14 | P7 => P6 | P8 => P3 | P9 => P5 | P10 => P4 | P11 => P9 | P12 => P8 | P13 => P10 | P14 => P7 end.
Definition fl60_62 (l:Line) := match l with L0 => L0 | L1 => L16 | L2 => L14 | L3 => L15 | L4 => L17 | L5 => L18 | L6 => L13 | L7 => L6 | L8 => L1 | L9 => L3 | L10 => L2 | L11 => L4 | L12 => L5 | L13 => L7 | L14 => L10 | L15 => L9 | L16 => L8 | L17 => L11 | L18 => L12 | L19 => L26 | L20 => L20 | L21 => L30 | L22 => L33 | L23 => L28 | L24 => L21 | L25 => L25 | L26 => L32 | L27 => L22 | L28 => L34 | L29 => L29 | L30 => L24 | L31 => L31 | L32 => L19 | L33 => L27 | L34 => L23 end.

(* P62 : S2 S9 S19 S24 S36 S45 S54 -> 
   P65 : S2 S9 S23 S30 S35 S40 S52  *)
Definition fp62_65 (p:Point) := match p with P0 => P2 | P1 => P1 | P2 => P0 | P3 => P12 | P4 => P13 | P5 => P14 | P6 => P11 | P7 => P9 | P8 => P8 | P9 => P7 | P10 => P10 | P11 => P6 | P12 => P3 | P13 => P4 | P14 => P5 end.
Definition fl62_65 (l:Line) := match l with L0 => L0 | L1 => L16 | L2 => L14 | L3 => L18 | L4 => L13 | L5 => L15 | L6 => L17 | L7 => L11 | L8 => L8 | L9 => L12 | L10 => L10 | L11 => L7 | L12 => L9 | L13 => L4 | L14 => L2 | L15 => L5 | L16 => L1 | L17 => L6 | L18 => L3 | L19 => L30 | L20 => L20 | L21 => L26 | L22 => L33 | L23 => L28 | L24 => L32 | L25 => L25 | L26 => L21 | L27 => L27 | L28 => L23 | L29 => L31 | L30 => L19 | L31 => L29 | L32 => L24 | L33 => L22 | L34 => L34 end.

(* P65 : S2 S9 S23 S30 S35 S40 S52 -> 
   P66 : S2 S10 S16 S29 S33 S47 S52  *)
Definition fp65_66 (p:Point) := match p with P0 => P7 | P1 => P13 | P2 => P5 | P3 => P10 | P4 => P2 | P5 => P4 | P6 => P12 | P7 => P14 | P8 => P6 | P9 => P0 | P10 => P8 | P11 => P3 | P12 => P11 | P13 => P9 | P14 => P1 end.
Definition fl65_66 (l:Line) := match l with L0 => L28 | L1 => L13 | L2 => L26 | L3 => L31 | L4 => L3 | L5 => L22 | L6 => L10 | L7 => L16 | L8 => L32 | L9 => L11 | L10 => L6 | L11 => L21 | L12 => L25 | L13 => L27 | L14 => L12 | L15 => L30 | L16 => L29 | L17 => L17 | L18 => L2 | L19 => L8 | L20 => L34 | L21 => L4 | L22 => L19 | L23 => L0 | L24 => L15 | L25 => L18 | L26 => L14 | L27 => L7 | L28 => L23 | L29 => L1 | L30 => L24 | L31 => L9 | L32 => L33 | L33 => L5 | L34 => L20 end.

(* P66 : S2 S10 S16 S29 S33 S47 S52 -> 
   P69 : S2 S10 S21 S30 S36 S43 S49  *)
Definition fp66_69 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P4 | P4 => P3 | P5 => P6 | P6 => P5 | P7 => P10 | P8 => P9 | P9 => P8 | P10 => P7 | P11 => P13 | P12 => P14 | P13 => P11 | P14 => P12 end.
Definition fl66_69 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L4 | L4 => L3 | L5 => L6 | L6 => L5 | L7 => L12 | L8 => L10 | L9 => L9 | L10 => L8 | L11 => L11 | L12 => L7 | L13 => L13 | L14 => L16 | L15 => L17 | L16 => L14 | L17 => L15 | L18 => L18 | L19 => L26 | L20 => L23 | L21 => L24 | L22 => L25 | L23 => L20 | L24 => L21 | L25 => L22 | L26 => L19 | L27 => L33 | L28 => L34 | L29 => L32 | L30 => L31 | L31 => L30 | L32 => L29 | L33 => L27 | L34 => L28 end.

(* P69 : S2 S10 S21 S30 S36 S43 S49 -> 
   P70 : S2 S10 S23 S24 S39 S44 S51  *)
Definition fp69_70 (p:Point) := match p with P0 => P12 | P1 => P3 | P2 => P8 | P3 => P1 | P4 => P14 | P5 => P5 | P6 => P10 | P7 => P13 | P8 => P2 | P9 => P9 | P10 => P6 | P11 => P11 | P12 => P0 | P13 => P7 | P14 => P4 end.
Definition fl69_70 (l:Line) := match l with L0 => L20 | L1 => L9 | L2 => L30 | L3 => L16 | L4 => L33 | L5 => L5 | L6 => L26 | L7 => L19 | L8 => L15 | L9 => L1 | L10 => L21 | L11 => L22 | L12 => L12 | L13 => L32 | L14 => L24 | L15 => L8 | L16 => L3 | L17 => L27 | L18 => L18 | L19 => L7 | L20 => L0 | L21 => L10 | L22 => L11 | L23 => L23 | L24 => L14 | L25 => L31 | L26 => L6 | L27 => L17 | L28 => L28 | L29 => L29 | L30 => L2 | L31 => L25 | L32 => L13 | L33 => L4 | L34 => L34 end.

(* P70 : S2 S10 S23 S24 S39 S44 S51 -> 
   P72 : S2 S12 S18 S25 S36 S47 S51  *)
Definition fp70_72 (p:Point) := match p with P0 => P13 | P1 => P5 | P2 => P7 | P3 => P8 | P4 => P6 | P5 => P14 | P6 => P0 | P7 => P9 | P8 => P3 | P9 => P11 | P10 => P1 | P11 => P2 | P12 => P12 | P13 => P4 | P14 => P10 end.
Definition fl70_72 (l:Line) := match l with L0 => L28 | L1 => L32 | L2 => L6 | L3 => L21 | L4 => L11 | L5 => L16 | L6 => L25 | L7 => L2 | L8 => L12 | L9 => L30 | L10 => L29 | L11 => L17 | L12 => L27 | L13 => L10 | L14 => L13 | L15 => L3 | L16 => L26 | L17 => L31 | L18 => L22 | L19 => L8 | L20 => L20 | L21 => L24 | L22 => L18 | L23 => L34 | L24 => L15 | L25 => L7 | L26 => L33 | L27 => L19 | L28 => L23 | L29 => L14 | L30 => L9 | L31 => L4 | L32 => L1 | L33 => L5 | L34 => L0 end.

(* P72 : S2 S12 S18 S25 S36 S47 S51 -> 
   P75 : S2 S12 S19 S29 S39 S40 S50  *)
Definition fp72_75 (p:Point) := match p with P0 => P9 | P1 => P4 | P2 => P14 | P3 => P7 | P4 => P1 | P5 => P12 | P6 => P6 | P7 => P3 | P8 => P13 | P9 => P0 | P10 => P10 | P11 => P11 | P12 => P5 | P13 => P8 | P14 => P2 end.
Definition fl72_75 (l:Line) := match l with L0 => L23 | L1 => L10 | L2 => L33 | L3 => L21 | L4 => L4 | L5 => L29 | L6 => L18 | L7 => L7 | L8 => L25 | L9 => L17 | L10 => L1 | L11 => L24 | L12 => L26 | L13 => L19 | L14 => L14 | L15 => L31 | L16 => L27 | L17 => L9 | L18 => L6 | L19 => L13 | L20 => L28 | L21 => L3 | L22 => L22 | L23 => L0 | L24 => L11 | L25 => L8 | L26 => L12 | L27 => L16 | L28 => L20 | L29 => L5 | L30 => L30 | L31 => L15 | L32 => L32 | L33 => L2 | L34 => L34 end.

(* P75 : S2 S12 S19 S29 S39 S40 S50 -> 
   P76 : S2 S12 S23 S26 S33 S43 S54  *)
Definition fp75_76 (p:Point) := match p with P0 => P14 | P1 => P4 | P2 => P9 | P3 => P11 | P4 => P2 | P5 => P8 | P6 => P5 | P7 => P3 | P8 => P10 | P9 => P0 | P10 => P13 | P11 => P7 | P12 => P6 | P13 => P12 | P14 => P1 end.
Definition fl75_76 (l:Line) := match l with L0 => L23 | L1 => L14 | L2 => L27 | L3 => L19 | L4 => L6 | L5 => L31 | L6 => L9 | L7 => L17 | L8 => L25 | L9 => L7 | L10 => L1 | L11 => L26 | L12 => L24 | L13 => L21 | L14 => L10 | L15 => L29 | L16 => L33 | L17 => L18 | L18 => L4 | L19 => L11 | L20 => L34 | L21 => L5 | L22 => L22 | L23 => L0 | L24 => L13 | L25 => L16 | L26 => L15 | L27 => L8 | L28 => L20 | L29 => L3 | L30 => L32 | L31 => L12 | L32 => L30 | L33 => L2 | L34 => L28 end.

(* P76 : S2 S12 S23 S26 S33 S43 S54 -> 
   P79 : S2 S14 S16 S26 S39 S45 S49  *)
Definition fp76_79 (p:Point) := match p with P0 => P4 | P1 => P9 | P2 => P14 | P3 => P0 | P4 => P3 | P5 => P10 | P6 => P13 | P7 => P6 | P8 => P1 | P9 => P12 | P10 => P7 | P11 => P5 | P12 => P2 | P13 => P11 | P14 => P8 end.
Definition fl76_79 (l:Line) := match l with L0 => L23 | L1 => L1 | L2 => L25 | L3 => L7 | L4 => L26 | L5 => L17 | L6 => L24 | L7 => L21 | L8 => L10 | L9 => L18 | L10 => L33 | L11 => L29 | L12 => L4 | L13 => L31 | L14 => L27 | L15 => L6 | L16 => L14 | L17 => L19 | L18 => L9 | L19 => L3 | L20 => L0 | L21 => L5 | L22 => L2 | L23 => L20 | L24 => L12 | L25 => L22 | L26 => L15 | L27 => L8 | L28 => L34 | L29 => L30 | L30 => L13 | L31 => L32 | L32 => L11 | L33 => L16 | L34 => L28 end.

(* P79 : S2 S14 S16 S26 S39 S45 S49 -> 
   P81 : S2 S14 S19 S25 S38 S43 S52  *)
Definition fp79_81 (p:Point) := match p with P0 => P6 | P1 => P10 | P2 => P11 | P3 => P9 | P4 => P12 | P5 => P0 | P6 => P5 | P7 => P1 | P8 => P4 | P9 => P8 | P10 => P13 | P11 => P7 | P12 => P14 | P13 => P2 | P14 => P3 end.
Definition fl79_81 (l:Line) := match l with L0 => L34 | L1 => L33 | L2 => L2 | L3 => L7 | L4 => L32 | L5 => L31 | L6 => L15 | L7 => L30 | L8 => L25 | L9 => L19 | L10 => L8 | L11 => L13 | L12 => L4 | L13 => L11 | L14 => L22 | L15 => L29 | L16 => L14 | L17 => L5 | L18 => L24 | L19 => L21 | L20 => L23 | L21 => L18 | L22 => L10 | L23 => L20 | L24 => L26 | L25 => L16 | L26 => L9 | L27 => L1 | L28 => L0 | L29 => L3 | L30 => L6 | L31 => L12 | L32 => L17 | L33 => L27 | L34 => L28 end.

(* P81 : S2 S14 S19 S25 S38 S43 S52 -> 
   P82 : S2 S14 S21 S24 S35 S47 S50  *)
Definition fp81_82 (p:Point) := match p with P0 => P6 | P1 => P10 | P2 => P11 | P3 => P9 | P4 => P12 | P5 => P0 | P6 => P5 | P7 => P1 | P8 => P4 | P9 => P8 | P10 => P13 | P11 => P7 | P12 => P14 | P13 => P2 | P14 => P3 end.
Definition fl81_82 (l:Line) := match l with L0 => L34 | L1 => L33 | L2 => L2 | L3 => L7 | L4 => L32 | L5 => L31 | L6 => L15 | L7 => L30 | L8 => L25 | L9 => L19 | L10 => L8 | L11 => L13 | L12 => L4 | L13 => L11 | L14 => L22 | L15 => L29 | L16 => L14 | L17 => L5 | L18 => L24 | L19 => L21 | L20 => L23 | L21 => L18 | L22 => L10 | L23 => L20 | L24 => L26 | L25 => L16 | L26 => L9 | L27 => L1 | L28 => L0 | L29 => L3 | L30 => L6 | L31 => L12 | L32 => L17 | L33 => L27 | L34 => L28 end.

(* P82 : S2 S14 S21 S24 S35 S47 S50 -> 
   P84 : S2 S15 S16 S25 S35 S44 S54  *)
Definition fp82_84 (p:Point) := match p with P0 => P14 | P1 => P4 | P2 => P9 | P3 => P6 | P4 => P7 | P5 => P1 | P6 => P12 | P7 => P2 | P8 => P11 | P9 => P5 | P10 => P8 | P11 => P3 | P12 => P10 | P13 => P0 | P14 => P13 end.
Definition fl82_84 (l:Line) := match l with L0 => L23 | L1 => L31 | L2 => L9 | L3 => L14 | L4 => L27 | L5 => L19 | L6 => L6 | L7 => L26 | L8 => L24 | L9 => L25 | L10 => L17 | L11 => L1 | L12 => L7 | L13 => L18 | L14 => L21 | L15 => L33 | L16 => L4 | L17 => L10 | L18 => L29 | L19 => L32 | L20 => L34 | L21 => L2 | L22 => L15 | L23 => L28 | L24 => L22 | L25 => L3 | L26 => L13 | L27 => L11 | L28 => L0 | L29 => L12 | L30 => L8 | L31 => L16 | L32 => L5 | L33 => L30 | L34 => L20 end.

(* P84 : S2 S15 S16 S25 S35 S44 S54 -> 
   P87 : S2 S15 S18 S30 S33 S45 S50  *)
Definition fp84_87 (p:Point) := match p with P0 => P4 | P1 => P14 | P2 => P9 | P3 => P0 | P4 => P3 | P5 => P13 | P6 => P10 | P7 => P5 | P8 => P2 | P9 => P8 | P10 => P11 | P11 => P6 | P12 => P1 | P13 => P7 | P14 => P12 end.
Definition fl84_87 (l:Line) := match l with L0 => L23 | L1 => L1 | L2 => L25 | L3 => L17 | L4 => L24 | L5 => L7 | L6 => L26 | L7 => L19 | L8 => L14 | L9 => L9 | L10 => L27 | L11 => L31 | L12 => L6 | L13 => L29 | L14 => L33 | L15 => L4 | L16 => L10 | L17 => L21 | L18 => L18 | L19 => L5 | L20 => L0 | L21 => L3 | L22 => L2 | L23 => L20 | L24 => L15 | L25 => L22 | L26 => L12 | L27 => L16 | L28 => L28 | L29 => L32 | L30 => L11 | L31 => L30 | L32 => L13 | L33 => L8 | L34 => L34 end.

(* P87 : S2 S15 S18 S30 S33 S45 S50 -> 
   P88 : S2 S15 S21 S26 S38 S40 S51  *)
Definition fp87_88 (p:Point) := match p with P0 => P4 | P1 => P14 | P2 => P9 | P3 => P3 | P4 => P0 | P5 => P10 | P6 => P13 | P7 => P11 | P8 => P8 | P9 => P2 | P10 => P5 | P11 => P7 | P12 => P12 | P13 => P6 | P14 => P1 end.
Definition fl87_88 (l:Line) := match l with L0 => L23 | L1 => L1 | L2 => L25 | L3 => L24 | L4 => L17 | L5 => L26 | L6 => L7 | L7 => L6 | L8 => L27 | L9 => L9 | L10 => L14 | L11 => L31 | L12 => L19 | L13 => L29 | L14 => L10 | L15 => L21 | L16 => L33 | L17 => L4 | L18 => L18 | L19 => L12 | L20 => L20 | L21 => L15 | L22 => L22 | L23 => L0 | L24 => L3 | L25 => L2 | L26 => L5 | L27 => L8 | L28 => L34 | L29 => L13 | L30 => L30 | L31 => L11 | L32 => L32 | L33 => L16 | L34 => L28 end.

(* P88 : S2 S15 S21 S26 S38 S40 S51 -> 
   P91 : S3 S8 S18 S31 S36 S45 S49  *)
Definition fp88_91 (p:Point) := match p with P0 => P0 | P1 => P2 | P2 => P1 | P3 => P3 | P4 => P4 | P5 => P6 | P6 => P5 | P7 => P7 | P8 => P8 | P9 => P10 | P10 => P9 | P11 => P11 | P12 => P12 | P13 => P14 | P14 => P13 end.
Definition fl88_91 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L3 | L4 => L4 | L5 => L5 | L6 => L6 | L7 => L17 | L8 => L18 | L9 => L16 | L10 => L13 | L11 => L14 | L12 => L15 | L13 => L10 | L14 => L11 | L15 => L12 | L16 => L9 | L17 => L7 | L18 => L8 | L19 => L21 | L20 => L20 | L21 => L19 | L22 => L22 | L23 => L25 | L24 => L24 | L25 => L23 | L26 => L26 | L27 => L32 | L28 => L31 | L29 => L34 | L30 => L33 | L31 => L28 | L32 => L27 | L33 => L30 | L34 => L29 end.

(* P91 : S3 S8 S18 S31 S36 S45 S49 -> 
   P93 : S3 S8 S21 S28 S35 S40 S55  *)
Definition fp91_93 (p:Point) := match p with P0 => P4 | P1 => P10 | P2 => P13 | P3 => P3 | P4 => P0 | P5 => P14 | P6 => P9 | P7 => P11 | P8 => P8 | P9 => P6 | P10 => P1 | P11 => P7 | P12 => P12 | P13 => P2 | P14 => P5 end.
Definition fl91_93 (l:Line) := match l with L0 => L25 | L1 => L1 | L2 => L23 | L3 => L24 | L4 => L7 | L5 => L26 | L6 => L17 | L7 => L4 | L8 => L8 | L9 => L30 | L10 => L34 | L11 => L13 | L12 => L19 | L13 => L11 | L14 => L28 | L15 => L21 | L16 => L16 | L17 => L6 | L18 => L32 | L19 => L12 | L20 => L20 | L21 => L15 | L22 => L22 | L23 => L2 | L24 => L3 | L25 => L0 | L26 => L5 | L27 => L27 | L28 => L14 | L29 => L31 | L30 => L9 | L31 => L29 | L32 => L18 | L33 => L33 | L34 => L10 end.

(* P93 : S3 S8 S21 S28 S35 S40 S55 -> 
   P94 : S3 S8 S23 S27 S33 S46 S52  *)
Definition fp93_94 (p:Point) := match p with P0 => P3 | P1 => P8 | P2 => P12 | P3 => P4 | P4 => P0 | P5 => P11 | P6 => P7 | P7 => P14 | P8 => P10 | P9 => P5 | P10 => P1 | P11 => P9 | P12 => P13 | P13 => P2 | P14 => P6 end.
Definition fl93_94 (l:Line) := match l with L0 => L20 | L1 => L1 | L2 => L22 | L3 => L19 | L4 => L12 | L5 => L21 | L6 => L15 | L7 => L3 | L8 => L8 | L9 => L32 | L10 => L27 | L11 => L18 | L12 => L24 | L13 => L9 | L14 => L33 | L15 => L26 | L16 => L16 | L17 => L5 | L18 => L30 | L19 => L7 | L20 => L25 | L21 => L17 | L22 => L23 | L23 => L2 | L24 => L4 | L25 => L0 | L26 => L6 | L27 => L34 | L28 => L14 | L29 => L29 | L30 => L11 | L31 => L31 | L32 => L13 | L33 => L28 | L34 => L10 end.

(* P94 : S3 S8 S23 S27 S33 S46 S52 -> 
   P96 : S3 S11 S16 S28 S33 S45 S54  *)
Definition fp94_96 (p:Point) := match p with P0 => P10 | P1 => P13 | P2 => P4 | P3 => P6 | P4 => P11 | P5 => P8 | P6 => P1 | P7 => P2 | P8 => P7 | P9 => P12 | P10 => P5 | P11 => P3 | P12 => P14 | P13 => P9 | P14 => P0 end.
Definition fl94_96 (l:Line) := match l with L0 => L25 | L1 => L34 | L2 => L8 | L3 => L13 | L4 => L30 | L5 => L19 | L6 => L4 | L7 => L11 | L8 => L28 | L9 => L6 | L10 => L16 | L11 => L21 | L12 => L32 | L13 => L17 | L14 => L1 | L15 => L7 | L16 => L23 | L17 => L24 | L18 => L26 | L19 => L2 | L20 => L31 | L21 => L33 | L22 => L15 | L23 => L5 | L24 => L22 | L25 => L29 | L26 => L14 | L27 => L3 | L28 => L18 | L29 => L20 | L30 => L27 | L31 => L0 | L32 => L10 | L33 => L9 | L34 => L12 end.

(* P96 : S3 S11 S16 S28 S33 S45 S54 -> 
   P99 : S3 S11 S17 S29 S38 S40 S52  *)
Definition fp96_99 (p:Point) := match p with P0 => P1 | P1 => P0 | P2 => P2 | P3 => P12 | P4 => P14 | P5 => P11 | P6 => P13 | P7 => P10 | P8 => P8 | P9 => P9 | P10 => P7 | P11 => P5 | P12 => P3 | P13 => P6 | P14 => P4 end.
Definition fl96_99 (l:Line) := match l with L0 => L0 | L1 => L9 | L2 => L11 | L3 => L8 | L4 => L10 | L5 => L12 | L6 => L7 | L7 => L6 | L8 => L3 | L9 => L1 | L10 => L4 | L11 => L2 | L12 => L5 | L13 => L13 | L14 => L17 | L15 => L16 | L16 => L15 | L17 => L14 | L18 => L18 | L19 => L26 | L20 => L20 | L21 => L33 | L22 => L30 | L23 => L23 | L24 => L27 | L25 => L31 | L26 => L19 | L27 => L24 | L28 => L34 | L29 => L29 | L30 => L22 | L31 => L25 | L32 => L32 | L33 => L21 | L34 => L28 end.

(* P99 : S3 S11 S17 S29 S38 S40 S52 -> 
   P100 : S3 S11 S21 S24 S36 S46 S51  *)
Definition fp99_100 (p:Point) := match p with P0 => P2 | P1 => P0 | P2 => P1 | P3 => P8 | P4 => P9 | P5 => P7 | P6 => P10 | P7 => P13 | P8 => P12 | P9 => P14 | P10 => P11 | P11 => P6 | P12 => P3 | P13 => P5 | P14 => P4 end.
Definition fl99_100 (l:Line) := match l with L0 => L0 | L1 => L18 | L2 => L13 | L3 => L16 | L4 => L14 | L5 => L15 | L6 => L17 | L7 => L4 | L8 => L5 | L9 => L1 | L10 => L6 | L11 => L2 | L12 => L3 | L13 => L11 | L14 => L7 | L15 => L8 | L16 => L12 | L17 => L10 | L18 => L9 | L19 => L24 | L20 => L20 | L21 => L27 | L22 => L32 | L23 => L23 | L24 => L33 | L25 => L29 | L26 => L21 | L27 => L26 | L28 => L28 | L29 => L31 | L30 => L22 | L31 => L25 | L32 => L30 | L33 => L19 | L34 => L34 end.

(* P100 : S3 S11 S21 S24 S36 S46 S51 -> 
   P102 : S3 S12 S17 S27 S36 S41 S54  *)
Definition fp100_102 (p:Point) := match p with P0 => P12 | P1 => P8 | P2 => P3 | P3 => P10 | P4 => P5 | P5 => P1 | P6 => P14 | P7 => P7 | P8 => P4 | P9 => P0 | P10 => P11 | P11 => P2 | P12 => P13 | P13 => P9 | P14 => P6 end.
Definition fl100_102 (l:Line) := match l with L0 => L20 | L1 => L30 | L2 => L9 | L3 => L26 | L4 => L5 | L5 => L16 | L6 => L33 | L7 => L27 | L8 => L24 | L9 => L32 | L10 => L3 | L11 => L18 | L12 => L8 | L13 => L22 | L14 => L15 | L15 => L19 | L16 => L21 | L17 => L12 | L18 => L1 | L19 => L34 | L20 => L25 | L21 => L4 | L22 => L13 | L23 => L2 | L24 => L17 | L25 => L29 | L26 => L28 | L27 => L7 | L28 => L10 | L29 => L0 | L30 => L11 | L31 => L31 | L32 => L23 | L33 => L6 | L34 => L14 end.

(* P102 : S3 S12 S17 S27 S36 S41 S54 -> 
   P104 : S3 S12 S18 S29 S33 S42 S55  *)
Definition fp102_104 (p:Point) := match p with P0 => P5 | P1 => P11 | P2 => P9 | P3 => P10 | P4 => P12 | P5 => P6 | P6 => P0 | P7 => P2 | P8 => P4 | P9 => P14 | P10 => P8 | P11 => P7 | P12 => P13 | P13 => P3 | P14 => P1 end.
Definition fl102_104 (l:Line) := match l with L0 => L29 | L1 => L30 | L2 => L2 | L3 => L17 | L4 => L27 | L5 => L28 | L6 => L12 | L7 => L5 | L8 => L24 | L9 => L11 | L10 => L14 | L11 => L22 | L12 => L34 | L13 => L18 | L14 => L10 | L15 => L4 | L16 => L21 | L17 => L33 | L18 => L23 | L19 => L8 | L20 => L25 | L21 => L19 | L22 => L13 | L23 => L9 | L24 => L26 | L25 => L20 | L26 => L16 | L27 => L7 | L28 => L15 | L29 => L31 | L30 => L32 | L31 => L0 | L32 => L1 | L33 => L6 | L34 => L3 end.

(* P104 : S3 S12 S18 S29 S33 S42 S55 -> 
   P107 : S3 S12 S23 S31 S34 S40 S51  *)
Definition fp104_107 (p:Point) := match p with P0 => P5 | P1 => P9 | P2 => P11 | P3 => P12 | P4 => P10 | P5 => P6 | P6 => P0 | P7 => P1 | P8 => P3 | P9 => P7 | P10 => P13 | P11 => P14 | P12 => P8 | P13 => P4 | P14 => P2 end.
Definition fl104_107 (l:Line) := match l with L0 => L29 | L1 => L30 | L2 => L2 | L3 => L12 | L4 => L28 | L5 => L27 | L6 => L17 | L7 => L4 | L8 => L21 | L9 => L18 | L10 => L10 | L11 => L23 | L12 => L33 | L13 => L11 | L14 => L14 | L15 => L5 | L16 => L24 | L17 => L34 | L18 => L22 | L19 => L16 | L20 => L20 | L21 => L26 | L22 => L9 | L23 => L13 | L24 => L19 | L25 => L25 | L26 => L8 | L27 => L15 | L28 => L7 | L29 => L31 | L30 => L32 | L31 => L0 | L32 => L1 | L33 => L3 | L34 => L6 end.

(* P107 : S3 S12 S23 S31 S34 S40 S51 -> 
   P109 : S3 S13 S16 S29 S34 S46 S49  *)
Definition fp107_109 (p:Point) := match p with P0 => P8 | P1 => P3 | P2 => P12 | P3 => P14 | P4 => P5 | P5 => P10 | P6 => P1 | P7 => P0 | P8 => P7 | P9 => P4 | P10 => P11 | P11 => P13 | P12 => P6 | P13 => P9 | P14 => P2 end.
Definition fl107_109 (l:Line) := match l with L0 => L20 | L1 => L27 | L2 => L8 | L3 => L3 | L4 => L24 | L5 => L32 | L6 => L18 | L7 => L12 | L8 => L22 | L9 => L15 | L10 => L1 | L11 => L21 | L12 => L19 | L13 => L5 | L14 => L16 | L15 => L9 | L16 => L33 | L17 => L30 | L18 => L26 | L19 => L14 | L20 => L31 | L21 => L23 | L22 => L6 | L23 => L17 | L24 => L28 | L25 => L29 | L26 => L2 | L27 => L13 | L28 => L4 | L29 => L25 | L30 => L34 | L31 => L0 | L32 => L10 | L33 => L7 | L34 => L11 end.

(* P109 : S3 S13 S16 S29 S34 S46 S49 -> 
   P110 : S3 S13 S18 S28 S38 S41 S51  *)
Definition fp109_110 (p:Point) := match p with P0 => P12 | P1 => P8 | P2 => P3 | P3 => P2 | P4 => P13 | P5 => P9 | P6 => P6 | P7 => P14 | P8 => P1 | P9 => P5 | P10 => P10 | P11 => P11 | P12 => P0 | P13 => P4 | P14 => P7 end.
Definition fl109_110 (l:Line) := match l with L0 => L20 | L1 => L16 | L2 => L33 | L3 => L9 | L4 => L30 | L5 => L5 | L6 => L26 | L7 => L32 | L8 => L8 | L9 => L3 | L10 => L27 | L11 => L24 | L12 => L18 | L13 => L19 | L14 => L22 | L15 => L15 | L16 => L1 | L17 => L21 | L18 => L12 | L19 => L13 | L20 => L0 | L21 => L17 | L22 => L14 | L23 => L28 | L24 => L11 | L25 => L25 | L26 => L6 | L27 => L10 | L28 => L23 | L29 => L29 | L30 => L4 | L31 => L31 | L32 => L7 | L33 => L2 | L34 => L34 end.

(* P110 : S3 S13 S18 S28 S38 S41 S51 -> 
   P113 : S3 S13 S23 S24 S35 S42 S54  *)
Definition fp110_113 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P4 | P4 => P3 | P5 => P6 | P6 => P5 | P7 => P9 | P8 => P10 | P9 => P7 | P10 => P8 | P11 => P14 | P12 => P13 | P13 => P12 | P14 => P11 end.
Definition fl110_113 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L4 | L4 => L3 | L5 => L6 | L6 => L5 | L7 => L12 | L8 => L8 | L9 => L11 | L10 => L10 | L11 => L9 | L12 => L7 | L13 => L18 | L14 => L14 | L15 => L17 | L16 => L16 | L17 => L15 | L18 => L13 | L19 => L24 | L20 => L25 | L21 => L26 | L22 => L23 | L23 => L22 | L24 => L19 | L25 => L20 | L26 => L21 | L27 => L34 | L28 => L33 | L29 => L31 | L30 => L32 | L31 => L29 | L32 => L30 | L33 => L28 | L34 => L27 end.

(* P113 : S3 S13 S23 S24 S35 S42 S54 -> 
   P115 : S3 S14 S16 S31 S35 S41 S52  *)
Definition fp113_115 (p:Point) := match p with P0 => P8 | P1 => P3 | P2 => P12 | P3 => P14 | P4 => P5 | P5 => P10 | P6 => P1 | P7 => P0 | P8 => P7 | P9 => P4 | P10 => P11 | P11 => P13 | P12 => P6 | P13 => P9 | P14 => P2 end.
Definition fl113_115 (l:Line) := match l with L0 => L20 | L1 => L27 | L2 => L8 | L3 => L3 | L4 => L24 | L5 => L32 | L6 => L18 | L7 => L12 | L8 => L22 | L9 => L15 | L10 => L1 | L11 => L21 | L12 => L19 | L13 => L5 | L14 => L16 | L15 => L9 | L16 => L33 | L17 => L30 | L18 => L26 | L19 => L14 | L20 => L31 | L21 => L23 | L22 => L6 | L23 => L17 | L24 => L28 | L25 => L29 | L26 => L2 | L27 => L13 | L28 => L4 | L29 => L25 | L30 => L34 | L31 => L0 | L32 => L10 | L33 => L7 | L34 => L11 end.

(* P115 : S3 S14 S16 S31 S35 S41 S52 -> 
   P116 : S3 S14 S17 S24 S34 S45 S55  *)
Definition fp115_116 (p:Point) := match p with P0 => P10 | P1 => P4 | P2 => P13 | P3 => P7 | P4 => P2 | P5 => P12 | P6 => P5 | P7 => P11 | P8 => P6 | P9 => P8 | P10 => P1 | P11 => P3 | P12 => P14 | P13 => P0 | P14 => P9 end.
Definition fl115_116 (l:Line) := match l with L0 => L25 | L1 => L13 | L2 => L30 | L3 => L34 | L4 => L8 | L5 => L19 | L6 => L4 | L7 => L17 | L8 => L7 | L9 => L23 | L10 => L24 | L11 => L1 | L12 => L26 | L13 => L11 | L14 => L21 | L15 => L28 | L16 => L6 | L17 => L16 | L18 => L32 | L19 => L10 | L20 => L31 | L21 => L3 | L22 => L22 | L23 => L18 | L24 => L15 | L25 => L0 | L26 => L14 | L27 => L33 | L28 => L5 | L29 => L20 | L30 => L9 | L31 => L29 | L32 => L2 | L33 => L27 | L34 => L12 end.

(* P116 : S3 S14 S17 S24 S34 S45 S55 -> 
   P119 : S3 S14 S21 S27 S38 S42 S49  *)
Definition fp116_119 (p:Point) := match p with P0 => P10 | P1 => P13 | P2 => P4 | P3 => P7 | P4 => P2 | P5 => P5 | P6 => P12 | P7 => P3 | P8 => P14 | P9 => P9 | P10 => P0 | P11 => P11 | P12 => P6 | P13 => P1 | P14 => P8 end.
Definition fl116_119 (l:Line) := match l with L0 => L25 | L1 => L13 | L2 => L30 | L3 => L19 | L4 => L4 | L5 => L34 | L6 => L8 | L7 => L16 | L8 => L6 | L9 => L32 | L10 => L21 | L11 => L11 | L12 => L28 | L13 => L1 | L14 => L24 | L15 => L26 | L16 => L7 | L17 => L17 | L18 => L23 | L19 => L3 | L20 => L31 | L21 => L10 | L22 => L22 | L23 => L18 | L24 => L14 | L25 => L0 | L26 => L15 | L27 => L27 | L28 => L12 | L29 => L29 | L30 => L2 | L31 => L20 | L32 => L9 | L33 => L33 | L34 => L5 end.

(* P119 : S3 S14 S21 S27 S38 S42 S49 -> 
   P120 : S4 S8 S19 S25 S36 S46 S53  *)
Definition fp119_120 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P14 | P8 => P13 | P9 => P12 | P10 => P11 | P11 => P10 | P12 => P9 | P13 => P8 | P14 => P7 end.
Definition fl119_120 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L6 | L4 => L5 | L5 => L4 | L6 => L3 | L7 => L7 | L8 => L11 | L9 => L10 | L10 => L9 | L11 => L8 | L12 => L12 | L13 => L14 | L14 => L13 | L15 => L15 | L16 => L18 | L17 => L17 | L18 => L16 | L19 => L22 | L20 => L21 | L21 => L20 | L22 => L19 | L23 => L26 | L24 => L25 | L25 => L24 | L26 => L23 | L27 => L28 | L28 => L27 | L29 => L30 | L30 => L29 | L31 => L31 | L32 => L32 | L33 => L33 | L34 => L34 end.

(* P120 : S4 S8 S19 S25 S36 S46 S53 -> 
   P123 : S4 S8 S22 S26 S33 S45 S55  *)
Definition fp120_123 (p:Point) := match p with P0 => P0 | P1 => P2 | P2 => P1 | P3 => P3 | P4 => P4 | P5 => P6 | P6 => P5 | P7 => P12 | P8 => P11 | P9 => P13 | P10 => P14 | P11 => P8 | P12 => P7 | P13 => P9 | P14 => P10 end.
Definition fl120_123 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L5 | L4 => L6 | L5 => L3 | L6 => L4 | L7 => L17 | L8 => L14 | L9 => L13 | L10 => L16 | L11 => L18 | L12 => L15 | L13 => L9 | L14 => L8 | L15 => L12 | L16 => L10 | L17 => L7 | L18 => L11 | L19 => L19 | L20 => L22 | L21 => L21 | L22 => L20 | L23 => L25 | L24 => L24 | L25 => L23 | L26 => L26 | L27 => L34 | L28 => L33 | L29 => L32 | L30 => L31 | L31 => L30 | L32 => L29 | L33 => L28 | L34 => L27 end.

(* P123 : S4 S8 S22 S26 S33 S45 S55 -> 
   P125 : S4 S8 S23 S31 S35 S44 S48  *)
Definition fp123_125 (p:Point) := match p with P0 => P2 | P1 => P0 | P2 => P1 | P3 => P14 | P4 => P11 | P5 => P13 | P6 => P12 | P7 => P5 | P8 => P4 | P9 => P6 | P10 => P3 | P11 => P8 | P12 => P9 | P13 => P7 | P14 => P10 end.
Definition fl123_125 (l:Line) := match l with L0 => L0 | L1 => L14 | L2 => L16 | L3 => L17 | L4 => L15 | L5 => L18 | L6 => L13 | L7 => L5 | L8 => L1 | L9 => L4 | L10 => L2 | L11 => L3 | L12 => L6 | L13 => L12 | L14 => L8 | L15 => L9 | L16 => L10 | L17 => L11 | L18 => L7 | L19 => L19 | L20 => L23 | L21 => L31 | L22 => L27 | L23 => L34 | L24 => L24 | L25 => L22 | L26 => L29 | L27 => L25 | L28 => L28 | L29 => L32 | L30 => L21 | L31 => L30 | L32 => L26 | L33 => L33 | L34 => L20 end.

(* P125 : S4 S8 S23 S31 S35 S44 S48 -> 
   P126 : S4 S10 S17 S29 S32 S44 S55  *)
Definition fp125_126 (p:Point) := match p with P0 => P13 | P1 => P9 | P2 => P3 | P3 => P6 | P4 => P8 | P5 => P12 | P6 => P2 | P7 => P1 | P8 => P11 | P9 => P7 | P10 => P5 | P11 => P4 | P12 => P10 | P13 => P14 | P14 => P0 end.
Definition fl125_126 (l:Line) := match l with L0 => L21 | L1 => L32 | L2 => L16 | L3 => L11 | L4 => L28 | L5 => L25 | L6 => L6 | L7 => L18 | L8 => L29 | L9 => L4 | L10 => L10 | L11 => L23 | L12 => L33 | L13 => L12 | L14 => L1 | L15 => L15 | L16 => L19 | L17 => L20 | L18 => L22 | L19 => L2 | L20 => L34 | L21 => L31 | L22 => L7 | L23 => L3 | L24 => L24 | L25 => L27 | L26 => L8 | L27 => L5 | L28 => L9 | L29 => L26 | L30 => L30 | L31 => L0 | L32 => L14 | L33 => L13 | L34 => L17 end.

(* P126 : S4 S10 S17 S29 S32 S44 S55 -> 
   P129 : S4 S10 S20 S31 S36 S41 S51  *)
Definition fp126_129 (p:Point) := match p with P0 => P6 | P1 => P14 | P2 => P7 | P3 => P13 | P4 => P8 | P5 => P0 | P6 => P5 | P7 => P10 | P8 => P11 | P9 => P3 | P10 => P2 | P11 => P4 | P12 => P1 | P13 => P9 | P14 => P12 end.
Definition fl126_129 (l:Line) := match l with L0 => L31 | L1 => L32 | L2 => L2 | L3 => L34 | L4 => L15 | L5 => L7 | L6 => L33 | L7 => L27 | L8 => L14 | L9 => L9 | L10 => L19 | L11 => L23 | L12 => L6 | L13 => L13 | L14 => L26 | L15 => L28 | L16 => L10 | L17 => L3 | L18 => L22 | L19 => L16 | L20 => L11 | L21 => L21 | L22 => L25 | L23 => L20 | L24 => L24 | L25 => L18 | L26 => L8 | L27 => L5 | L28 => L4 | L29 => L1 | L30 => L0 | L31 => L30 | L32 => L29 | L33 => L12 | L34 => L17 end.

(* P129 : S4 S10 S20 S31 S36 S41 S51 -> 
   P130 : S4 S10 S23 S30 S33 S42 S53  *)
Definition fp129_130 (p:Point) := match p with P0 => P6 | P1 => P7 | P2 => P14 | P3 => P8 | P4 => P13 | P5 => P0 | P6 => P5 | P7 => P12 | P8 => P9 | P9 => P4 | P10 => P1 | P11 => P3 | P12 => P2 | P13 => P11 | P14 => P10 end.
Definition fl129_130 (l:Line) := match l with L0 => L31 | L1 => L32 | L2 => L2 | L3 => L33 | L4 => L7 | L5 => L15 | L6 => L34 | L7 => L28 | L8 => L10 | L9 => L13 | L10 => L26 | L11 => L22 | L12 => L3 | L13 => L9 | L14 => L19 | L15 => L27 | L16 => L14 | L17 => L6 | L18 => L23 | L19 => L8 | L20 => L18 | L21 => L24 | L22 => L20 | L23 => L25 | L24 => L21 | L25 => L11 | L26 => L16 | L27 => L4 | L28 => L5 | L29 => L1 | L30 => L0 | L31 => L30 | L32 => L29 | L33 => L17 | L34 => L12 end.

(* P130 : S4 S10 S23 S30 S33 S42 S53 -> 
   P133 : S4 S11 S17 S30 S36 S45 S48  *)
Definition fp130_133 (p:Point) := match p with P0 => P11 | P1 => P8 | P2 => P4 | P3 => P10 | P4 => P6 | P5 => P1 | P6 => P13 | P7 => P3 | P8 => P7 | P9 => P12 | P10 => P0 | P11 => P14 | P12 => P2 | P13 => P5 | P14 => P9 end.
Definition fl130_133 (l:Line) := match l with L0 => L24 | L1 => L34 | L2 => L11 | L3 => L22 | L4 => L5 | L5 => L14 | L6 => L29 | L7 => L32 | L8 => L3 | L9 => L18 | L10 => L20 | L11 => L27 | L12 => L8 | L13 => L1 | L14 => L23 | L15 => L25 | L16 => L17 | L17 => L7 | L18 => L26 | L19 => L4 | L20 => L13 | L21 => L30 | L22 => L19 | L23 => L33 | L24 => L31 | L25 => L2 | L26 => L15 | L27 => L10 | L28 => L12 | L29 => L9 | L30 => L0 | L31 => L21 | L32 => L28 | L33 => L16 | L34 => L6 end.

(* P133 : S4 S11 S17 S30 S36 S45 S48 -> 
   P135 : S4 S11 S20 S29 S33 S46 S50  *)
Definition fp133_135 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P4 | P4 => P3 | P5 => P6 | P6 => P5 | P7 => P10 | P8 => P9 | P9 => P8 | P10 => P7 | P11 => P13 | P12 => P14 | P13 => P11 | P14 => P12 end.
Definition fl133_135 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L4 | L4 => L3 | L5 => L6 | L6 => L5 | L7 => L12 | L8 => L10 | L9 => L9 | L10 => L8 | L11 => L11 | L12 => L7 | L13 => L13 | L14 => L16 | L15 => L17 | L16 => L14 | L17 => L15 | L18 => L18 | L19 => L26 | L20 => L23 | L21 => L24 | L22 => L25 | L23 => L20 | L24 => L21 | L25 => L22 | L26 => L19 | L27 => L33 | L28 => L34 | L29 => L32 | L30 => L31 | L31 => L30 | L32 => L29 | L33 => L27 | L34 => L28 end.

(* P135 : S4 S11 S20 S29 S33 S46 S50 -> 
   P136 : S4 S11 S22 S25 S38 S44 S51  *)
Definition fp135_136 (p:Point) := match p with P0 => P3 | P1 => P13 | P2 => P9 | P3 => P0 | P4 => P4 | P5 => P14 | P6 => P10 | P7 => P12 | P8 => P8 | P9 => P2 | P10 => P6 | P11 => P11 | P12 => P7 | P13 => P1 | P14 => P5 end.
Definition fl135_136 (l:Line) := match l with L0 => L21 | L1 => L1 | L2 => L19 | L3 => L20 | L4 => L15 | L5 => L22 | L6 => L12 | L7 => L25 | L8 => L32 | L9 => L28 | L10 => L16 | L11 => L11 | L12 => L6 | L13 => L33 | L14 => L29 | L15 => L4 | L16 => L10 | L17 => L23 | L18 => L18 | L19 => L2 | L20 => L3 | L21 => L0 | L22 => L5 | L23 => L17 | L24 => L24 | L25 => L7 | L26 => L26 | L27 => L27 | L28 => L9 | L29 => L14 | L30 => L31 | L31 => L30 | L32 => L8 | L33 => L13 | L34 => L34 end.

(* P136 : S4 S11 S22 S25 S38 S44 S51 -> 
   P139 : S4 S13 S19 S29 S38 S42 S48  *)
Definition fp136_139 (p:Point) := match p with P0 => P5 | P1 => P12 | P2 => P10 | P3 => P8 | P4 => P14 | P5 => P3 | P6 => P1 | P7 => P0 | P8 => P6 | P9 => P11 | P10 => P9 | P11 => P7 | P12 => P13 | P13 => P4 | P14 => P2 end.
Definition fl136_139 (l:Line) := match l with L0 => L30 | L1 => L27 | L2 => L12 | L3 => L2 | L4 => L29 | L5 => L28 | L6 => L17 | L7 => L9 | L8 => L33 | L9 => L16 | L10 => L5 | L11 => L26 | L12 => L20 | L13 => L4 | L14 => L13 | L15 => L8 | L16 => L25 | L17 => L19 | L18 => L34 | L19 => L18 | L20 => L32 | L21 => L24 | L22 => L3 | L23 => L14 | L24 => L31 | L25 => L23 | L26 => L6 | L27 => L15 | L28 => L1 | L29 => L22 | L30 => L21 | L31 => L0 | L32 => L7 | L33 => L11 | L34 => L10 end.

(* P139 : S4 S13 S19 S29 S38 S42 S48 -> 
   P141 : S4 S13 S22 S30 S35 S41 S50  *)
Definition fp139_141 (p:Point) := match p with P0 => P0 | P1 => P2 | P2 => P1 | P3 => P3 | P4 => P4 | P5 => P6 | P6 => P5 | P7 => P12 | P8 => P11 | P9 => P13 | P10 => P14 | P11 => P8 | P12 => P7 | P13 => P9 | P14 => P10 end.
Definition fl139_141 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L5 | L4 => L6 | L5 => L3 | L6 => L4 | L7 => L17 | L8 => L14 | L9 => L13 | L10 => L16 | L11 => L18 | L12 => L15 | L13 => L9 | L14 => L8 | L15 => L12 | L16 => L10 | L17 => L7 | L18 => L11 | L19 => L19 | L20 => L22 | L21 => L21 | L22 => L20 | L23 => L25 | L24 => L24 | L25 => L23 | L26 => L26 | L27 => L34 | L28 => L33 | L29 => L32 | L30 => L31 | L31 => L30 | L32 => L29 | L33 => L28 | L34 => L27 end.

(* P141 : S4 S13 S22 S30 S35 S41 S50 -> 
   P142 : S4 S13 S23 S26 S32 S46 S51  *)
Definition fp141_142 (p:Point) := match p with P0 => P9 | P1 => P3 | P2 => P13 | P3 => P1 | P4 => P7 | P5 => P5 | P6 => P11 | P7 => P4 | P8 => P14 | P9 => P0 | P10 => P10 | P11 => P6 | P12 => P12 | P13 => P2 | P14 => P8 end.
Definition fl141_142 (l:Line) := match l with L0 => L21 | L1 => L10 | L2 => L29 | L3 => L23 | L4 => L4 | L5 => L33 | L6 => L18 | L7 => L22 | L8 => L19 | L9 => L20 | L10 => L1 | L11 => L15 | L12 => L12 | L13 => L25 | L14 => L32 | L15 => L11 | L16 => L16 | L17 => L28 | L18 => L6 | L19 => L8 | L20 => L9 | L21 => L0 | L22 => L7 | L23 => L3 | L24 => L31 | L25 => L13 | L26 => L26 | L27 => L27 | L28 => L17 | L29 => L2 | L30 => L30 | L31 => L24 | L32 => L14 | L33 => L5 | L34 => L34 end.

(* P142 : S4 S13 S23 S26 S32 S46 S51 -> 
   P145 : S4 S14 S17 S26 S38 S41 S53  *)
Definition fp142_145 (p:Point) := match p with P0 => P12 | P1 => P10 | P2 => P5 | P3 => P6 | P4 => P9 | P5 => P11 | P6 => P0 | P7 => P2 | P8 => P13 | P9 => P7 | P10 => P4 | P11 => P3 | P12 => P8 | P13 => P14 | P14 => P1 end.
Definition fl142_145 (l:Line) := match l with L0 => L30 | L1 => L33 | L2 => L5 | L3 => L16 | L4 => L26 | L5 => L20 | L6 => L9 | L7 => L4 | L8 => L25 | L9 => L8 | L10 => L13 | L11 => L19 | L12 => L34 | L13 => L17 | L14 => L12 | L15 => L2 | L16 => L27 | L17 => L29 | L18 => L28 | L19 => L7 | L20 => L32 | L21 => L31 | L22 => L15 | L23 => L10 | L24 => L21 | L25 => L23 | L26 => L18 | L27 => L11 | L28 => L14 | L29 => L22 | L30 => L24 | L31 => L0 | L32 => L6 | L33 => L3 | L34 => L1 end.

(* P145 : S4 S14 S17 S26 S38 S41 S53 -> 
   P147 : S4 S14 S19 S31 S32 S45 S50  *)
Definition fp145_147 (p:Point) := match p with P0 => P11 | P1 => P4 | P2 => P8 | P3 => P1 | P4 => P13 | P5 => P6 | P6 => P10 | P7 => P5 | P8 => P9 | P9 => P2 | P10 => P14 | P11 => P3 | P12 => P7 | P13 => P0 | P14 => P12 end.
Definition fl145_147 (l:Line) := match l with L0 => L24 | L1 => L11 | L2 => L34 | L3 => L29 | L4 => L14 | L5 => L22 | L6 => L5 | L7 => L25 | L8 => L23 | L9 => L26 | L10 => L17 | L11 => L1 | L12 => L7 | L13 => L27 | L14 => L20 | L15 => L8 | L16 => L3 | L17 => L32 | L18 => L18 | L19 => L9 | L20 => L10 | L21 => L0 | L22 => L12 | L23 => L16 | L24 => L21 | L25 => L6 | L26 => L28 | L27 => L33 | L28 => L2 | L29 => L15 | L30 => L31 | L31 => L30 | L32 => L4 | L33 => L13 | L34 => L19 end.

(* P147 : S4 S14 S19 S31 S32 S45 S50 -> 
   P148 : S4 S14 S20 S25 S35 S42 S55  *)
Definition fp147_148 (p:Point) := match p with P0 => P11 | P1 => P4 | P2 => P8 | P3 => P13 | P4 => P1 | P5 => P10 | P6 => P6 | P7 => P14 | P8 => P2 | P9 => P9 | P10 => P5 | P11 => P0 | P12 => P12 | P13 => P3 | P14 => P7 end.
Definition fl147_148 (l:Line) := match l with L0 => L24 | L1 => L11 | L2 => L34 | L3 => L14 | L4 => L29 | L5 => L5 | L6 => L22 | L7 => L7 | L8 => L17 | L9 => L26 | L10 => L23 | L11 => L1 | L12 => L25 | L13 => L27 | L14 => L3 | L15 => L32 | L16 => L20 | L17 => L8 | L18 => L18 | L19 => L28 | L20 => L16 | L21 => L21 | L22 => L6 | L23 => L10 | L24 => L0 | L25 => L12 | L26 => L9 | L27 => L13 | L28 => L19 | L29 => L4 | L30 => L30 | L31 => L31 | L32 => L15 | L33 => L33 | L34 => L2 end.

(* P148 : S4 S14 S20 S25 S35 S42 S55 -> 
   P151 : S5 S8 S19 S28 S39 S45 S48  *)
Definition fp148_151 (p:Point) := match p with P0 => P14 | P1 => P8 | P2 => P5 | P3 => P2 | P4 => P11 | P5 => P9 | P6 => P4 | P7 => P7 | P8 => P6 | P9 => P0 | P10 => P13 | P11 => P10 | P12 => P3 | P13 => P1 | P14 => P12 end.
Definition fl148_151 (l:Line) := match l with L0 => L27 | L1 => L14 | L2 => L23 | L3 => L31 | L4 => L6 | L5 => L19 | L6 => L9 | L7 => L24 | L8 => L32 | L9 => L20 | L10 => L3 | L11 => L8 | L12 => L18 | L13 => L28 | L14 => L30 | L15 => L17 | L16 => L12 | L17 => L29 | L18 => L2 | L19 => L16 | L20 => L15 | L21 => L0 | L22 => L13 | L23 => L5 | L24 => L34 | L25 => L11 | L26 => L22 | L27 => L33 | L28 => L10 | L29 => L4 | L30 => L21 | L31 => L26 | L32 => L7 | L33 => L1 | L34 => L25 end.

(* P151 : S5 S8 S19 S28 S39 S45 S48 -> 
   P152 : S5 S8 S21 S26 S37 S46 S49  *)
Definition fp151_152 (p:Point) := match p with P0 => P5 | P1 => P14 | P2 => P8 | P3 => P7 | P4 => P13 | P5 => P6 | P6 => P0 | P7 => P9 | P8 => P11 | P9 => P4 | P10 => P2 | P11 => P1 | P12 => P3 | P13 => P12 | P14 => P10 end.
Definition fl151_152 (l:Line) := match l with L0 => L27 | L1 => L28 | L2 => L2 | L3 => L29 | L4 => L17 | L5 => L12 | L6 => L30 | L7 => L6 | L8 => L14 | L9 => L19 | L10 => L23 | L11 => L9 | L12 => L31 | L13 => L18 | L14 => L8 | L15 => L3 | L16 => L20 | L17 => L32 | L18 => L24 | L19 => L13 | L20 => L22 | L21 => L26 | L22 => L10 | L23 => L25 | L24 => L11 | L25 => L16 | L26 => L21 | L27 => L34 | L28 => L33 | L29 => L7 | L30 => L15 | L31 => L4 | L32 => L5 | L33 => L1 | L34 => L0 end.

(* P152 : S5 S8 S21 S26 S37 S46 S49 -> 
   P154 : S5 S8 S22 S25 S35 S47 S52  *)
Definition fp152_154 (p:Point) := match p with P0 => P5 | P1 => P14 | P2 => P8 | P3 => P7 | P4 => P13 | P5 => P6 | P6 => P0 | P7 => P9 | P8 => P11 | P9 => P4 | P10 => P2 | P11 => P1 | P12 => P3 | P13 => P12 | P14 => P10 end.
Definition fl152_154 (l:Line) := match l with L0 => L27 | L1 => L28 | L2 => L2 | L3 => L29 | L4 => L17 | L5 => L12 | L6 => L30 | L7 => L6 | L8 => L14 | L9 => L19 | L10 => L23 | L11 => L9 | L12 => L31 | L13 => L18 | L14 => L8 | L15 => L3 | L16 => L20 | L17 => L32 | L18 => L24 | L19 => L13 | L20 => L22 | L21 => L26 | L22 => L10 | L23 => L25 | L24 => L11 | L25 => L16 | L26 => L21 | L27 => L34 | L28 => L33 | L29 => L7 | L30 => L15 | L31 => L4 | L32 => L5 | L33 => L1 | L34 => L0 end.

(* P154 : S5 S8 S22 S25 S35 S47 S52 -> 
   P157 : S5 S9 S19 S29 S32 S46 S52  *)
Definition fp154_157 (p:Point) := match p with P0 => P1 | P1 => P2 | P2 => P0 | P3 => P10 | P4 => P8 | P5 => P7 | P6 => P9 | P7 => P14 | P8 => P12 | P9 => P11 | P10 => P13 | P11 => P3 | P12 => P5 | P13 => P6 | P14 => P4 end.
Definition fl154_157 (l:Line) := match l with L0 => L0 | L1 => L8 | L2 => L10 | L3 => L9 | L4 => L11 | L5 => L12 | L6 => L7 | L7 => L18 | L8 => L16 | L9 => L17 | L10 => L14 | L11 => L15 | L12 => L13 | L13 => L6 | L14 => L1 | L15 => L4 | L16 => L2 | L17 => L3 | L18 => L5 | L19 => L25 | L20 => L30 | L21 => L34 | L22 => L19 | L23 => L24 | L24 => L20 | L25 => L32 | L26 => L27 | L27 => L26 | L28 => L31 | L29 => L22 | L30 => L28 | L31 => L23 | L32 => L33 | L33 => L29 | L34 => L21 end.

(* P157 : S5 S9 S19 S29 S32 S46 S52 -> 
   P158 : S5 S9 S20 S28 S35 S41 S54  *)
Definition fp157_158 (p:Point) := match p with P0 => P12 | P1 => P7 | P2 => P4 | P3 => P13 | P4 => P2 | P5 => P5 | P6 => P10 | P7 => P1 | P8 => P14 | P9 => P9 | P10 => P6 | P11 => P11 | P12 => P0 | P13 => P3 | P14 => P8 end.
Definition fl157_158 (l:Line) := match l with L0 => L26 | L1 => L16 | L2 => L30 | L3 => L9 | L4 => L33 | L5 => L5 | L6 => L20 | L7 => L13 | L8 => L31 | L9 => L3 | L10 => L10 | L11 => L22 | L12 => L28 | L13 => L7 | L14 => L24 | L15 => L25 | L16 => L1 | L17 => L17 | L18 => L23 | L19 => L32 | L20 => L6 | L21 => L21 | L22 => L11 | L23 => L18 | L24 => L14 | L25 => L15 | L26 => L0 | L27 => L27 | L28 => L12 | L29 => L29 | L30 => L2 | L31 => L8 | L32 => L19 | L33 => L4 | L34 => L34 end.

(* P158 : S5 S9 S20 S28 S35 S41 S54 -> 
   P160 : S5 S9 S22 S30 S34 S45 S49  *)
Definition fp158_160 (p:Point) := match p with P0 => P13 | P1 => P9 | P2 => P3 | P3 => P12 | P4 => P2 | P5 => P6 | P6 => P8 | P7 => P1 | P8 => P11 | P9 => P7 | P10 => P5 | P11 => P14 | P12 => P0 | P13 => P4 | P14 => P10 end.
Definition fl158_160 (l:Line) := match l with L0 => L21 | L1 => L16 | L2 => L32 | L3 => L11 | L4 => L28 | L5 => L6 | L6 => L25 | L7 => L18 | L8 => L29 | L9 => L4 | L10 => L10 | L11 => L23 | L12 => L33 | L13 => L12 | L14 => L19 | L15 => L20 | L16 => L1 | L17 => L15 | L18 => L22 | L19 => L30 | L20 => L5 | L21 => L26 | L22 => L9 | L23 => L13 | L24 => L14 | L25 => L17 | L26 => L0 | L27 => L34 | L28 => L7 | L29 => L31 | L30 => L2 | L31 => L8 | L32 => L24 | L33 => L3 | L34 => L27 end.

(* P160 : S5 S9 S22 S30 S34 S45 S49 -> 
   P163 : S5 S10 S17 S30 S37 S41 S52  *)
Definition fp160_163 (p:Point) := match p with P0 => P13 | P1 => P3 | P2 => P9 | P3 => P6 | P4 => P8 | P5 => P2 | P6 => P12 | P7 => P14 | P8 => P0 | P9 => P10 | P10 => P4 | P11 => P7 | P12 => P5 | P13 => P11 | P14 => P1 end.
Definition fl160_163 (l:Line) := match l with L0 => L21 | L1 => L32 | L2 => L16 | L3 => L6 | L4 => L25 | L5 => L28 | L6 => L11 | L7 => L20 | L8 => L1 | L9 => L12 | L10 => L19 | L11 => L22 | L12 => L15 | L13 => L23 | L14 => L10 | L15 => L33 | L16 => L29 | L17 => L18 | L18 => L4 | L19 => L7 | L20 => L2 | L21 => L34 | L22 => L31 | L23 => L8 | L24 => L3 | L25 => L24 | L26 => L27 | L27 => L0 | L28 => L14 | L29 => L13 | L30 => L17 | L31 => L9 | L32 => L5 | L33 => L30 | L34 => L26 end.

(* P163 : S5 S10 S17 S30 S37 S41 S52 -> 
   P165 : S5 S10 S20 S29 S39 S42 S49  *)
Definition fp163_165 (p:Point) := match p with P0 => P0 | P1 => P2 | P2 => P1 | P3 => P3 | P4 => P4 | P5 => P6 | P6 => P5 | P7 => P12 | P8 => P11 | P9 => P13 | P10 => P14 | P11 => P8 | P12 => P7 | P13 => P9 | P14 => P10 end.
Definition fl163_165 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L5 | L4 => L6 | L5 => L3 | L6 => L4 | L7 => L17 | L8 => L14 | L9 => L13 | L10 => L16 | L11 => L18 | L12 => L15 | L13 => L9 | L14 => L8 | L15 => L12 | L16 => L10 | L17 => L7 | L18 => L11 | L19 => L19 | L20 => L22 | L21 => L21 | L22 => L20 | L23 => L25 | L24 => L24 | L25 => L23 | L26 => L26 | L27 => L34 | L28 => L33 | L29 => L32 | L30 => L31 | L31 => L30 | L32 => L29 | L33 => L28 | L34 => L27 end.

(* P165 : S5 S10 S20 S29 S39 S42 S49 -> 
   P166 : S5 S10 S21 S28 S32 S47 S51  *)
Definition fp165_166 (p:Point) := match p with P0 => P1 | P1 => P0 | P2 => P2 | P3 => P14 | P4 => P12 | P5 => P13 | P6 => P11 | P7 => P7 | P8 => P9 | P9 => P8 | P10 => P10 | P11 => P6 | P12 => P4 | P13 => P5 | P14 => P3 end.
Definition fl165_166 (l:Line) := match l with L0 => L0 | L1 => L9 | L2 => L11 | L3 => L10 | L4 => L8 | L5 => L7 | L6 => L12 | L7 => L5 | L8 => L4 | L9 => L1 | L10 => L3 | L11 => L2 | L12 => L6 | L13 => L13 | L14 => L15 | L15 => L14 | L16 => L17 | L17 => L16 | L18 => L18 | L19 => L19 | L20 => L23 | L21 => L27 | L22 => L31 | L23 => L20 | L24 => L33 | L25 => L30 | L26 => L26 | L27 => L21 | L28 => L28 | L29 => L32 | L30 => L25 | L31 => L22 | L32 => L29 | L33 => L24 | L34 => L34 end.

(* P166 : S5 S10 S21 S28 S32 S47 S51 -> 
   P169 : S5 S12 S17 S29 S34 S47 S48  *)
Definition fp166_169 (p:Point) := match p with P0 => P14 | P1 => P8 | P2 => P5 | P3 => P2 | P4 => P11 | P5 => P9 | P6 => P4 | P7 => P10 | P8 => P3 | P9 => P1 | P10 => P12 | P11 => P7 | P12 => P6 | P13 => P0 | P14 => P13 end.
Definition fl166_169 (l:Line) := match l with L0 => L27 | L1 => L14 | L2 => L23 | L3 => L19 | L4 => L9 | L5 => L31 | L6 => L6 | L7 => L24 | L8 => L20 | L9 => L32 | L10 => L8 | L11 => L3 | L12 => L18 | L13 => L30 | L14 => L28 | L15 => L17 | L16 => L2 | L17 => L29 | L18 => L12 | L19 => L16 | L20 => L15 | L21 => L0 | L22 => L13 | L23 => L11 | L24 => L22 | L25 => L5 | L26 => L34 | L27 => L21 | L28 => L4 | L29 => L10 | L30 => L33 | L31 => L25 | L32 => L1 | L33 => L7 | L34 => L26 end.

(* P169 : S5 S12 S17 S29 S34 S47 S48 -> 
   P170 : S5 S12 S19 S25 S37 S42 S54  *)
Definition fp169_170 (p:Point) := match p with P0 => P3 | P1 => P9 | P2 => P13 | P3 => P0 | P4 => P4 | P5 => P10 | P6 => P14 | P7 => P7 | P8 => P11 | P9 => P1 | P10 => P5 | P11 => P8 | P12 => P12 | P13 => P2 | P14 => P6 end.
Definition fl169_170 (l:Line) := match l with L0 => L21 | L1 => L1 | L2 => L19 | L3 => L22 | L4 => L12 | L5 => L20 | L6 => L15 | L7 => L23 | L8 => L29 | L9 => L33 | L10 => L10 | L11 => L18 | L12 => L4 | L13 => L28 | L14 => L32 | L15 => L6 | L16 => L16 | L17 => L25 | L18 => L11 | L19 => L2 | L20 => L5 | L21 => L0 | L22 => L3 | L23 => L7 | L24 => L24 | L25 => L17 | L26 => L26 | L27 => L34 | L28 => L13 | L29 => L8 | L30 => L30 | L31 => L31 | L32 => L14 | L33 => L9 | L34 => L27 end.

(* P170 : S5 S12 S19 S25 S37 S42 S54 -> 
   P173 : S5 S12 S22 S26 S39 S41 S51  *)
Definition fp170_173 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P4 | P4 => P3 | P5 => P6 | P6 => P5 | P7 => P9 | P8 => P10 | P9 => P7 | P10 => P8 | P11 => P14 | P12 => P13 | P13 => P12 | P14 => P11 end.
Definition fl170_173 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L4 | L4 => L3 | L5 => L6 | L6 => L5 | L7 => L12 | L8 => L8 | L9 => L11 | L10 => L10 | L11 => L9 | L12 => L7 | L13 => L18 | L14 => L14 | L15 => L17 | L16 => L16 | L17 => L15 | L18 => L13 | L19 => L24 | L20 => L25 | L21 => L26 | L22 => L23 | L23 => L22 | L24 => L19 | L25 => L20 | L26 => L21 | L27 => L34 | L28 => L33 | L29 => L31 | L30 => L32 | L31 => L29 | L32 => L30 | L33 => L28 | L34 => L27 end.

(* P173 : S5 S12 S22 S26 S39 S41 S51 -> 
   P174 : S5 S15 S17 S26 S32 S45 S54  *)
Definition fp173_174 (p:Point) := match p with P0 => P12 | P1 => P7 | P2 => P4 | P3 => P10 | P4 => P5 | P5 => P2 | P6 => P13 | P7 => P14 | P8 => P1 | P9 => P6 | P10 => P9 | P11 => P3 | P12 => P8 | P13 => P11 | P14 => P0 end.
Definition fl173_174 (l:Line) := match l with L0 => L26 | L1 => L30 | L2 => L16 | L3 => L9 | L4 => L33 | L5 => L20 | L6 => L5 | L7 => L28 | L8 => L10 | L9 => L3 | L10 => L31 | L11 => L22 | L12 => L13 | L13 => L23 | L14 => L1 | L15 => L25 | L16 => L24 | L17 => L17 | L18 => L7 | L19 => L4 | L20 => L8 | L21 => L34 | L22 => L19 | L23 => L2 | L24 => L12 | L25 => L29 | L26 => L27 | L27 => L0 | L28 => L14 | L29 => L15 | L30 => L18 | L31 => L6 | L32 => L11 | L33 => L32 | L34 => L21 end.

(* P174 : S5 S15 S17 S26 S32 S45 S54 -> 
   P176 : S5 S15 S20 S25 S34 S46 S51  *)
Definition fp174_176 (p:Point) := match p with P0 => P0 | P1 => P2 | P2 => P1 | P3 => P3 | P4 => P4 | P5 => P6 | P6 => P5 | P7 => P12 | P8 => P11 | P9 => P13 | P10 => P14 | P11 => P8 | P12 => P7 | P13 => P9 | P14 => P10 end.
Definition fl174_176 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L5 | L4 => L6 | L5 => L3 | L6 => L4 | L7 => L17 | L8 => L14 | L9 => L13 | L10 => L16 | L11 => L18 | L12 => L15 | L13 => L9 | L14 => L8 | L15 => L12 | L16 => L10 | L17 => L7 | L18 => L11 | L19 => L19 | L20 => L22 | L21 => L21 | L22 => L20 | L23 => L25 | L24 => L24 | L25 => L23 | L26 => L26 | L27 => L34 | L28 => L33 | L29 => L32 | L30 => L31 | L31 => L30 | L32 => L29 | L33 => L28 | L34 => L27 end.

(* P176 : S5 S15 S20 S25 S34 S46 S51 -> 
   P179 : S5 S15 S21 S30 S35 S42 S48  *)
Definition fp176_179 (p:Point) := match p with P0 => P9 | P1 => P3 | P2 => P13 | P3 => P2 | P4 => P8 | P5 => P6 | P6 => P12 | P7 => P5 | P8 => P11 | P9 => P1 | P10 => P7 | P11 => P4 | P12 => P14 | P13 => P0 | P14 => P10 end.
Definition fl176_179 (l:Line) := match l with L0 => L21 | L1 => L18 | L2 => L33 | L3 => L29 | L4 => L10 | L5 => L23 | L6 => L4 | L7 => L20 | L8 => L22 | L9 => L19 | L10 => L12 | L11 => L1 | L12 => L15 | L13 => L28 | L14 => L25 | L15 => L16 | L16 => L6 | L17 => L32 | L18 => L11 | L19 => L13 | L20 => L14 | L21 => L0 | L22 => L17 | L23 => L8 | L24 => L24 | L25 => L3 | L26 => L27 | L27 => L34 | L28 => L2 | L29 => L7 | L30 => L31 | L31 => L30 | L32 => L5 | L33 => L9 | L34 => L26 end.

(* P179 : S5 S15 S21 S30 S35 S42 S48 -> 
   P181 : S6 S8 S18 S25 S37 S44 S55  *)
Definition fp179_181 (p:Point) := match p with P0 => P12 | P1 => P5 | P2 => P10 | P3 => P6 | P4 => P9 | P5 => P0 | P6 => P11 | P7 => P14 | P8 => P1 | P9 => P8 | P10 => P3 | P11 => P7 | P12 => P4 | P13 => P13 | P14 => P2 end.
Definition fl179_181 (l:Line) := match l with L0 => L30 | L1 => L33 | L2 => L5 | L3 => L9 | L4 => L20 | L5 => L26 | L6 => L16 | L7 => L29 | L8 => L12 | L9 => L17 | L10 => L27 | L11 => L28 | L12 => L2 | L13 => L19 | L14 => L13 | L15 => L34 | L16 => L25 | L17 => L4 | L18 => L8 | L19 => L15 | L20 => L7 | L21 => L32 | L22 => L31 | L23 => L18 | L24 => L10 | L25 => L21 | L26 => L23 | L27 => L0 | L28 => L6 | L29 => L3 | L30 => L1 | L31 => L14 | L32 => L11 | L33 => L24 | L34 => L22 end.

(* P181 : S6 S8 S18 S25 S37 S44 S55 -> 
   P183 : S6 S8 S21 S27 S36 S47 S48  *)
Definition fp181_183 (p:Point) := match p with P0 => P11 | P1 => P7 | P2 => P3 | P3 => P14 | P4 => P2 | P5 => P6 | P6 => P10 | P7 => P9 | P8 => P5 | P9 => P1 | P10 => P13 | P11 => P4 | P12 => P8 | P13 => P12 | P14 => P0 end.
Definition fl181_183 (l:Line) := match l with L0 => L22 | L1 => L14 | L2 => L34 | L3 => L29 | L4 => L11 | L5 => L24 | L6 => L5 | L7 => L13 | L8 => L28 | L9 => L3 | L10 => L10 | L11 => L26 | L12 => L31 | L13 => L21 | L14 => L1 | L15 => L19 | L16 => L20 | L17 => L15 | L18 => L12 | L19 => L6 | L20 => L27 | L21 => L9 | L22 => L23 | L23 => L0 | L24 => L17 | L25 => L16 | L26 => L18 | L27 => L2 | L28 => L33 | L29 => L7 | L30 => L32 | L31 => L4 | L32 => L30 | L33 => L8 | L34 => L25 end.

(* P183 : S6 S8 S21 S27 S36 S47 S48 -> 
   P184 : S6 S8 S23 S26 S39 S40 S53  *)
Definition fp183_184 (p:Point) := match p with P0 => P11 | P1 => P7 | P2 => P3 | P3 => P2 | P4 => P14 | P5 => P10 | P6 => P6 | P7 => P1 | P8 => P13 | P9 => P9 | P10 => P5 | P11 => P0 | P12 => P12 | P13 => P8 | P14 => P4 end.
Definition fl183_184 (l:Line) := match l with L0 => L22 | L1 => L14 | L2 => L34 | L3 => L11 | L4 => L29 | L5 => L5 | L6 => L24 | L7 => L31 | L8 => L28 | L9 => L26 | L10 => L10 | L11 => L3 | L12 => L13 | L13 => L12 | L14 => L1 | L15 => L15 | L16 => L20 | L17 => L19 | L18 => L21 | L19 => L17 | L20 => L16 | L21 => L18 | L22 => L0 | L23 => L23 | L24 => L6 | L25 => L27 | L26 => L9 | L27 => L25 | L28 => L8 | L29 => L4 | L30 => L30 | L31 => L7 | L32 => L32 | L33 => L33 | L34 => L2 end.

(* P184 : S6 S8 S23 S26 S39 S40 S53 -> 
   P187 : S6 S9 S18 S30 S36 S41 S53  *)
Definition fp184_187 (p:Point) := match p with P0 => P2 | P1 => P0 | P2 => P1 | P3 => P13 | P4 => P12 | P5 => P14 | P6 => P11 | P7 => P6 | P8 => P3 | P9 => P5 | P10 => P4 | P11 => P8 | P12 => P9 | P13 => P7 | P14 => P10 end.
Definition fl184_187 (l:Line) := match l with L0 => L0 | L1 => L16 | L2 => L14 | L3 => L15 | L4 => L17 | L5 => L18 | L6 => L13 | L7 => L5 | L8 => L1 | L9 => L4 | L10 => L2 | L11 => L3 | L12 => L6 | L13 => L7 | L14 => L8 | L15 => L11 | L16 => L10 | L17 => L9 | L18 => L12 | L19 => L25 | L20 => L21 | L21 => L28 | L22 => L32 | L23 => L30 | L24 => L20 | L25 => L26 | L26 => L33 | L27 => L19 | L28 => L31 | L29 => L27 | L30 => L23 | L31 => L34 | L32 => L22 | L33 => L29 | L34 => L24 end.

(* P187 : S6 S9 S18 S30 S36 S41 S53 -> 
   P189 : S6 S9 S20 S29 S34 S40 S55  *)
Definition fp187_189 (p:Point) := match p with P0 => P5 | P1 => P12 | P2 => P10 | P3 => P9 | P4 => P11 | P5 => P6 | P6 => P0 | P7 => P4 | P8 => P2 | P9 => P7 | P10 => P13 | P11 => P14 | P12 => P8 | P13 => P1 | P14 => P3 end.
Definition fl187_189 (l:Line) := match l with L0 => L30 | L1 => L29 | L2 => L2 | L3 => L17 | L4 => L28 | L5 => L27 | L6 => L12 | L7 => L5 | L8 => L16 | L9 => L20 | L10 => L26 | L11 => L9 | L12 => L33 | L13 => L25 | L14 => L19 | L15 => L4 | L16 => L8 | L17 => L34 | L18 => L13 | L19 => L21 | L20 => L18 | L21 => L10 | L22 => L23 | L23 => L22 | L24 => L14 | L25 => L11 | L26 => L24 | L27 => L15 | L28 => L7 | L29 => L31 | L30 => L32 | L31 => L1 | L32 => L0 | L33 => L3 | L34 => L6 end.

(* P189 : S6 S9 S20 S29 S34 S40 S55 -> 
   P190 : S6 S9 S23 S27 S32 S44 S54  *)
Definition fp189_190 (p:Point) := match p with P0 => P5 | P1 => P12 | P2 => P10 | P3 => P9 | P4 => P11 | P5 => P6 | P6 => P0 | P7 => P4 | P8 => P2 | P9 => P7 | P10 => P13 | P11 => P14 | P12 => P8 | P13 => P1 | P14 => P3 end.
Definition fl189_190 (l:Line) := match l with L0 => L30 | L1 => L29 | L2 => L2 | L3 => L17 | L4 => L28 | L5 => L27 | L6 => L12 | L7 => L5 | L8 => L16 | L9 => L20 | L10 => L26 | L11 => L9 | L12 => L33 | L13 => L25 | L14 => L19 | L15 => L4 | L16 => L8 | L17 => L34 | L18 => L13 | L19 => L21 | L20 => L18 | L21 => L10 | L22 => L23 | L23 => L22 | L24 => L14 | L25 => L11 | L26 => L24 | L27 => L15 | L28 => L7 | L29 => L31 | L30 => L32 | L31 => L1 | L32 => L0 | L33 => L3 | L34 => L6 end.

(* P190 : S6 S9 S23 S27 S32 S44 S54 -> 
   P193 : S6 S11 S16 S29 S39 S44 S48  *)
Definition fp190_193 (p:Point) := match p with P0 => P12 | P1 => P5 | P2 => P10 | P3 => P14 | P4 => P1 | P5 => P8 | P6 => P3 | P7 => P4 | P8 => P7 | P9 => P2 | P10 => P13 | P11 => P9 | P12 => P6 | P13 => P11 | P14 => P0 end.
Definition fl190_193 (l:Line) := match l with L0 => L30 | L1 => L9 | L2 => L20 | L3 => L26 | L4 => L16 | L5 => L33 | L6 => L5 | L7 => L12 | L8 => L28 | L9 => L2 | L10 => L17 | L11 => L29 | L12 => L27 | L13 => L25 | L14 => L4 | L15 => L19 | L16 => L34 | L17 => L8 | L18 => L13 | L19 => L6 | L20 => L31 | L21 => L14 | L22 => L23 | L23 => L0 | L24 => L10 | L25 => L11 | L26 => L7 | L27 => L3 | L28 => L24 | L29 => L18 | L30 => L32 | L31 => L1 | L32 => L22 | L33 => L15 | L34 => L21 end.

(* P193 : S6 S11 S16 S29 S39 S44 S48 -> 
   P194 : S6 S11 S20 S25 S36 S43 S54  *)
Definition fp193_194 (p:Point) := match p with P0 => P9 | P1 => P14 | P2 => P4 | P3 => P8 | P4 => P2 | P5 => P5 | P6 => P11 | P7 => P13 | P8 => P3 | P9 => P0 | P10 => P10 | P11 => P6 | P12 => P12 | P13 => P7 | P14 => P1 end.
Definition fl193_194 (l:Line) := match l with L0 => L23 | L1 => L18 | L2 => L29 | L3 => L21 | L4 => L4 | L5 => L33 | L6 => L10 | L7 => L14 | L8 => L19 | L9 => L9 | L10 => L6 | L11 => L31 | L12 => L27 | L13 => L25 | L14 => L7 | L15 => L24 | L16 => L26 | L17 => L17 | L18 => L1 | L19 => L8 | L20 => L20 | L21 => L3 | L22 => L32 | L23 => L0 | L24 => L15 | L25 => L13 | L26 => L16 | L27 => L12 | L28 => L28 | L29 => L2 | L30 => L30 | L31 => L11 | L32 => L22 | L33 => L5 | L34 => L34 end.

(* P194 : S6 S11 S20 S25 S36 S43 S54 -> 
   P197 : S6 S11 S21 S30 S37 S40 S50  *)
Definition fp194_197 (p:Point) := match p with P0 => P14 | P1 => P9 | P2 => P4 | P3 => P12 | P4 => P1 | P5 => P6 | P6 => P7 | P7 => P10 | P8 => P3 | P9 => P0 | P10 => P13 | P11 => P5 | P12 => P8 | P13 => P11 | P14 => P2 end.
Definition fl194_197 (l:Line) := match l with L0 => L23 | L1 => L9 | L2 => L31 | L3 => L19 | L4 => L6 | L5 => L27 | L6 => L14 | L7 => L10 | L8 => L21 | L9 => L18 | L10 => L4 | L11 => L29 | L12 => L33 | L13 => L25 | L14 => L17 | L15 => L26 | L16 => L24 | L17 => L7 | L18 => L1 | L19 => L16 | L20 => L20 | L21 => L5 | L22 => L30 | L23 => L0 | L24 => L12 | L25 => L11 | L26 => L8 | L27 => L15 | L28 => L34 | L29 => L2 | L30 => L32 | L31 => L13 | L32 => L22 | L33 => L3 | L34 => L28 end.

(* P197 : S6 S11 S21 S30 S37 S40 S50 -> 
   P198 : S6 S13 S16 S26 S37 S41 S54  *)
Definition fp197_198 (p:Point) := match p with P0 => P8 | P1 => P13 | P2 => P6 | P3 => P14 | P4 => P5 | P5 => P0 | P6 => P7 | P7 => P4 | P8 => P11 | P9 => P10 | P10 => P1 | P11 => P9 | P12 => P2 | P13 => P3 | P14 => P12 end.
Definition fl197_198 (l:Line) := match l with L0 => L32 | L1 => L27 | L2 => L3 | L3 => L24 | L4 => L8 | L5 => L18 | L6 => L20 | L7 => L28 | L8 => L11 | L9 => L16 | L10 => L25 | L11 => L21 | L12 => L6 | L13 => L7 | L14 => L33 | L15 => L31 | L16 => L15 | L17 => L2 | L18 => L34 | L19 => L9 | L20 => L14 | L21 => L19 | L22 => L23 | L23 => L30 | L24 => L29 | L25 => L12 | L26 => L17 | L27 => L5 | L28 => L1 | L29 => L4 | L30 => L0 | L31 => L26 | L32 => L22 | L33 => L13 | L34 => L10 end.

(* P198 : S6 S13 S16 S26 S37 S41 S54 -> 
   P200 : S6 S13 S18 S29 S32 S47 S50  *)
Definition fp198_200 (p:Point) := match p with P0 => P3 | P1 => P7 | P2 => P11 | P3 => P4 | P4 => P0 | P5 => P12 | P6 => P8 | P7 => P9 | P8 => P13 | P9 => P1 | P10 => P5 | P11 => P14 | P12 => P10 | P13 => P6 | P14 => P2 end.
Definition fl198_200 (l:Line) := match l with L0 => L22 | L1 => L1 | L2 => L20 | L3 => L21 | L4 => L12 | L5 => L19 | L6 => L15 | L7 => L3 | L8 => L28 | L9 => L13 | L10 => L10 | L11 => L31 | L12 => L26 | L13 => L29 | L14 => L14 | L15 => L24 | L16 => L34 | L17 => L5 | L18 => L11 | L19 => L17 | L20 => L25 | L21 => L7 | L22 => L23 | L23 => L0 | L24 => L6 | L25 => L2 | L26 => L4 | L27 => L16 | L28 => L33 | L29 => L9 | L30 => L30 | L31 => L18 | L32 => L32 | L33 => L8 | L34 => L27 end.

(* P200 : S6 S13 S18 S29 S32 S47 S50 -> 
   P203 : S6 S13 S23 S30 S34 S43 S48  *)
Definition fp200_203 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P4 | P4 => P3 | P5 => P6 | P6 => P5 | P7 => P9 | P8 => P10 | P9 => P7 | P10 => P8 | P11 => P14 | P12 => P13 | P13 => P12 | P14 => P11 end.
Definition fl200_203 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L4 | L4 => L3 | L5 => L6 | L6 => L5 | L7 => L12 | L8 => L8 | L9 => L11 | L10 => L10 | L11 => L9 | L12 => L7 | L13 => L18 | L14 => L14 | L15 => L17 | L16 => L16 | L17 => L15 | L18 => L13 | L19 => L24 | L20 => L25 | L21 => L26 | L22 => L23 | L23 => L22 | L24 => L19 | L25 => L20 | L26 => L21 | L27 => L34 | L28 => L33 | L29 => L31 | L30 => L32 | L31 => L29 | L32 => L30 | L33 => L28 | L34 => L27 end.

(* P203 : S6 S13 S23 S30 S34 S43 S48 -> 
   P204 : S6 S14 S16 S25 S34 S47 S53  *)
Definition fp203_204 (p:Point) := match p with P0 => P14 | P1 => P9 | P2 => P4 | P3 => P8 | P4 => P5 | P5 => P2 | P6 => P11 | P7 => P6 | P8 => P7 | P9 => P12 | P10 => P1 | P11 => P13 | P12 => P0 | P13 => P3 | P14 => P10 end.
Definition fl203_204 (l:Line) := match l with L0 => L23 | L1 => L27 | L2 => L14 | L3 => L31 | L4 => L9 | L5 => L6 | L6 => L19 | L7 => L29 | L8 => L10 | L9 => L4 | L10 => L33 | L11 => L21 | L12 => L18 | L13 => L7 | L14 => L25 | L15 => L24 | L16 => L1 | L17 => L17 | L18 => L26 | L19 => L8 | L20 => L3 | L21 => L20 | L22 => L32 | L23 => L30 | L24 => L28 | L25 => L12 | L26 => L2 | L27 => L13 | L28 => L15 | L29 => L16 | L30 => L0 | L31 => L34 | L32 => L22 | L33 => L5 | L34 => L11 end.

(* P204 : S6 S14 S16 S25 S34 S47 S53 -> 
   P207 : S6 S14 S20 S27 S39 S41 S50  *)
Definition fp204_207 (p:Point) := match p with P0 => P1 | P1 => P2 | P2 => P0 | P3 => P11 | P4 => P13 | P5 => P14 | P6 => P12 | P7 => P3 | P8 => P5 | P9 => P6 | P10 => P4 | P11 => P7 | P12 => P9 | P13 => P10 | P14 => P8 end.
Definition fl204_207 (l:Line) := match l with L0 => L0 | L1 => L11 | L2 => L9 | L3 => L12 | L4 => L7 | L5 => L10 | L6 => L8 | L7 => L16 | L8 => L17 | L9 => L18 | L10 => L15 | L11 => L13 | L12 => L14 | L13 => L1 | L14 => L3 | L15 => L5 | L16 => L4 | L17 => L6 | L18 => L2 | L19 => L24 | L20 => L29 | L21 => L34 | L22 => L22 | L23 => L32 | L24 => L28 | L25 => L25 | L26 => L21 | L27 => L27 | L28 => L19 | L29 => L31 | L30 => L23 | L31 => L20 | L32 => L30 | L33 => L33 | L34 => L26 end.

(* P207 : S6 S14 S20 S27 S39 S41 S50 -> 
   P208 : S6 S14 S21 S26 S32 S43 S55  *)
Definition fp207_208 (p:Point) := match p with P0 => P1 | P1 => P0 | P2 => P2 | P3 => P11 | P4 => P13 | P5 => P12 | P6 => P14 | P7 => P7 | P8 => P9 | P9 => P8 | P10 => P10 | P11 => P3 | P12 => P5 | P13 => P4 | P14 => P6 end.
Definition fl207_208 (l:Line) := match l with L0 => L0 | L1 => L11 | L2 => L9 | L3 => L10 | L4 => L8 | L5 => L12 | L6 => L7 | L7 => L6 | L8 => L4 | L9 => L2 | L10 => L3 | L11 => L1 | L12 => L5 | L13 => L13 | L14 => L15 | L15 => L14 | L16 => L17 | L17 => L16 | L18 => L18 | L19 => L34 | L20 => L29 | L21 => L24 | L22 => L22 | L23 => L32 | L24 => L21 | L25 => L25 | L26 => L28 | L27 => L33 | L28 => L26 | L29 => L20 | L30 => L30 | L31 => L31 | L32 => L23 | L33 => L27 | L34 => L19 end.

(* P208 : S6 S14 S21 S26 S32 S43 S55 -> 
   P210 : S7 S9 S18 S28 S32 S45 S55  *)
Definition fp208_210 (p:Point) := match p with P0 => P0 | P1 => P2 | P2 => P1 | P3 => P4 | P4 => P3 | P5 => P5 | P6 => P6 | P7 => P10 | P8 => P9 | P9 => P7 | P10 => P8 | P11 => P13 | P12 => P14 | P13 => P12 | P14 => P11 end.
Definition fl208_210 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L4 | L4 => L3 | L5 => L6 | L6 => L5 | L7 => L15 | L8 => L18 | L9 => L14 | L10 => L13 | L11 => L16 | L12 => L17 | L13 => L8 | L14 => L11 | L15 => L7 | L16 => L9 | L17 => L12 | L18 => L10 | L19 => L24 | L20 => L23 | L21 => L26 | L22 => L25 | L23 => L22 | L24 => L21 | L25 => L20 | L26 => L19 | L27 => L29 | L28 => L30 | L29 => L28 | L30 => L27 | L31 => L34 | L32 => L33 | L33 => L31 | L34 => L32 end.

(* P210 : S7 S9 S18 S28 S32 S45 S55 -> 
   P213 : S7 S9 S22 S27 S38 S41 S52  *)
Definition fp210_213 (p:Point) := match p with P0 => P10 | P1 => P13 | P2 => P4 | P3 => P8 | P4 => P1 | P5 => P6 | P6 => P11 | P7 => P5 | P8 => P12 | P9 => P7 | P10 => P2 | P11 => P14 | P12 => P3 | P13 => P0 | P14 => P9 end.
Definition fl210_213 (l:Line) := match l with L0 => L25 | L1 => L8 | L2 => L34 | L3 => L30 | L4 => L13 | L5 => L19 | L6 => L4 | L7 => L11 | L8 => L16 | L9 => L21 | L10 => L28 | L11 => L6 | L12 => L32 | L13 => L17 | L14 => L23 | L15 => L24 | L16 => L1 | L17 => L7 | L18 => L26 | L19 => L18 | L20 => L20 | L21 => L3 | L22 => L27 | L23 => L10 | L24 => L9 | L25 => L0 | L26 => L12 | L27 => L33 | L28 => L2 | L29 => L31 | L30 => L15 | L31 => L29 | L32 => L5 | L33 => L22 | L34 => L14 end.

(* P213 : S7 S9 S22 S27 S38 S41 S52 -> 
   P214 : S7 S9 S23 S24 S34 S46 S53  *)
Definition fp213_214 (p:Point) := match p with P0 => P10 | P1 => P4 | P2 => P13 | P3 => P8 | P4 => P1 | P5 => P11 | P6 => P6 | P7 => P14 | P8 => P3 | P9 => P9 | P10 => P0 | P11 => P5 | P12 => P12 | P13 => P2 | P14 => P7 end.
Definition fl213_214 (l:Line) := match l with L0 => L25 | L1 => L8 | L2 => L34 | L3 => L19 | L4 => L4 | L5 => L30 | L6 => L13 | L7 => L7 | L8 => L1 | L9 => L26 | L10 => L23 | L11 => L17 | L12 => L24 | L13 => L6 | L14 => L28 | L15 => L32 | L16 => L16 | L17 => L11 | L18 => L21 | L19 => L3 | L20 => L20 | L21 => L18 | L22 => L27 | L23 => L10 | L24 => L12 | L25 => L0 | L26 => L9 | L27 => L22 | L28 => L14 | L29 => L29 | L30 => L5 | L31 => L31 | L32 => L15 | L33 => L33 | L34 => L2 end.

(* P214 : S7 S9 S23 S24 S34 S46 S53 -> 
   P216 : S7 S10 S16 S28 S39 S41 S53  *)
Definition fp214_216 (p:Point) := match p with P0 => P12 | P1 => P6 | P2 => P9 | P3 => P1 | P4 => P14 | P5 => P4 | P6 => P7 | P7 => P2 | P8 => P13 | P9 => P3 | P10 => P8 | P11 => P0 | P12 => P11 | P13 => P5 | P14 => P10 end.
Definition fl214_216 (l:Line) := match l with L0 => L33 | L1 => L9 | L2 => L26 | L3 => L16 | L4 => L20 | L5 => L5 | L6 => L30 | L7 => L31 | L8 => L32 | L9 => L34 | L10 => L15 | L11 => L2 | L12 => L7 | L13 => L18 | L14 => L4 | L15 => L10 | L16 => L29 | L17 => L23 | L18 => L21 | L19 => L8 | L20 => L11 | L21 => L12 | L22 => L0 | L23 => L19 | L24 => L6 | L25 => L27 | L26 => L14 | L27 => L25 | L28 => L17 | L29 => L1 | L30 => L24 | L31 => L13 | L32 => L28 | L33 => L22 | L34 => L3 end.

(* P216 : S7 S10 S16 S28 S39 S41 S53 -> 
   P218 : S7 S10 S21 S24 S37 S42 S55  *)
Definition fp216_218 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P4 | P4 => P3 | P5 => P6 | P6 => P5 | P7 => P10 | P8 => P9 | P9 => P8 | P10 => P7 | P11 => P13 | P12 => P14 | P13 => P11 | P14 => P12 end.
Definition fl216_218 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L4 | L4 => L3 | L5 => L6 | L6 => L5 | L7 => L12 | L8 => L10 | L9 => L9 | L10 => L8 | L11 => L11 | L12 => L7 | L13 => L13 | L14 => L16 | L15 => L17 | L16 => L14 | L17 => L15 | L18 => L18 | L19 => L26 | L20 => L23 | L21 => L24 | L22 => L25 | L23 => L20 | L24 => L21 | L25 => L22 | L26 => L19 | L27 => L33 | L28 => L34 | L29 => L32 | L30 => L31 | L31 => L30 | L32 => L29 | L33 => L27 | L34 => L28 end.

(* P218 : S7 S10 S21 S24 S37 S42 S55 -> 
   P221 : S7 S10 S23 S31 S32 S43 S52  *)
Definition fp218_221 (p:Point) := match p with P0 => P4 | P1 => P13 | P2 => P10 | P3 => P0 | P4 => P3 | P5 => P14 | P6 => P9 | P7 => P2 | P8 => P5 | P9 => P12 | P10 => P7 | P11 => P1 | P12 => P6 | P13 => P11 | P14 => P8 end.
Definition fl218_221 (l:Line) := match l with L0 => L25 | L1 => L1 | L2 => L23 | L3 => L17 | L4 => L26 | L5 => L7 | L6 => L24 | L7 => L21 | L8 => L28 | L9 => L32 | L10 => L16 | L11 => L11 | L12 => L6 | L13 => L13 | L14 => L8 | L15 => L4 | L16 => L34 | L17 => L19 | L18 => L30 | L19 => L3 | L20 => L2 | L21 => L5 | L22 => L0 | L23 => L20 | L24 => L12 | L25 => L22 | L26 => L15 | L27 => L27 | L28 => L14 | L29 => L9 | L30 => L31 | L31 => L18 | L32 => L29 | L33 => L33 | L34 => L10 end.

(* P221 : S7 S10 S23 S31 S32 S43 S52 -> 
   P222 : S7 S11 S16 S25 S37 S46 S52  *)
Definition fp221_222 (p:Point) := match p with P0 => P12 | P1 => P6 | P2 => P9 | P3 => P1 | P4 => P14 | P5 => P4 | P6 => P7 | P7 => P2 | P8 => P13 | P9 => P3 | P10 => P8 | P11 => P0 | P12 => P11 | P13 => P5 | P14 => P10 end.
Definition fl221_222 (l:Line) := match l with L0 => L33 | L1 => L9 | L2 => L26 | L3 => L16 | L4 => L20 | L5 => L5 | L6 => L30 | L7 => L31 | L8 => L32 | L9 => L34 | L10 => L15 | L11 => L2 | L12 => L7 | L13 => L18 | L14 => L4 | L15 => L10 | L16 => L29 | L17 => L23 | L18 => L21 | L19 => L8 | L20 => L11 | L21 => L12 | L22 => L0 | L23 => L19 | L24 => L6 | L25 => L27 | L26 => L14 | L27 => L25 | L28 => L17 | L29 => L1 | L30 => L24 | L31 => L13 | L32 => L28 | L33 => L22 | L34 => L3 end.

(* P222 : S7 S11 S16 S25 S37 S46 S52 -> 
   P225 : S7 S11 S21 S28 S38 S43 S48  *)
Definition fp222_225 (p:Point) := match p with P0 => P6 | P1 => P12 | P2 => P9 | P3 => P11 | P4 => P10 | P5 => P0 | P6 => P5 | P7 => P3 | P8 => P2 | P9 => P8 | P10 => P13 | P11 => P7 | P12 => P14 | P13 => P4 | P14 => P1 end.
Definition fl222_225 (l:Line) := match l with L0 => L33 | L1 => L34 | L2 => L2 | L3 => L15 | L4 => L32 | L5 => L31 | L6 => L7 | L7 => L30 | L8 => L16 | L9 => L9 | L10 => L20 | L11 => L26 | L12 => L5 | L13 => L21 | L14 => L10 | L15 => L29 | L16 => L23 | L17 => L4 | L18 => L18 | L19 => L11 | L20 => L14 | L21 => L24 | L22 => L22 | L23 => L8 | L24 => L13 | L25 => L25 | L26 => L19 | L27 => L0 | L28 => L1 | L29 => L3 | L30 => L6 | L31 => L12 | L32 => L17 | L33 => L27 | L34 => L28 end.

(* P225 : S7 S11 S21 S28 S38 S43 S48 -> 
   P226 : S7 S11 S22 S24 S39 S45 S50  *)
Definition fp225_226 (p:Point) := match p with P0 => P6 | P1 => P9 | P2 => P12 | P3 => P10 | P4 => P11 | P5 => P0 | P6 => P5 | P7 => P4 | P8 => P1 | P9 => P14 | P10 => P7 | P11 => P13 | P12 => P8 | P13 => P3 | P14 => P2 end.
Definition fl225_226 (l:Line) := match l with L0 => L33 | L1 => L34 | L2 => L2 | L3 => L7 | L4 => L31 | L5 => L32 | L6 => L15 | L7 => L29 | L8 => L10 | L9 => L18 | L10 => L23 | L11 => L21 | L12 => L4 | L13 => L26 | L14 => L16 | L15 => L30 | L16 => L20 | L17 => L5 | L18 => L9 | L19 => L13 | L20 => L8 | L21 => L19 | L22 => L25 | L23 => L14 | L24 => L11 | L25 => L22 | L26 => L24 | L27 => L0 | L28 => L1 | L29 => L6 | L30 => L3 | L31 => L17 | L32 => L12 | L33 => L27 | L34 => L28 end.

(* P226 : S7 S11 S22 S24 S39 S45 S50 -> 
   P229 : S7 S12 S18 S31 S37 S41 S50  *)
Definition fp226_229 (p:Point) := match p with P0 => P14 | P1 => P8 | P2 => P5 | P3 => P2 | P4 => P11 | P5 => P9 | P6 => P4 | P7 => P1 | P8 => P12 | P9 => P10 | P10 => P3 | P11 => P0 | P12 => P13 | P13 => P7 | P14 => P6 end.
Definition fl226_229 (l:Line) := match l with L0 => L27 | L1 => L14 | L2 => L23 | L3 => L9 | L4 => L19 | L5 => L6 | L6 => L31 | L7 => L24 | L8 => L20 | L9 => L32 | L10 => L8 | L11 => L3 | L12 => L18 | L13 => L12 | L14 => L2 | L15 => L17 | L16 => L28 | L17 => L29 | L18 => L30 | L19 => L15 | L20 => L16 | L21 => L13 | L22 => L0 | L23 => L34 | L24 => L5 | L25 => L22 | L26 => L11 | L27 => L33 | L28 => L10 | L29 => L4 | L30 => L21 | L31 => L7 | L32 => L26 | L33 => L25 | L34 => L1 end.

(* P229 : S7 S12 S18 S31 S37 S41 S50 -> 
   P230 : S7 S12 S22 S25 S34 S43 S55  *)
Definition fp229_230 (p:Point) := match p with P0 => P2 | P1 => P1 | P2 => P0 | P3 => P11 | P4 => P14 | P5 => P13 | P6 => P12 | P7 => P7 | P8 => P10 | P9 => P9 | P10 => P8 | P11 => P3 | P12 => P6 | P13 => P5 | P14 => P4 end.
Definition fl229_230 (l:Line) := match l with L0 => L0 | L1 => L14 | L2 => L16 | L3 => L13 | L4 => L18 | L5 => L15 | L6 => L17 | L7 => L9 | L8 => L8 | L9 => L7 | L10 => L10 | L11 => L12 | L12 => L11 | L13 => L3 | L14 => L1 | L15 => L5 | L16 => L2 | L17 => L6 | L18 => L4 | L19 => L24 | L20 => L34 | L21 => L29 | L22 => L22 | L23 => L23 | L24 => L19 | L25 => L27 | L26 => L31 | L27 => L25 | L28 => L28 | L29 => L21 | L30 => L32 | L31 => L26 | L32 => L30 | L33 => L33 | L34 => L20 end.

(* P230 : S7 S12 S22 S25 S34 S43 S55 -> 
   P232 : S7 S12 S23 S27 S39 S42 S48  *)
Definition fp230_232 (p:Point) := match p with P0 => P1 | P1 => P2 | P2 => P0 | P3 => P7 | P4 => P9 | P5 => P10 | P6 => P8 | P7 => P11 | P8 => P13 | P9 => P14 | P10 => P12 | P11 => P3 | P12 => P5 | P13 => P6 | P14 => P4 end.
Definition fl230_232 (l:Line) := match l with L0 => L0 | L1 => L10 | L2 => L8 | L3 => L11 | L4 => L9 | L5 => L12 | L6 => L7 | L7 => L18 | L8 => L16 | L9 => L17 | L10 => L14 | L11 => L15 | L12 => L13 | L13 => L5 | L14 => L1 | L15 => L3 | L16 => L2 | L17 => L4 | L18 => L6 | L19 => L26 | L20 => L28 | L21 => L31 | L22 => L22 | L23 => L23 | L24 => L21 | L25 => L33 | L26 => L29 | L27 => L25 | L28 => L34 | L29 => L19 | L30 => L30 | L31 => L24 | L32 => L32 | L33 => L27 | L34 => L20 end.

(* P232 : S7 S12 S23 S27 S39 S42 S48 -> 
   P235 : S7 S15 S16 S31 S34 S45 S48  *)
Definition fp232_235 (p:Point) := match p with P0 => P9 | P1 => P6 | P2 => P12 | P3 => P8 | P4 => P2 | P5 => P13 | P6 => P3 | P7 => P14 | P8 => P4 | P9 => P7 | P10 => P1 | P11 => P5 | P12 => P11 | P13 => P0 | P14 => P10 end.
Definition fl232_235 (l:Line) := match l with L0 => L33 | L1 => L18 | L2 => L21 | L3 => L23 | L4 => L10 | L5 => L29 | L6 => L4 | L7 => L15 | L8 => L7 | L9 => L34 | L10 => L31 | L11 => L2 | L12 => L32 | L13 => L9 | L14 => L30 | L15 => L20 | L16 => L5 | L17 => L16 | L18 => L26 | L19 => L8 | L20 => L24 | L21 => L3 | L22 => L27 | L23 => L13 | L24 => L17 | L25 => L0 | L26 => L14 | L27 => L25 | L28 => L6 | L29 => L28 | L30 => L11 | L31 => L19 | L32 => L1 | L33 => L22 | L34 => L12 end.

(* P235 : S7 S15 S16 S31 S34 S45 S48 -> 
   P236 : S7 S15 S18 S25 S38 S42 S53  *)
Definition fp235_236 (p:Point) := match p with P0 => P11 | P1 => P3 | P2 => P7 | P3 => P1 | P4 => P13 | P5 => P5 | P6 => P9 | P7 => P2 | P8 => P14 | P9 => P6 | P10 => P10 | P11 => P0 | P12 => P12 | P13 => P4 | P14 => P8 end.
Definition fl235_236 (l:Line) := match l with L0 => L22 | L1 => L11 | L2 => L29 | L3 => L14 | L4 => L34 | L5 => L5 | L6 => L24 | L7 => L21 | L8 => L19 | L9 => L20 | L10 => L15 | L11 => L1 | L12 => L12 | L13 => L13 | L14 => L3 | L15 => L10 | L16 => L26 | L17 => L28 | L18 => L31 | L19 => L8 | L20 => L9 | L21 => L7 | L22 => L0 | L23 => L32 | L24 => L6 | L25 => L25 | L26 => L16 | L27 => L27 | L28 => L17 | L29 => L2 | L30 => L30 | L31 => L18 | L32 => L23 | L33 => L33 | L34 => L4 end.

(* P236 : S7 S15 S18 S25 S38 S42 S53 -> 
   P238 : S7 S15 S21 S27 S32 S46 S50  *)
Definition fp236_238 (p:Point) := match p with P0 => P13 | P1 => P4 | P2 => P10 | P3 => P1 | P4 => P11 | P5 => P6 | P6 => P8 | P7 => P2 | P8 => P12 | P9 => P5 | P10 => P7 | P11 => P0 | P12 => P14 | P13 => P3 | P14 => P9 end.
Definition fl236_238 (l:Line) := match l with L0 => L25 | L1 => L11 | L2 => L32 | L3 => L16 | L4 => L28 | L5 => L6 | L6 => L21 | L7 => L24 | L8 => L26 | L9 => L23 | L10 => L17 | L11 => L1 | L12 => L7 | L13 => L13 | L14 => L4 | L15 => L8 | L16 => L19 | L17 => L34 | L18 => L30 | L19 => L10 | L20 => L9 | L21 => L12 | L22 => L0 | L23 => L29 | L24 => L5 | L25 => L22 | L26 => L14 | L27 => L33 | L28 => L15 | L29 => L2 | L30 => L31 | L31 => L18 | L32 => L20 | L33 => L27 | L34 => L3 end.

(* P238 : S7 S15 S21 S27 S32 S46 S50 -> 
   P1 : S0 S9 S19 S28 S38 S40 S53  *)
Definition fp238_1 (p:Point) := match p with P0 => P0 | P1 => P1 | P2 => P2 | P3 => P3 | P4 => P4 | P5 => P5 | P6 => P6 | P7 => P14 | P8 => P13 | P9 => P12 | P10 => P11 | P11 => P10 | P12 => P9 | P13 => P8 | P14 => P7 end.
Definition fl238_1 (l:Line) := match l with L0 => L0 | L1 => L1 | L2 => L2 | L3 => L6 | L4 => L5 | L5 => L4 | L6 => L3 | L7 => L7 | L8 => L11 | L9 => L10 | L10 => L9 | L11 => L8 | L12 => L12 | L13 => L14 | L14 => L13 | L15 => L15 | L16 => L18 | L17 => L17 | L18 => L16 | L19 => L22 | L20 => L21 | L21 => L20 | L22 => L19 | L23 => L26 | L24 => L25 | L25 => L24 | L26 => L23 | L27 => L28 | L28 => L27 | L29 => L30 | L30 => L29 | L31 => L31 | L32 => L32 | L33 => L33 | L34 => L34 end.


Require Import List.
Check (map fl238_1).
Definition are_isomorphic (p1:list (list Line)) (p2:list (list Line)) : Prop :=
  exists fp, exists fl,
      is_collineation fp fl /\
      forall s:(list Line) (* spread *), In s p1 -> In (map fl s) p2.
      (* map (map fl) p1 = p2. too strong property *)

Lemma are_iso_P238_P1 : are_isomorphic PA238 PA1.
Proof.
  exists fp238_1.
  exists fl238_1.
  split.  
  is_col.
  intros.
  repeat (match goal with H:In _ _ |- _ =>
                          first [elim (in_nil H) | inversion_clear H; [solve [subst; simpl; intuition] | idtac]] end).
Qed.



Lemma all_isomorphic_lemma :  forall t1 t2 : (list (list Line)), In t1 class0 -> In t2 class0 -> are_isomorphic t1 t2.
Proof.
  apply (all_equiv (list Line)).
  simpl; lia.
  admit. (* apply are_isomorphic_refl.*)
  admit. (*  apply are_isomorphic_trans.*)
  unfold all_iso_decomp.
  intros n H.
  apply equiv'.
  repeat split.
  intros.
