Require Import ssreflect ssrfun ssrbool.

Require Import PG32.pg32_inductive PG32.pg32_proofs.
Require Import PG32.pg32_spreads.
Require Import PG32.pg32_spreads_collineations.
Require Import PG32.pg32_spreads_packings.
Require Import PG32.pg32_packings_collineations.
Require Import PG32.pg32_automorphisms.
Require Import PG32.pg32_decomp_prelude.

Require Import List.
Import ListNotations.

(* P4 P0 *)
Lemma is_collineations_descr_B_P4_P0 :
  forall fp fl, is_collineation fp fl -> fp P0 = P4 -> fp P1 = P0 -> In (fp,fl) all_c56.
Proof.
  intros fp fl Hfpfl HP0 HP1.
    assert (HP0P1:(P0<>P1)) by discriminate;
    generalize (fp_lemma fp fl Hfpfl P0 P1 HP0P1); clear HP0P1; rewrite HP0; rewrite HP1; intros HP2; cbn in HP2; 
    case_eq (fp P3); intros HP3; try solve [not_bijP | elim_degen_cases fp fl Hfpfl];
    assert (HP0P3:(P0<>P3)) by discriminate;
      generalize (fp_lemma fp fl Hfpfl P0 P3 HP0P3); clear HP0P3; rewrite HP0; rewrite HP3; intros HP4; cbn in HP4;
        assert (HP1P3:(P1<>P3)) by discriminate;
        generalize (fp_lemma fp fl Hfpfl P1 P3 HP1P3); clear HP1P3; rewrite HP1; rewrite HP3; intros HP5; cbn in HP5;
          assert (HP0P5:(P0<>P5)) by discriminate;
          generalize (fp_lemma fp fl Hfpfl P0 P5 HP0P5); clear HP0P5; rewrite HP0; rewrite HP5; intros HP6; cbn in HP6;
            case_eq (fp P7); intros HP7; try solve [not_bijP | elim_degen_cases fp fl Hfpfl];
    assert (HP0P7:(P0<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P0 P7 HP0P7); clear HP0P7; rewrite HP0; rewrite HP7; intros HP8; cbn in HP8;
 assert (HP1P7:(P1<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P1 P7 HP1P7); clear HP1P7; rewrite HP1; rewrite HP7; intros HP9; cbn in HP9;
  assert (HP2P7:(P2<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P2 P7 HP2P7); clear HP2P7; rewrite HP2; rewrite HP7; intros HP10; cbn in HP10;
assert (HP3P7:(P3<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P3 P7 HP3P7); clear HP3P7; rewrite HP3; rewrite HP7; intros HP11; cbn in HP11;
assert (HP4P7:(P4<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P4 P7 HP4P7); clear HP4P7; rewrite HP4; rewrite HP7; intros HP12; cbn in HP12;
assert (HP5P7:(P5<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P5 P7 HP5P7); clear HP5P7; rewrite HP5; rewrite HP7; intros HP13; cbn in HP13;
assert (HP6P7:(P6<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P6 P7 HP6P7); clear HP6P7; rewrite HP6; rewrite HP7; intros HP14; cbn in HP14;
assert (Hfl:(fl L0 = l_from_points (fp P0) (fp P1) /\
    fl L1 = l_from_points (fp P0) (fp P3) /\
    fl L2 = l_from_points (fp P0) (fp P5) /\
    fl L3 = l_from_points (fp P0) (fp P7) /\
    fl L4 = l_from_points (fp P0) (fp P10) /\
    fl L5 = l_from_points (fp P0) (fp P11) /\
    fl L6 = l_from_points (fp P0) (fp P13) /\
    fl L7 = l_from_points (fp P1) (fp P4) /\
    fl L8 = l_from_points (fp P1) (fp P8) /\
    fl L9 = l_from_points (fp P1) (fp P12) /\
    fl L10 = l_from_points (fp P1) (fp P7) /\
    fl L11 = l_from_points (fp P1) (fp P13) /\
    fl L12 = l_from_points (fp P1) (fp P3) /\
    fl L13 = l_from_points (fp P2) (fp P7) /\
    fl L14 = l_from_points (fp P2) (fp P11) /\
    fl L15 = l_from_points (fp P2) (fp P3) /\
    fl L16 = l_from_points (fp P2) (fp P12) /\
    fl L17 = l_from_points (fp P2) (fp P4) /\
    fl L18 = l_from_points (fp P2) (fp P8) /\
    fl L19 = l_from_points (fp P3) (fp P10) /\
    fl L20 = l_from_points (fp P3) (fp P8) /\
    fl L21 = l_from_points (fp P3) (fp P9) /\
    fl L22 = l_from_points (fp P3) (fp P7) /\
    fl L23 = l_from_points (fp P4) (fp P9) /\
    fl L24 = l_from_points (fp P4) (fp P8) /\
    fl L25 = l_from_points (fp P4) (fp P10) /\
    fl L26 = l_from_points (fp P4) (fp P7) /\
    fl L27 = l_from_points (fp P5) (fp P8) /\
    fl L28 = l_from_points (fp P5) (fp P7) /\
    fl L29 = l_from_points (fp P5) (fp P9) /\
    fl L30 = l_from_points (fp P5) (fp P10) /\
    fl L31 = l_from_points (fp P6) (fp P7) /\
    fl L32 = l_from_points (fp P6) (fp P8) /\
    fl L33 = l_from_points (fp P6) (fp P9) /\
    fl L34 = l_from_points (fp P6) (fp P10))) by (repeat split; (rewrite <- (is_collineation_l_from_points fp fl Hfpfl); [reflexivity | discriminate]));
rewrite HP0 in Hfl; rewrite HP1 in Hfl; rewrite HP2 in Hfl; rewrite HP3 in Hfl; rewrite HP4 in Hfl;
rewrite HP5 in Hfl; rewrite HP6 in Hfl; rewrite HP7 in Hfl; rewrite HP8 in Hfl; rewrite HP9 in Hfl;
rewrite HP10 in Hfl; rewrite HP11 in Hfl; rewrite HP12 in Hfl; rewrite HP13 in Hfl;
destruct Hfl as [HL0 [HL1 [HL2 [HL3 [HL4 [HL5 [HL6 [HL7 [HL8 [HL9 [HL10 [HL11 [HL12 [HL13 [HL14 [HL15 [HL16 [HL17 [HL18 [HL19 [HL20 [HL21 [HL22 [HL23 [HL24 [HL25 [HL26 [HL27 [HL28 [HL29 [HL30 [HL31 [HL32 [HL33 HL34]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
unfold all_c56.
par:time (repeat (match goal with |- In (?fp, ?fl) ((?fp_i,?fl_i)::_) =>
                let HeqP := fresh in assert (HeqP:fp=fp_i) by (apply fp_ext; intros p; destruct p;
                                       solve [rewrite HP0; reflexivity |
                                              rewrite HP1; reflexivity |
                                              rewrite HP2; reflexivity |
                                              rewrite HP3; reflexivity |
                                              rewrite HP4; reflexivity |
                                              rewrite HP5; reflexivity |
                                              rewrite HP6; reflexivity |
                                              rewrite HP7; reflexivity |
                                              rewrite HP8; reflexivity |
                                              rewrite HP9; reflexivity |
                                              rewrite HP10; reflexivity |
                                              rewrite HP11; reflexivity |
                                              rewrite HP12; reflexivity |
                                              rewrite HP13; reflexivity |
                                              rewrite HP14; reflexivity ]);
                let HeqL := fresh in assert (HeqL:fl=fl_i) by (apply fl_ext; intros l; destruct l;
                                       solve [rewrite HL0; reflexivity |
                                              rewrite HL1; reflexivity |
                                              rewrite HL2; reflexivity |
                                              rewrite HL3; reflexivity |
                                              rewrite HL4; reflexivity |
                                              rewrite HL5; reflexivity |
                                              rewrite HL6; reflexivity |
                                              rewrite HL7; reflexivity |
                                              rewrite HL8; reflexivity |
                                              rewrite HL9; reflexivity |
                                              rewrite HL10; reflexivity |
                                              rewrite HL11; reflexivity |
                                              rewrite HL12; reflexivity |
                                              rewrite HL13; reflexivity |
                                              rewrite HL14; reflexivity |
                                              rewrite HL15; reflexivity |
                                              rewrite HL16; reflexivity |
                                              rewrite HL17; reflexivity |
                                              rewrite HL18; reflexivity |
                                              rewrite HL19; reflexivity |
                                              rewrite HL20; reflexivity |
                                              rewrite HL21; reflexivity |
                                              rewrite HL22; reflexivity |
                                              rewrite HL23; reflexivity |
                                              rewrite HL24; reflexivity |
                                              rewrite HL25; reflexivity |
                                              rewrite HL26; reflexivity |
                                              rewrite HL27; reflexivity |
                                              rewrite HL28; reflexivity |
                                              rewrite HL29; reflexivity |
                                              rewrite HL30; reflexivity |
                                              rewrite HL31; reflexivity |
                                              rewrite HL32; reflexivity |
                                              rewrite HL33; reflexivity |                                              
                                              rewrite HL34; reflexivity ]); rewrite HeqL; rewrite HeqP; apply in_eq
end || apply in_cons)).
Qed.

(* P4 P1 *)
Lemma is_collineations_descr_B_P4_P1 :
  forall fp fl, is_collineation fp fl -> fp P0 = P4 -> fp P1 = P1 -> In (fp,fl) all_c57.
Proof.
  intros fp fl Hfpfl HP0 HP1.
    assert (HP0P1:(P0<>P1)) by discriminate;
    generalize (fp_lemma fp fl Hfpfl P0 P1 HP0P1); clear HP0P1; rewrite HP0; rewrite HP1; intros HP2; cbn in HP2; 
    case_eq (fp P3); intros HP3; try solve [not_bijP | elim_degen_cases fp fl Hfpfl];
    assert (HP0P3:(P0<>P3)) by discriminate;
      generalize (fp_lemma fp fl Hfpfl P0 P3 HP0P3); clear HP0P3; rewrite HP0; rewrite HP3; intros HP4; cbn in HP4;
        assert (HP1P3:(P1<>P3)) by discriminate;
        generalize (fp_lemma fp fl Hfpfl P1 P3 HP1P3); clear HP1P3; rewrite HP1; rewrite HP3; intros HP5; cbn in HP5;
          assert (HP0P5:(P0<>P5)) by discriminate;
          generalize (fp_lemma fp fl Hfpfl P0 P5 HP0P5); clear HP0P5; rewrite HP0; rewrite HP5; intros HP6; cbn in HP6;
            case_eq (fp P7); intros HP7; try solve [not_bijP | elim_degen_cases fp fl Hfpfl];
    assert (HP0P7:(P0<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P0 P7 HP0P7); clear HP0P7; rewrite HP0; rewrite HP7; intros HP8; cbn in HP8;
 assert (HP1P7:(P1<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P1 P7 HP1P7); clear HP1P7; rewrite HP1; rewrite HP7; intros HP9; cbn in HP9;
  assert (HP2P7:(P2<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P2 P7 HP2P7); clear HP2P7; rewrite HP2; rewrite HP7; intros HP10; cbn in HP10;
assert (HP3P7:(P3<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P3 P7 HP3P7); clear HP3P7; rewrite HP3; rewrite HP7; intros HP11; cbn in HP11;
assert (HP4P7:(P4<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P4 P7 HP4P7); clear HP4P7; rewrite HP4; rewrite HP7; intros HP12; cbn in HP12;
assert (HP5P7:(P5<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P5 P7 HP5P7); clear HP5P7; rewrite HP5; rewrite HP7; intros HP13; cbn in HP13;
assert (HP6P7:(P6<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P6 P7 HP6P7); clear HP6P7; rewrite HP6; rewrite HP7; intros HP14; cbn in HP14;
assert (Hfl:(fl L0 = l_from_points (fp P0) (fp P1) /\
    fl L1 = l_from_points (fp P0) (fp P3) /\
    fl L2 = l_from_points (fp P0) (fp P5) /\
    fl L3 = l_from_points (fp P0) (fp P7) /\
    fl L4 = l_from_points (fp P0) (fp P10) /\
    fl L5 = l_from_points (fp P0) (fp P11) /\
    fl L6 = l_from_points (fp P0) (fp P13) /\
    fl L7 = l_from_points (fp P1) (fp P4) /\
    fl L8 = l_from_points (fp P1) (fp P8) /\
    fl L9 = l_from_points (fp P1) (fp P12) /\
    fl L10 = l_from_points (fp P1) (fp P7) /\
    fl L11 = l_from_points (fp P1) (fp P13) /\
    fl L12 = l_from_points (fp P1) (fp P3) /\
    fl L13 = l_from_points (fp P2) (fp P7) /\
    fl L14 = l_from_points (fp P2) (fp P11) /\
    fl L15 = l_from_points (fp P2) (fp P3) /\
    fl L16 = l_from_points (fp P2) (fp P12) /\
    fl L17 = l_from_points (fp P2) (fp P4) /\
    fl L18 = l_from_points (fp P2) (fp P8) /\
    fl L19 = l_from_points (fp P3) (fp P10) /\
    fl L20 = l_from_points (fp P3) (fp P8) /\
    fl L21 = l_from_points (fp P3) (fp P9) /\
    fl L22 = l_from_points (fp P3) (fp P7) /\
    fl L23 = l_from_points (fp P4) (fp P9) /\
    fl L24 = l_from_points (fp P4) (fp P8) /\
    fl L25 = l_from_points (fp P4) (fp P10) /\
    fl L26 = l_from_points (fp P4) (fp P7) /\
    fl L27 = l_from_points (fp P5) (fp P8) /\
    fl L28 = l_from_points (fp P5) (fp P7) /\
    fl L29 = l_from_points (fp P5) (fp P9) /\
    fl L30 = l_from_points (fp P5) (fp P10) /\
    fl L31 = l_from_points (fp P6) (fp P7) /\
    fl L32 = l_from_points (fp P6) (fp P8) /\
    fl L33 = l_from_points (fp P6) (fp P9) /\
    fl L34 = l_from_points (fp P6) (fp P10))) by (repeat split; (rewrite <- (is_collineation_l_from_points fp fl Hfpfl); [reflexivity | discriminate]));
rewrite HP0 in Hfl; rewrite HP1 in Hfl; rewrite HP2 in Hfl; rewrite HP3 in Hfl; rewrite HP4 in Hfl;
rewrite HP5 in Hfl; rewrite HP6 in Hfl; rewrite HP7 in Hfl; rewrite HP8 in Hfl; rewrite HP9 in Hfl;
rewrite HP10 in Hfl; rewrite HP11 in Hfl; rewrite HP12 in Hfl; rewrite HP13 in Hfl;
destruct Hfl as [HL0 [HL1 [HL2 [HL3 [HL4 [HL5 [HL6 [HL7 [HL8 [HL9 [HL10 [HL11 [HL12 [HL13 [HL14 [HL15 [HL16 [HL17 [HL18 [HL19 [HL20 [HL21 [HL22 [HL23 [HL24 [HL25 [HL26 [HL27 [HL28 [HL29 [HL30 [HL31 [HL32 [HL33 HL34]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
unfold all_c57.
par:time (repeat (match goal with |- In (?fp, ?fl) ((?fp_i,?fl_i)::_) =>
                let HeqP := fresh in assert (HeqP:fp=fp_i) by (apply fp_ext; intros p; destruct p;
                                       solve [rewrite HP0; reflexivity |
                                              rewrite HP1; reflexivity |
                                              rewrite HP2; reflexivity |
                                              rewrite HP3; reflexivity |
                                              rewrite HP4; reflexivity |
                                              rewrite HP5; reflexivity |
                                              rewrite HP6; reflexivity |
                                              rewrite HP7; reflexivity |
                                              rewrite HP8; reflexivity |
                                              rewrite HP9; reflexivity |
                                              rewrite HP10; reflexivity |
                                              rewrite HP11; reflexivity |
                                              rewrite HP12; reflexivity |
                                              rewrite HP13; reflexivity |
                                              rewrite HP14; reflexivity ]);
                let HeqL := fresh in assert (HeqL:fl=fl_i) by (apply fl_ext; intros l; destruct l;
                                       solve [rewrite HL0; reflexivity |
                                              rewrite HL1; reflexivity |
                                              rewrite HL2; reflexivity |
                                              rewrite HL3; reflexivity |
                                              rewrite HL4; reflexivity |
                                              rewrite HL5; reflexivity |
                                              rewrite HL6; reflexivity |
                                              rewrite HL7; reflexivity |
                                              rewrite HL8; reflexivity |
                                              rewrite HL9; reflexivity |
                                              rewrite HL10; reflexivity |
                                              rewrite HL11; reflexivity |
                                              rewrite HL12; reflexivity |
                                              rewrite HL13; reflexivity |
                                              rewrite HL14; reflexivity |
                                              rewrite HL15; reflexivity |
                                              rewrite HL16; reflexivity |
                                              rewrite HL17; reflexivity |
                                              rewrite HL18; reflexivity |
                                              rewrite HL19; reflexivity |
                                              rewrite HL20; reflexivity |
                                              rewrite HL21; reflexivity |
                                              rewrite HL22; reflexivity |
                                              rewrite HL23; reflexivity |
                                              rewrite HL24; reflexivity |
                                              rewrite HL25; reflexivity |
                                              rewrite HL26; reflexivity |
                                              rewrite HL27; reflexivity |
                                              rewrite HL28; reflexivity |
                                              rewrite HL29; reflexivity |
                                              rewrite HL30; reflexivity |
                                              rewrite HL31; reflexivity |
                                              rewrite HL32; reflexivity |
                                              rewrite HL33; reflexivity |                                              
                                              rewrite HL34; reflexivity ]); rewrite HeqL; rewrite HeqP; apply in_eq
end || apply in_cons)).
Qed.
 
(* P4 P3 *)
Lemma is_collineations_descr_B_P4_P2 :
  forall fp fl, is_collineation fp fl -> fp P0 = P4 -> fp P1 = P2 -> In (fp,fl) all_c58.
Proof.
  intros fp fl Hfpfl HP0 HP1.
    assert (HP0P1:(P0<>P1)) by discriminate;
    generalize (fp_lemma fp fl Hfpfl P0 P1 HP0P1); clear HP0P1; rewrite HP0; rewrite HP1; intros HP2; cbn in HP2; 
    case_eq (fp P3); intros HP3; try solve [not_bijP | elim_degen_cases fp fl Hfpfl];
    assert (HP0P3:(P0<>P3)) by discriminate;
      generalize (fp_lemma fp fl Hfpfl P0 P3 HP0P3); clear HP0P3; rewrite HP0; rewrite HP3; intros HP4; cbn in HP4;
        assert (HP1P3:(P1<>P3)) by discriminate;
        generalize (fp_lemma fp fl Hfpfl P1 P3 HP1P3); clear HP1P3; rewrite HP1; rewrite HP3; intros HP5; cbn in HP5;
          assert (HP0P5:(P0<>P5)) by discriminate;
          generalize (fp_lemma fp fl Hfpfl P0 P5 HP0P5); clear HP0P5; rewrite HP0; rewrite HP5; intros HP6; cbn in HP6;
            case_eq (fp P7); intros HP7; try solve [not_bijP | elim_degen_cases fp fl Hfpfl];
    assert (HP0P7:(P0<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P0 P7 HP0P7); clear HP0P7; rewrite HP0; rewrite HP7; intros HP8; cbn in HP8;
 assert (HP1P7:(P1<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P1 P7 HP1P7); clear HP1P7; rewrite HP1; rewrite HP7; intros HP9; cbn in HP9;
  assert (HP2P7:(P2<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P2 P7 HP2P7); clear HP2P7; rewrite HP2; rewrite HP7; intros HP10; cbn in HP10;
assert (HP3P7:(P3<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P3 P7 HP3P7); clear HP3P7; rewrite HP3; rewrite HP7; intros HP11; cbn in HP11;
assert (HP4P7:(P4<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P4 P7 HP4P7); clear HP4P7; rewrite HP4; rewrite HP7; intros HP12; cbn in HP12;
assert (HP5P7:(P5<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P5 P7 HP5P7); clear HP5P7; rewrite HP5; rewrite HP7; intros HP13; cbn in HP13;
assert (HP6P7:(P6<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P6 P7 HP6P7); clear HP6P7; rewrite HP6; rewrite HP7; intros HP14; cbn in HP14;
assert (Hfl:(fl L0 = l_from_points (fp P0) (fp P1) /\
    fl L1 = l_from_points (fp P0) (fp P3) /\
    fl L2 = l_from_points (fp P0) (fp P5) /\
    fl L3 = l_from_points (fp P0) (fp P7) /\
    fl L4 = l_from_points (fp P0) (fp P10) /\
    fl L5 = l_from_points (fp P0) (fp P11) /\
    fl L6 = l_from_points (fp P0) (fp P13) /\
    fl L7 = l_from_points (fp P1) (fp P4) /\
    fl L8 = l_from_points (fp P1) (fp P8) /\
    fl L9 = l_from_points (fp P1) (fp P12) /\
    fl L10 = l_from_points (fp P1) (fp P7) /\
    fl L11 = l_from_points (fp P1) (fp P13) /\
    fl L12 = l_from_points (fp P1) (fp P3) /\
    fl L13 = l_from_points (fp P2) (fp P7) /\
    fl L14 = l_from_points (fp P2) (fp P11) /\
    fl L15 = l_from_points (fp P2) (fp P3) /\
    fl L16 = l_from_points (fp P2) (fp P12) /\
    fl L17 = l_from_points (fp P2) (fp P4) /\
    fl L18 = l_from_points (fp P2) (fp P8) /\
    fl L19 = l_from_points (fp P3) (fp P10) /\
    fl L20 = l_from_points (fp P3) (fp P8) /\
    fl L21 = l_from_points (fp P3) (fp P9) /\
    fl L22 = l_from_points (fp P3) (fp P7) /\
    fl L23 = l_from_points (fp P4) (fp P9) /\
    fl L24 = l_from_points (fp P4) (fp P8) /\
    fl L25 = l_from_points (fp P4) (fp P10) /\
    fl L26 = l_from_points (fp P4) (fp P7) /\
    fl L27 = l_from_points (fp P5) (fp P8) /\
    fl L28 = l_from_points (fp P5) (fp P7) /\
    fl L29 = l_from_points (fp P5) (fp P9) /\
    fl L30 = l_from_points (fp P5) (fp P10) /\
    fl L31 = l_from_points (fp P6) (fp P7) /\
    fl L32 = l_from_points (fp P6) (fp P8) /\
    fl L33 = l_from_points (fp P6) (fp P9) /\
    fl L34 = l_from_points (fp P6) (fp P10))) by (repeat split; (rewrite <- (is_collineation_l_from_points fp fl Hfpfl); [reflexivity | discriminate]));
rewrite HP0 in Hfl; rewrite HP1 in Hfl; rewrite HP2 in Hfl; rewrite HP3 in Hfl; rewrite HP4 in Hfl;
rewrite HP5 in Hfl; rewrite HP6 in Hfl; rewrite HP7 in Hfl; rewrite HP8 in Hfl; rewrite HP9 in Hfl;
rewrite HP10 in Hfl; rewrite HP11 in Hfl; rewrite HP12 in Hfl; rewrite HP13 in Hfl;
destruct Hfl as [HL0 [HL1 [HL2 [HL3 [HL4 [HL5 [HL6 [HL7 [HL8 [HL9 [HL10 [HL11 [HL12 [HL13 [HL14 [HL15 [HL16 [HL17 [HL18 [HL19 [HL20 [HL21 [HL22 [HL23 [HL24 [HL25 [HL26 [HL27 [HL28 [HL29 [HL30 [HL31 [HL32 [HL33 HL34]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
unfold all_c58.
par:time (repeat (match goal with |- In (?fp, ?fl) ((?fp_i,?fl_i)::_) =>
                let HeqP := fresh in assert (HeqP:fp=fp_i) by (apply fp_ext; intros p; destruct p;
                                       solve [rewrite HP0; reflexivity |
                                              rewrite HP1; reflexivity |
                                              rewrite HP2; reflexivity |
                                              rewrite HP3; reflexivity |
                                              rewrite HP4; reflexivity |
                                              rewrite HP5; reflexivity |
                                              rewrite HP6; reflexivity |
                                              rewrite HP7; reflexivity |
                                              rewrite HP8; reflexivity |
                                              rewrite HP9; reflexivity |
                                              rewrite HP10; reflexivity |
                                              rewrite HP11; reflexivity |
                                              rewrite HP12; reflexivity |
                                              rewrite HP13; reflexivity |
                                              rewrite HP14; reflexivity ]);
                let HeqL := fresh in assert (HeqL:fl=fl_i) by (apply fl_ext; intros l; destruct l;
                                       solve [rewrite HL0; reflexivity |
                                              rewrite HL1; reflexivity |
                                              rewrite HL2; reflexivity |
                                              rewrite HL3; reflexivity |
                                              rewrite HL4; reflexivity |
                                              rewrite HL5; reflexivity |
                                              rewrite HL6; reflexivity |
                                              rewrite HL7; reflexivity |
                                              rewrite HL8; reflexivity |
                                              rewrite HL9; reflexivity |
                                              rewrite HL10; reflexivity |
                                              rewrite HL11; reflexivity |
                                              rewrite HL12; reflexivity |
                                              rewrite HL13; reflexivity |
                                              rewrite HL14; reflexivity |
                                              rewrite HL15; reflexivity |
                                              rewrite HL16; reflexivity |
                                              rewrite HL17; reflexivity |
                                              rewrite HL18; reflexivity |
                                              rewrite HL19; reflexivity |
                                              rewrite HL20; reflexivity |
                                              rewrite HL21; reflexivity |
                                              rewrite HL22; reflexivity |
                                              rewrite HL23; reflexivity |
                                              rewrite HL24; reflexivity |
                                              rewrite HL25; reflexivity |
                                              rewrite HL26; reflexivity |
                                              rewrite HL27; reflexivity |
                                              rewrite HL28; reflexivity |
                                              rewrite HL29; reflexivity |
                                              rewrite HL30; reflexivity |
                                              rewrite HL31; reflexivity |
                                              rewrite HL32; reflexivity |
                                              rewrite HL33; reflexivity |                                              
                                              rewrite HL34; reflexivity ]); rewrite HeqL; rewrite HeqP; apply in_eq
end || apply in_cons)).
Qed.

(* P4 P3 *)
Lemma is_collineations_descr_B_P4_P3 :
  forall fp fl, is_collineation fp fl -> fp P0 = P4 -> fp P1 = P3 -> In (fp,fl) all_c59.
Proof.
  intros fp fl Hfpfl HP0 HP1.
    assert (HP0P1:(P0<>P1)) by discriminate;
    generalize (fp_lemma fp fl Hfpfl P0 P1 HP0P1); clear HP0P1; rewrite HP0; rewrite HP1; intros HP2; cbn in HP2; 
    case_eq (fp P3); intros HP3; try solve [not_bijP | elim_degen_cases fp fl Hfpfl];
    assert (HP0P3:(P0<>P3)) by discriminate;
      generalize (fp_lemma fp fl Hfpfl P0 P3 HP0P3); clear HP0P3; rewrite HP0; rewrite HP3; intros HP4; cbn in HP4;
        assert (HP1P3:(P1<>P3)) by discriminate;
        generalize (fp_lemma fp fl Hfpfl P1 P3 HP1P3); clear HP1P3; rewrite HP1; rewrite HP3; intros HP5; cbn in HP5;
          assert (HP0P5:(P0<>P5)) by discriminate;
          generalize (fp_lemma fp fl Hfpfl P0 P5 HP0P5); clear HP0P5; rewrite HP0; rewrite HP5; intros HP6; cbn in HP6;
            case_eq (fp P7); intros HP7; try solve [not_bijP | elim_degen_cases fp fl Hfpfl];
    assert (HP0P7:(P0<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P0 P7 HP0P7); clear HP0P7; rewrite HP0; rewrite HP7; intros HP8; cbn in HP8;
 assert (HP1P7:(P1<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P1 P7 HP1P7); clear HP1P7; rewrite HP1; rewrite HP7; intros HP9; cbn in HP9;
  assert (HP2P7:(P2<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P2 P7 HP2P7); clear HP2P7; rewrite HP2; rewrite HP7; intros HP10; cbn in HP10;
assert (HP3P7:(P3<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P3 P7 HP3P7); clear HP3P7; rewrite HP3; rewrite HP7; intros HP11; cbn in HP11;
assert (HP4P7:(P4<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P4 P7 HP4P7); clear HP4P7; rewrite HP4; rewrite HP7; intros HP12; cbn in HP12;
assert (HP5P7:(P5<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P5 P7 HP5P7); clear HP5P7; rewrite HP5; rewrite HP7; intros HP13; cbn in HP13;
assert (HP6P7:(P6<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P6 P7 HP6P7); clear HP6P7; rewrite HP6; rewrite HP7; intros HP14; cbn in HP14;
assert (Hfl:(fl L0 = l_from_points (fp P0) (fp P1) /\
    fl L1 = l_from_points (fp P0) (fp P3) /\
    fl L2 = l_from_points (fp P0) (fp P5) /\
    fl L3 = l_from_points (fp P0) (fp P7) /\
    fl L4 = l_from_points (fp P0) (fp P10) /\
    fl L5 = l_from_points (fp P0) (fp P11) /\
    fl L6 = l_from_points (fp P0) (fp P13) /\
    fl L7 = l_from_points (fp P1) (fp P4) /\
    fl L8 = l_from_points (fp P1) (fp P8) /\
    fl L9 = l_from_points (fp P1) (fp P12) /\
    fl L10 = l_from_points (fp P1) (fp P7) /\
    fl L11 = l_from_points (fp P1) (fp P13) /\
    fl L12 = l_from_points (fp P1) (fp P3) /\
    fl L13 = l_from_points (fp P2) (fp P7) /\
    fl L14 = l_from_points (fp P2) (fp P11) /\
    fl L15 = l_from_points (fp P2) (fp P3) /\
    fl L16 = l_from_points (fp P2) (fp P12) /\
    fl L17 = l_from_points (fp P2) (fp P4) /\
    fl L18 = l_from_points (fp P2) (fp P8) /\
    fl L19 = l_from_points (fp P3) (fp P10) /\
    fl L20 = l_from_points (fp P3) (fp P8) /\
    fl L21 = l_from_points (fp P3) (fp P9) /\
    fl L22 = l_from_points (fp P3) (fp P7) /\
    fl L23 = l_from_points (fp P4) (fp P9) /\
    fl L24 = l_from_points (fp P4) (fp P8) /\
    fl L25 = l_from_points (fp P4) (fp P10) /\
    fl L26 = l_from_points (fp P4) (fp P7) /\
    fl L27 = l_from_points (fp P5) (fp P8) /\
    fl L28 = l_from_points (fp P5) (fp P7) /\
    fl L29 = l_from_points (fp P5) (fp P9) /\
    fl L30 = l_from_points (fp P5) (fp P10) /\
    fl L31 = l_from_points (fp P6) (fp P7) /\
    fl L32 = l_from_points (fp P6) (fp P8) /\
    fl L33 = l_from_points (fp P6) (fp P9) /\
    fl L34 = l_from_points (fp P6) (fp P10))) by (repeat split; (rewrite <- (is_collineation_l_from_points fp fl Hfpfl); [reflexivity | discriminate]));
rewrite HP0 in Hfl; rewrite HP1 in Hfl; rewrite HP2 in Hfl; rewrite HP3 in Hfl; rewrite HP4 in Hfl;
rewrite HP5 in Hfl; rewrite HP6 in Hfl; rewrite HP7 in Hfl; rewrite HP8 in Hfl; rewrite HP9 in Hfl;
rewrite HP10 in Hfl; rewrite HP11 in Hfl; rewrite HP12 in Hfl; rewrite HP13 in Hfl;
destruct Hfl as [HL0 [HL1 [HL2 [HL3 [HL4 [HL5 [HL6 [HL7 [HL8 [HL9 [HL10 [HL11 [HL12 [HL13 [HL14 [HL15 [HL16 [HL17 [HL18 [HL19 [HL20 [HL21 [HL22 [HL23 [HL24 [HL25 [HL26 [HL27 [HL28 [HL29 [HL30 [HL31 [HL32 [HL33 HL34]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
unfold all_c59.
par:time (repeat (match goal with |- In (?fp, ?fl) ((?fp_i,?fl_i)::_) =>
                let HeqP := fresh in assert (HeqP:fp=fp_i) by (apply fp_ext; intros p; destruct p;
                                       solve [rewrite HP0; reflexivity |
                                              rewrite HP1; reflexivity |
                                              rewrite HP2; reflexivity |
                                              rewrite HP3; reflexivity |
                                              rewrite HP4; reflexivity |
                                              rewrite HP5; reflexivity |
                                              rewrite HP6; reflexivity |
                                              rewrite HP7; reflexivity |
                                              rewrite HP8; reflexivity |
                                              rewrite HP9; reflexivity |
                                              rewrite HP10; reflexivity |
                                              rewrite HP11; reflexivity |
                                              rewrite HP12; reflexivity |
                                              rewrite HP13; reflexivity |
                                              rewrite HP14; reflexivity ]);
                let HeqL := fresh in assert (HeqL:fl=fl_i) by (apply fl_ext; intros l; destruct l;
                                       solve [rewrite HL0; reflexivity |
                                              rewrite HL1; reflexivity |
                                              rewrite HL2; reflexivity |
                                              rewrite HL3; reflexivity |
                                              rewrite HL4; reflexivity |
                                              rewrite HL5; reflexivity |
                                              rewrite HL6; reflexivity |
                                              rewrite HL7; reflexivity |
                                              rewrite HL8; reflexivity |
                                              rewrite HL9; reflexivity |
                                              rewrite HL10; reflexivity |
                                              rewrite HL11; reflexivity |
                                              rewrite HL12; reflexivity |
                                              rewrite HL13; reflexivity |
                                              rewrite HL14; reflexivity |
                                              rewrite HL15; reflexivity |
                                              rewrite HL16; reflexivity |
                                              rewrite HL17; reflexivity |
                                              rewrite HL18; reflexivity |
                                              rewrite HL19; reflexivity |
                                              rewrite HL20; reflexivity |
                                              rewrite HL21; reflexivity |
                                              rewrite HL22; reflexivity |
                                              rewrite HL23; reflexivity |
                                              rewrite HL24; reflexivity |
                                              rewrite HL25; reflexivity |
                                              rewrite HL26; reflexivity |
                                              rewrite HL27; reflexivity |
                                              rewrite HL28; reflexivity |
                                              rewrite HL29; reflexivity |
                                              rewrite HL30; reflexivity |
                                              rewrite HL31; reflexivity |
                                              rewrite HL32; reflexivity |
                                              rewrite HL33; reflexivity |                                              
                                              rewrite HL34; reflexivity ]); rewrite HeqL; rewrite HeqP; apply in_eq
end || apply in_cons)).
Qed.

(* P4 P5 *)
Lemma is_collineations_descr_B_P4_P5 :
  forall fp fl, is_collineation fp fl -> fp P0 = P4 -> fp P1 = P5 -> In (fp,fl) all_c60.
Proof.
  intros fp fl Hfpfl HP0 HP1.
    assert (HP0P1:(P0<>P1)) by discriminate;
    generalize (fp_lemma fp fl Hfpfl P0 P1 HP0P1); clear HP0P1; rewrite HP0; rewrite HP1; intros HP2; cbn in HP2; 
    case_eq (fp P3); intros HP3; try solve [not_bijP | elim_degen_cases fp fl Hfpfl];
    assert (HP0P3:(P0<>P3)) by discriminate;
      generalize (fp_lemma fp fl Hfpfl P0 P3 HP0P3); clear HP0P3; rewrite HP0; rewrite HP3; intros HP4; cbn in HP4;
        assert (HP1P3:(P1<>P3)) by discriminate;
        generalize (fp_lemma fp fl Hfpfl P1 P3 HP1P3); clear HP1P3; rewrite HP1; rewrite HP3; intros HP5; cbn in HP5;
          assert (HP0P5:(P0<>P5)) by discriminate;
          generalize (fp_lemma fp fl Hfpfl P0 P5 HP0P5); clear HP0P5; rewrite HP0; rewrite HP5; intros HP6; cbn in HP6;
            case_eq (fp P7); intros HP7; try solve [not_bijP | elim_degen_cases fp fl Hfpfl];
    assert (HP0P7:(P0<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P0 P7 HP0P7); clear HP0P7; rewrite HP0; rewrite HP7; intros HP8; cbn in HP8;
 assert (HP1P7:(P1<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P1 P7 HP1P7); clear HP1P7; rewrite HP1; rewrite HP7; intros HP9; cbn in HP9;
  assert (HP2P7:(P2<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P2 P7 HP2P7); clear HP2P7; rewrite HP2; rewrite HP7; intros HP10; cbn in HP10;
assert (HP3P7:(P3<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P3 P7 HP3P7); clear HP3P7; rewrite HP3; rewrite HP7; intros HP11; cbn in HP11;
assert (HP4P7:(P4<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P4 P7 HP4P7); clear HP4P7; rewrite HP4; rewrite HP7; intros HP12; cbn in HP12;
assert (HP5P7:(P5<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P5 P7 HP5P7); clear HP5P7; rewrite HP5; rewrite HP7; intros HP13; cbn in HP13;
assert (HP6P7:(P6<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P6 P7 HP6P7); clear HP6P7; rewrite HP6; rewrite HP7; intros HP14; cbn in HP14;
assert (Hfl:(fl L0 = l_from_points (fp P0) (fp P1) /\
    fl L1 = l_from_points (fp P0) (fp P3) /\
    fl L2 = l_from_points (fp P0) (fp P5) /\
    fl L3 = l_from_points (fp P0) (fp P7) /\
    fl L4 = l_from_points (fp P0) (fp P10) /\
    fl L5 = l_from_points (fp P0) (fp P11) /\
    fl L6 = l_from_points (fp P0) (fp P13) /\
    fl L7 = l_from_points (fp P1) (fp P4) /\
    fl L8 = l_from_points (fp P1) (fp P8) /\
    fl L9 = l_from_points (fp P1) (fp P12) /\
    fl L10 = l_from_points (fp P1) (fp P7) /\
    fl L11 = l_from_points (fp P1) (fp P13) /\
    fl L12 = l_from_points (fp P1) (fp P3) /\
    fl L13 = l_from_points (fp P2) (fp P7) /\
    fl L14 = l_from_points (fp P2) (fp P11) /\
    fl L15 = l_from_points (fp P2) (fp P3) /\
    fl L16 = l_from_points (fp P2) (fp P12) /\
    fl L17 = l_from_points (fp P2) (fp P4) /\
    fl L18 = l_from_points (fp P2) (fp P8) /\
    fl L19 = l_from_points (fp P3) (fp P10) /\
    fl L20 = l_from_points (fp P3) (fp P8) /\
    fl L21 = l_from_points (fp P3) (fp P9) /\
    fl L22 = l_from_points (fp P3) (fp P7) /\
    fl L23 = l_from_points (fp P4) (fp P9) /\
    fl L24 = l_from_points (fp P4) (fp P8) /\
    fl L25 = l_from_points (fp P4) (fp P10) /\
    fl L26 = l_from_points (fp P4) (fp P7) /\
    fl L27 = l_from_points (fp P5) (fp P8) /\
    fl L28 = l_from_points (fp P5) (fp P7) /\
    fl L29 = l_from_points (fp P5) (fp P9) /\
    fl L30 = l_from_points (fp P5) (fp P10) /\
    fl L31 = l_from_points (fp P6) (fp P7) /\
    fl L32 = l_from_points (fp P6) (fp P8) /\
    fl L33 = l_from_points (fp P6) (fp P9) /\
    fl L34 = l_from_points (fp P6) (fp P10))) by (repeat split; (rewrite <- (is_collineation_l_from_points fp fl Hfpfl); [reflexivity | discriminate]));
rewrite HP0 in Hfl; rewrite HP1 in Hfl; rewrite HP2 in Hfl; rewrite HP3 in Hfl; rewrite HP4 in Hfl;
rewrite HP5 in Hfl; rewrite HP6 in Hfl; rewrite HP7 in Hfl; rewrite HP8 in Hfl; rewrite HP9 in Hfl;
rewrite HP10 in Hfl; rewrite HP11 in Hfl; rewrite HP12 in Hfl; rewrite HP13 in Hfl;
destruct Hfl as [HL0 [HL1 [HL2 [HL3 [HL4 [HL5 [HL6 [HL7 [HL8 [HL9 [HL10 [HL11 [HL12 [HL13 [HL14 [HL15 [HL16 [HL17 [HL18 [HL19 [HL20 [HL21 [HL22 [HL23 [HL24 [HL25 [HL26 [HL27 [HL28 [HL29 [HL30 [HL31 [HL32 [HL33 HL34]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
unfold all_c60.
par:time (repeat (match goal with |- In (?fp, ?fl) ((?fp_i,?fl_i)::_) =>
                let HeqP := fresh in assert (HeqP:fp=fp_i) by (apply fp_ext; intros p; destruct p;
                                       solve [rewrite HP0; reflexivity |
                                              rewrite HP1; reflexivity |
                                              rewrite HP2; reflexivity |
                                              rewrite HP3; reflexivity |
                                              rewrite HP4; reflexivity |
                                              rewrite HP5; reflexivity |
                                              rewrite HP6; reflexivity |
                                              rewrite HP7; reflexivity |
                                              rewrite HP8; reflexivity |
                                              rewrite HP9; reflexivity |
                                              rewrite HP10; reflexivity |
                                              rewrite HP11; reflexivity |
                                              rewrite HP12; reflexivity |
                                              rewrite HP13; reflexivity |
                                              rewrite HP14; reflexivity ]);
                let HeqL := fresh in assert (HeqL:fl=fl_i) by (apply fl_ext; intros l; destruct l;
                                       solve [rewrite HL0; reflexivity |
                                              rewrite HL1; reflexivity |
                                              rewrite HL2; reflexivity |
                                              rewrite HL3; reflexivity |
                                              rewrite HL4; reflexivity |
                                              rewrite HL5; reflexivity |
                                              rewrite HL6; reflexivity |
                                              rewrite HL7; reflexivity |
                                              rewrite HL8; reflexivity |
                                              rewrite HL9; reflexivity |
                                              rewrite HL10; reflexivity |
                                              rewrite HL11; reflexivity |
                                              rewrite HL12; reflexivity |
                                              rewrite HL13; reflexivity |
                                              rewrite HL14; reflexivity |
                                              rewrite HL15; reflexivity |
                                              rewrite HL16; reflexivity |
                                              rewrite HL17; reflexivity |
                                              rewrite HL18; reflexivity |
                                              rewrite HL19; reflexivity |
                                              rewrite HL20; reflexivity |
                                              rewrite HL21; reflexivity |
                                              rewrite HL22; reflexivity |
                                              rewrite HL23; reflexivity |
                                              rewrite HL24; reflexivity |
                                              rewrite HL25; reflexivity |
                                              rewrite HL26; reflexivity |
                                              rewrite HL27; reflexivity |
                                              rewrite HL28; reflexivity |
                                              rewrite HL29; reflexivity |
                                              rewrite HL30; reflexivity |
                                              rewrite HL31; reflexivity |
                                              rewrite HL32; reflexivity |
                                              rewrite HL33; reflexivity |                                              
                                              rewrite HL34; reflexivity ]); rewrite HeqL; rewrite HeqP; apply in_eq
end || apply in_cons)).
Qed.

(* P4 P6 *)
Lemma is_collineations_descr_B_P4_P6 :
  forall fp fl, is_collineation fp fl -> fp P0 = P4 -> fp P1 = P6 -> In (fp,fl) all_c61.
Proof.
  intros fp fl Hfpfl HP0 HP1.
    assert (HP0P1:(P0<>P1)) by discriminate;
    generalize (fp_lemma fp fl Hfpfl P0 P1 HP0P1); clear HP0P1; rewrite HP0; rewrite HP1; intros HP2; cbn in HP2; 
    case_eq (fp P3); intros HP3; try solve [not_bijP | elim_degen_cases fp fl Hfpfl];
    assert (HP0P3:(P0<>P3)) by discriminate;
      generalize (fp_lemma fp fl Hfpfl P0 P3 HP0P3); clear HP0P3; rewrite HP0; rewrite HP3; intros HP4; cbn in HP4;
        assert (HP1P3:(P1<>P3)) by discriminate;
        generalize (fp_lemma fp fl Hfpfl P1 P3 HP1P3); clear HP1P3; rewrite HP1; rewrite HP3; intros HP5; cbn in HP5;
          assert (HP0P5:(P0<>P5)) by discriminate;
          generalize (fp_lemma fp fl Hfpfl P0 P5 HP0P5); clear HP0P5; rewrite HP0; rewrite HP5; intros HP6; cbn in HP6;
            case_eq (fp P7); intros HP7; try solve [not_bijP | elim_degen_cases fp fl Hfpfl];
    assert (HP0P7:(P0<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P0 P7 HP0P7); clear HP0P7; rewrite HP0; rewrite HP7; intros HP8; cbn in HP8;
 assert (HP1P7:(P1<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P1 P7 HP1P7); clear HP1P7; rewrite HP1; rewrite HP7; intros HP9; cbn in HP9;
  assert (HP2P7:(P2<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P2 P7 HP2P7); clear HP2P7; rewrite HP2; rewrite HP7; intros HP10; cbn in HP10;
assert (HP3P7:(P3<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P3 P7 HP3P7); clear HP3P7; rewrite HP3; rewrite HP7; intros HP11; cbn in HP11;
assert (HP4P7:(P4<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P4 P7 HP4P7); clear HP4P7; rewrite HP4; rewrite HP7; intros HP12; cbn in HP12;
assert (HP5P7:(P5<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P5 P7 HP5P7); clear HP5P7; rewrite HP5; rewrite HP7; intros HP13; cbn in HP13;
assert (HP6P7:(P6<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P6 P7 HP6P7); clear HP6P7; rewrite HP6; rewrite HP7; intros HP14; cbn in HP14;
assert (Hfl:(fl L0 = l_from_points (fp P0) (fp P1) /\
    fl L1 = l_from_points (fp P0) (fp P3) /\
    fl L2 = l_from_points (fp P0) (fp P5) /\
    fl L3 = l_from_points (fp P0) (fp P7) /\
    fl L4 = l_from_points (fp P0) (fp P10) /\
    fl L5 = l_from_points (fp P0) (fp P11) /\
    fl L6 = l_from_points (fp P0) (fp P13) /\
    fl L7 = l_from_points (fp P1) (fp P4) /\
    fl L8 = l_from_points (fp P1) (fp P8) /\
    fl L9 = l_from_points (fp P1) (fp P12) /\
    fl L10 = l_from_points (fp P1) (fp P7) /\
    fl L11 = l_from_points (fp P1) (fp P13) /\
    fl L12 = l_from_points (fp P1) (fp P3) /\
    fl L13 = l_from_points (fp P2) (fp P7) /\
    fl L14 = l_from_points (fp P2) (fp P11) /\
    fl L15 = l_from_points (fp P2) (fp P3) /\
    fl L16 = l_from_points (fp P2) (fp P12) /\
    fl L17 = l_from_points (fp P2) (fp P4) /\
    fl L18 = l_from_points (fp P2) (fp P8) /\
    fl L19 = l_from_points (fp P3) (fp P10) /\
    fl L20 = l_from_points (fp P3) (fp P8) /\
    fl L21 = l_from_points (fp P3) (fp P9) /\
    fl L22 = l_from_points (fp P3) (fp P7) /\
    fl L23 = l_from_points (fp P4) (fp P9) /\
    fl L24 = l_from_points (fp P4) (fp P8) /\
    fl L25 = l_from_points (fp P4) (fp P10) /\
    fl L26 = l_from_points (fp P4) (fp P7) /\
    fl L27 = l_from_points (fp P5) (fp P8) /\
    fl L28 = l_from_points (fp P5) (fp P7) /\
    fl L29 = l_from_points (fp P5) (fp P9) /\
    fl L30 = l_from_points (fp P5) (fp P10) /\
    fl L31 = l_from_points (fp P6) (fp P7) /\
    fl L32 = l_from_points (fp P6) (fp P8) /\
    fl L33 = l_from_points (fp P6) (fp P9) /\
    fl L34 = l_from_points (fp P6) (fp P10))) by (repeat split; (rewrite <- (is_collineation_l_from_points fp fl Hfpfl); [reflexivity | discriminate]));
rewrite HP0 in Hfl; rewrite HP1 in Hfl; rewrite HP2 in Hfl; rewrite HP3 in Hfl; rewrite HP4 in Hfl;
rewrite HP5 in Hfl; rewrite HP6 in Hfl; rewrite HP7 in Hfl; rewrite HP8 in Hfl; rewrite HP9 in Hfl;
rewrite HP10 in Hfl; rewrite HP11 in Hfl; rewrite HP12 in Hfl; rewrite HP13 in Hfl;
destruct Hfl as [HL0 [HL1 [HL2 [HL3 [HL4 [HL5 [HL6 [HL7 [HL8 [HL9 [HL10 [HL11 [HL12 [HL13 [HL14 [HL15 [HL16 [HL17 [HL18 [HL19 [HL20 [HL21 [HL22 [HL23 [HL24 [HL25 [HL26 [HL27 [HL28 [HL29 [HL30 [HL31 [HL32 [HL33 HL34]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
unfold all_c61.
par:time (repeat (match goal with |- In (?fp, ?fl) ((?fp_i,?fl_i)::_) =>
                let HeqP := fresh in assert (HeqP:fp=fp_i) by (apply fp_ext; intros p; destruct p;
                                       solve [rewrite HP0; reflexivity |
                                              rewrite HP1; reflexivity |
                                              rewrite HP2; reflexivity |
                                              rewrite HP3; reflexivity |
                                              rewrite HP4; reflexivity |
                                              rewrite HP5; reflexivity |
                                              rewrite HP6; reflexivity |
                                              rewrite HP7; reflexivity |
                                              rewrite HP8; reflexivity |
                                              rewrite HP9; reflexivity |
                                              rewrite HP10; reflexivity |
                                              rewrite HP11; reflexivity |
                                              rewrite HP12; reflexivity |
                                              rewrite HP13; reflexivity |
                                              rewrite HP14; reflexivity ]);
                let HeqL := fresh in assert (HeqL:fl=fl_i) by (apply fl_ext; intros l; destruct l;
                                       solve [rewrite HL0; reflexivity |
                                              rewrite HL1; reflexivity |
                                              rewrite HL2; reflexivity |
                                              rewrite HL3; reflexivity |
                                              rewrite HL4; reflexivity |
                                              rewrite HL5; reflexivity |
                                              rewrite HL6; reflexivity |
                                              rewrite HL7; reflexivity |
                                              rewrite HL8; reflexivity |
                                              rewrite HL9; reflexivity |
                                              rewrite HL10; reflexivity |
                                              rewrite HL11; reflexivity |
                                              rewrite HL12; reflexivity |
                                              rewrite HL13; reflexivity |
                                              rewrite HL14; reflexivity |
                                              rewrite HL15; reflexivity |
                                              rewrite HL16; reflexivity |
                                              rewrite HL17; reflexivity |
                                              rewrite HL18; reflexivity |
                                              rewrite HL19; reflexivity |
                                              rewrite HL20; reflexivity |
                                              rewrite HL21; reflexivity |
                                              rewrite HL22; reflexivity |
                                              rewrite HL23; reflexivity |
                                              rewrite HL24; reflexivity |
                                              rewrite HL25; reflexivity |
                                              rewrite HL26; reflexivity |
                                              rewrite HL27; reflexivity |
                                              rewrite HL28; reflexivity |
                                              rewrite HL29; reflexivity |
                                              rewrite HL30; reflexivity |
                                              rewrite HL31; reflexivity |
                                              rewrite HL32; reflexivity |
                                              rewrite HL33; reflexivity |                                              
                                              rewrite HL34; reflexivity ]); rewrite HeqL; rewrite HeqP; apply in_eq
end || apply in_cons)).
Qed.

(* P4 P7 *)
Lemma is_collineations_descr_B_P4_P7 :
  forall fp fl, is_collineation fp fl -> fp P0 = P4 -> fp P1 = P7 -> In (fp,fl) all_c62.
Proof.
  intros fp fl Hfpfl HP0 HP1.
    assert (HP0P1:(P0<>P1)) by discriminate;
    generalize (fp_lemma fp fl Hfpfl P0 P1 HP0P1); clear HP0P1; rewrite HP0; rewrite HP1; intros HP2; cbn in HP2; 
    case_eq (fp P3); intros HP3; try solve [not_bijP | elim_degen_cases fp fl Hfpfl];
    assert (HP0P3:(P0<>P3)) by discriminate;
      generalize (fp_lemma fp fl Hfpfl P0 P3 HP0P3); clear HP0P3; rewrite HP0; rewrite HP3; intros HP4; cbn in HP4;
        assert (HP1P3:(P1<>P3)) by discriminate;
        generalize (fp_lemma fp fl Hfpfl P1 P3 HP1P3); clear HP1P3; rewrite HP1; rewrite HP3; intros HP5; cbn in HP5;
          assert (HP0P5:(P0<>P5)) by discriminate;
          generalize (fp_lemma fp fl Hfpfl P0 P5 HP0P5); clear HP0P5; rewrite HP0; rewrite HP5; intros HP6; cbn in HP6;
            case_eq (fp P7); intros HP7; try solve [not_bijP | elim_degen_cases fp fl Hfpfl];
    assert (HP0P7:(P0<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P0 P7 HP0P7); clear HP0P7; rewrite HP0; rewrite HP7; intros HP8; cbn in HP8;
 assert (HP1P7:(P1<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P1 P7 HP1P7); clear HP1P7; rewrite HP1; rewrite HP7; intros HP9; cbn in HP9;
  assert (HP2P7:(P2<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P2 P7 HP2P7); clear HP2P7; rewrite HP2; rewrite HP7; intros HP10; cbn in HP10;
assert (HP3P7:(P3<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P3 P7 HP3P7); clear HP3P7; rewrite HP3; rewrite HP7; intros HP11; cbn in HP11;
assert (HP4P7:(P4<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P4 P7 HP4P7); clear HP4P7; rewrite HP4; rewrite HP7; intros HP12; cbn in HP12;
assert (HP5P7:(P5<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P5 P7 HP5P7); clear HP5P7; rewrite HP5; rewrite HP7; intros HP13; cbn in HP13;
assert (HP6P7:(P6<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P6 P7 HP6P7); clear HP6P7; rewrite HP6; rewrite HP7; intros HP14; cbn in HP14;
assert (Hfl:(fl L0 = l_from_points (fp P0) (fp P1) /\
    fl L1 = l_from_points (fp P0) (fp P3) /\
    fl L2 = l_from_points (fp P0) (fp P5) /\
    fl L3 = l_from_points (fp P0) (fp P7) /\
    fl L4 = l_from_points (fp P0) (fp P10) /\
    fl L5 = l_from_points (fp P0) (fp P11) /\
    fl L6 = l_from_points (fp P0) (fp P13) /\
    fl L7 = l_from_points (fp P1) (fp P4) /\
    fl L8 = l_from_points (fp P1) (fp P8) /\
    fl L9 = l_from_points (fp P1) (fp P12) /\
    fl L10 = l_from_points (fp P1) (fp P7) /\
    fl L11 = l_from_points (fp P1) (fp P13) /\
    fl L12 = l_from_points (fp P1) (fp P3) /\
    fl L13 = l_from_points (fp P2) (fp P7) /\
    fl L14 = l_from_points (fp P2) (fp P11) /\
    fl L15 = l_from_points (fp P2) (fp P3) /\
    fl L16 = l_from_points (fp P2) (fp P12) /\
    fl L17 = l_from_points (fp P2) (fp P4) /\
    fl L18 = l_from_points (fp P2) (fp P8) /\
    fl L19 = l_from_points (fp P3) (fp P10) /\
    fl L20 = l_from_points (fp P3) (fp P8) /\
    fl L21 = l_from_points (fp P3) (fp P9) /\
    fl L22 = l_from_points (fp P3) (fp P7) /\
    fl L23 = l_from_points (fp P4) (fp P9) /\
    fl L24 = l_from_points (fp P4) (fp P8) /\
    fl L25 = l_from_points (fp P4) (fp P10) /\
    fl L26 = l_from_points (fp P4) (fp P7) /\
    fl L27 = l_from_points (fp P5) (fp P8) /\
    fl L28 = l_from_points (fp P5) (fp P7) /\
    fl L29 = l_from_points (fp P5) (fp P9) /\
    fl L30 = l_from_points (fp P5) (fp P10) /\
    fl L31 = l_from_points (fp P6) (fp P7) /\
    fl L32 = l_from_points (fp P6) (fp P8) /\
    fl L33 = l_from_points (fp P6) (fp P9) /\
    fl L34 = l_from_points (fp P6) (fp P10))) by (repeat split; (rewrite <- (is_collineation_l_from_points fp fl Hfpfl); [reflexivity | discriminate]));
rewrite HP0 in Hfl; rewrite HP1 in Hfl; rewrite HP2 in Hfl; rewrite HP3 in Hfl; rewrite HP4 in Hfl;
rewrite HP5 in Hfl; rewrite HP6 in Hfl; rewrite HP7 in Hfl; rewrite HP8 in Hfl; rewrite HP9 in Hfl;
rewrite HP10 in Hfl; rewrite HP11 in Hfl; rewrite HP12 in Hfl; rewrite HP13 in Hfl;
destruct Hfl as [HL0 [HL1 [HL2 [HL3 [HL4 [HL5 [HL6 [HL7 [HL8 [HL9 [HL10 [HL11 [HL12 [HL13 [HL14 [HL15 [HL16 [HL17 [HL18 [HL19 [HL20 [HL21 [HL22 [HL23 [HL24 [HL25 [HL26 [HL27 [HL28 [HL29 [HL30 [HL31 [HL32 [HL33 HL34]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
unfold all_c62.
par:time (repeat (match goal with |- In (?fp, ?fl) ((?fp_i,?fl_i)::_) =>
                let HeqP := fresh in assert (HeqP:fp=fp_i) by (apply fp_ext; intros p; destruct p;
                                       solve [rewrite HP0; reflexivity |
                                              rewrite HP1; reflexivity |
                                              rewrite HP2; reflexivity |
                                              rewrite HP3; reflexivity |
                                              rewrite HP4; reflexivity |
                                              rewrite HP5; reflexivity |
                                              rewrite HP6; reflexivity |
                                              rewrite HP7; reflexivity |
                                              rewrite HP8; reflexivity |
                                              rewrite HP9; reflexivity |
                                              rewrite HP10; reflexivity |
                                              rewrite HP11; reflexivity |
                                              rewrite HP12; reflexivity |
                                              rewrite HP13; reflexivity |
                                              rewrite HP14; reflexivity ]);
                let HeqL := fresh in assert (HeqL:fl=fl_i) by (apply fl_ext; intros l; destruct l;
                                       solve [rewrite HL0; reflexivity |
                                              rewrite HL1; reflexivity |
                                              rewrite HL2; reflexivity |
                                              rewrite HL3; reflexivity |
                                              rewrite HL4; reflexivity |
                                              rewrite HL5; reflexivity |
                                              rewrite HL6; reflexivity |
                                              rewrite HL7; reflexivity |
                                              rewrite HL8; reflexivity |
                                              rewrite HL9; reflexivity |
                                              rewrite HL10; reflexivity |
                                              rewrite HL11; reflexivity |
                                              rewrite HL12; reflexivity |
                                              rewrite HL13; reflexivity |
                                              rewrite HL14; reflexivity |
                                              rewrite HL15; reflexivity |
                                              rewrite HL16; reflexivity |
                                              rewrite HL17; reflexivity |
                                              rewrite HL18; reflexivity |
                                              rewrite HL19; reflexivity |
                                              rewrite HL20; reflexivity |
                                              rewrite HL21; reflexivity |
                                              rewrite HL22; reflexivity |
                                              rewrite HL23; reflexivity |
                                              rewrite HL24; reflexivity |
                                              rewrite HL25; reflexivity |
                                              rewrite HL26; reflexivity |
                                              rewrite HL27; reflexivity |
                                              rewrite HL28; reflexivity |
                                              rewrite HL29; reflexivity |
                                              rewrite HL30; reflexivity |
                                              rewrite HL31; reflexivity |
                                              rewrite HL32; reflexivity |
                                              rewrite HL33; reflexivity |                                              
                                              rewrite HL34; reflexivity ]); rewrite HeqL; rewrite HeqP; apply in_eq
end || apply in_cons)).
Qed.

(* P4 P8 *)
Lemma is_collineations_descr_B_P4_P8 :
  forall fp fl, is_collineation fp fl -> fp P0 = P4 -> fp P1 = P8 -> In (fp,fl) all_c63.
Proof.
  intros fp fl Hfpfl HP0 HP1.
    assert (HP0P1:(P0<>P1)) by discriminate;
    generalize (fp_lemma fp fl Hfpfl P0 P1 HP0P1); clear HP0P1; rewrite HP0; rewrite HP1; intros HP2; cbn in HP2; 
    case_eq (fp P3); intros HP3; try solve [not_bijP | elim_degen_cases fp fl Hfpfl];
    assert (HP0P3:(P0<>P3)) by discriminate;
      generalize (fp_lemma fp fl Hfpfl P0 P3 HP0P3); clear HP0P3; rewrite HP0; rewrite HP3; intros HP4; cbn in HP4;
        assert (HP1P3:(P1<>P3)) by discriminate;
        generalize (fp_lemma fp fl Hfpfl P1 P3 HP1P3); clear HP1P3; rewrite HP1; rewrite HP3; intros HP5; cbn in HP5;
          assert (HP0P5:(P0<>P5)) by discriminate;
          generalize (fp_lemma fp fl Hfpfl P0 P5 HP0P5); clear HP0P5; rewrite HP0; rewrite HP5; intros HP6; cbn in HP6;
            case_eq (fp P7); intros HP7; try solve [not_bijP | elim_degen_cases fp fl Hfpfl];
    assert (HP0P7:(P0<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P0 P7 HP0P7); clear HP0P7; rewrite HP0; rewrite HP7; intros HP8; cbn in HP8;
 assert (HP1P7:(P1<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P1 P7 HP1P7); clear HP1P7; rewrite HP1; rewrite HP7; intros HP9; cbn in HP9;
  assert (HP2P7:(P2<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P2 P7 HP2P7); clear HP2P7; rewrite HP2; rewrite HP7; intros HP10; cbn in HP10;
assert (HP3P7:(P3<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P3 P7 HP3P7); clear HP3P7; rewrite HP3; rewrite HP7; intros HP11; cbn in HP11;
assert (HP4P7:(P4<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P4 P7 HP4P7); clear HP4P7; rewrite HP4; rewrite HP7; intros HP12; cbn in HP12;
assert (HP5P7:(P5<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P5 P7 HP5P7); clear HP5P7; rewrite HP5; rewrite HP7; intros HP13; cbn in HP13;
assert (HP6P7:(P6<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P6 P7 HP6P7); clear HP6P7; rewrite HP6; rewrite HP7; intros HP14; cbn in HP14;
assert (Hfl:(fl L0 = l_from_points (fp P0) (fp P1) /\
    fl L1 = l_from_points (fp P0) (fp P3) /\
    fl L2 = l_from_points (fp P0) (fp P5) /\
    fl L3 = l_from_points (fp P0) (fp P7) /\
    fl L4 = l_from_points (fp P0) (fp P10) /\
    fl L5 = l_from_points (fp P0) (fp P11) /\
    fl L6 = l_from_points (fp P0) (fp P13) /\
    fl L7 = l_from_points (fp P1) (fp P4) /\
    fl L8 = l_from_points (fp P1) (fp P8) /\
    fl L9 = l_from_points (fp P1) (fp P12) /\
    fl L10 = l_from_points (fp P1) (fp P7) /\
    fl L11 = l_from_points (fp P1) (fp P13) /\
    fl L12 = l_from_points (fp P1) (fp P3) /\
    fl L13 = l_from_points (fp P2) (fp P7) /\
    fl L14 = l_from_points (fp P2) (fp P11) /\
    fl L15 = l_from_points (fp P2) (fp P3) /\
    fl L16 = l_from_points (fp P2) (fp P12) /\
    fl L17 = l_from_points (fp P2) (fp P4) /\
    fl L18 = l_from_points (fp P2) (fp P8) /\
    fl L19 = l_from_points (fp P3) (fp P10) /\
    fl L20 = l_from_points (fp P3) (fp P8) /\
    fl L21 = l_from_points (fp P3) (fp P9) /\
    fl L22 = l_from_points (fp P3) (fp P7) /\
    fl L23 = l_from_points (fp P4) (fp P9) /\
    fl L24 = l_from_points (fp P4) (fp P8) /\
    fl L25 = l_from_points (fp P4) (fp P10) /\
    fl L26 = l_from_points (fp P4) (fp P7) /\
    fl L27 = l_from_points (fp P5) (fp P8) /\
    fl L28 = l_from_points (fp P5) (fp P7) /\
    fl L29 = l_from_points (fp P5) (fp P9) /\
    fl L30 = l_from_points (fp P5) (fp P10) /\
    fl L31 = l_from_points (fp P6) (fp P7) /\
    fl L32 = l_from_points (fp P6) (fp P8) /\
    fl L33 = l_from_points (fp P6) (fp P9) /\
    fl L34 = l_from_points (fp P6) (fp P10))) by (repeat split; (rewrite <- (is_collineation_l_from_points fp fl Hfpfl); [reflexivity | discriminate]));
rewrite HP0 in Hfl; rewrite HP1 in Hfl; rewrite HP2 in Hfl; rewrite HP3 in Hfl; rewrite HP4 in Hfl;
rewrite HP5 in Hfl; rewrite HP6 in Hfl; rewrite HP7 in Hfl; rewrite HP8 in Hfl; rewrite HP9 in Hfl;
rewrite HP10 in Hfl; rewrite HP11 in Hfl; rewrite HP12 in Hfl; rewrite HP13 in Hfl;
destruct Hfl as [HL0 [HL1 [HL2 [HL3 [HL4 [HL5 [HL6 [HL7 [HL8 [HL9 [HL10 [HL11 [HL12 [HL13 [HL14 [HL15 [HL16 [HL17 [HL18 [HL19 [HL20 [HL21 [HL22 [HL23 [HL24 [HL25 [HL26 [HL27 [HL28 [HL29 [HL30 [HL31 [HL32 [HL33 HL34]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
unfold all_c63.
par:time (repeat (match goal with |- In (?fp, ?fl) ((?fp_i,?fl_i)::_) =>
                let HeqP := fresh in assert (HeqP:fp=fp_i) by (apply fp_ext; intros p; destruct p;
                                       solve [rewrite HP0; reflexivity |
                                              rewrite HP1; reflexivity |
                                              rewrite HP2; reflexivity |
                                              rewrite HP3; reflexivity |
                                              rewrite HP4; reflexivity |
                                              rewrite HP5; reflexivity |
                                              rewrite HP6; reflexivity |
                                              rewrite HP7; reflexivity |
                                              rewrite HP8; reflexivity |
                                              rewrite HP9; reflexivity |
                                              rewrite HP10; reflexivity |
                                              rewrite HP11; reflexivity |
                                              rewrite HP12; reflexivity |
                                              rewrite HP13; reflexivity |
                                              rewrite HP14; reflexivity ]);
                let HeqL := fresh in assert (HeqL:fl=fl_i) by (apply fl_ext; intros l; destruct l;
                                       solve [rewrite HL0; reflexivity |
                                              rewrite HL1; reflexivity |
                                              rewrite HL2; reflexivity |
                                              rewrite HL3; reflexivity |
                                              rewrite HL4; reflexivity |
                                              rewrite HL5; reflexivity |
                                              rewrite HL6; reflexivity |
                                              rewrite HL7; reflexivity |
                                              rewrite HL8; reflexivity |
                                              rewrite HL9; reflexivity |
                                              rewrite HL10; reflexivity |
                                              rewrite HL11; reflexivity |
                                              rewrite HL12; reflexivity |
                                              rewrite HL13; reflexivity |
                                              rewrite HL14; reflexivity |
                                              rewrite HL15; reflexivity |
                                              rewrite HL16; reflexivity |
                                              rewrite HL17; reflexivity |
                                              rewrite HL18; reflexivity |
                                              rewrite HL19; reflexivity |
                                              rewrite HL20; reflexivity |
                                              rewrite HL21; reflexivity |
                                              rewrite HL22; reflexivity |
                                              rewrite HL23; reflexivity |
                                              rewrite HL24; reflexivity |
                                              rewrite HL25; reflexivity |
                                              rewrite HL26; reflexivity |
                                              rewrite HL27; reflexivity |
                                              rewrite HL28; reflexivity |
                                              rewrite HL29; reflexivity |
                                              rewrite HL30; reflexivity |
                                              rewrite HL31; reflexivity |
                                              rewrite HL32; reflexivity |
                                              rewrite HL33; reflexivity |                                              
                                              rewrite HL34; reflexivity ]); rewrite HeqL; rewrite HeqP; apply in_eq
end || apply in_cons)).
Qed.

(* P4 P9 *)
Lemma is_collineations_descr_B_P4_P9 :
  forall fp fl, is_collineation fp fl -> fp P0 = P4 -> fp P1 = P9 -> In (fp,fl) all_c64.
Proof.
  intros fp fl Hfpfl HP0 HP1.
    assert (HP0P1:(P0<>P1)) by discriminate;
    generalize (fp_lemma fp fl Hfpfl P0 P1 HP0P1); clear HP0P1; rewrite HP0; rewrite HP1; intros HP2; cbn in HP2; 
    case_eq (fp P3); intros HP3; try solve [not_bijP | elim_degen_cases fp fl Hfpfl];
    assert (HP0P3:(P0<>P3)) by discriminate;
      generalize (fp_lemma fp fl Hfpfl P0 P3 HP0P3); clear HP0P3; rewrite HP0; rewrite HP3; intros HP4; cbn in HP4;
        assert (HP1P3:(P1<>P3)) by discriminate;
        generalize (fp_lemma fp fl Hfpfl P1 P3 HP1P3); clear HP1P3; rewrite HP1; rewrite HP3; intros HP5; cbn in HP5;
          assert (HP0P5:(P0<>P5)) by discriminate;
          generalize (fp_lemma fp fl Hfpfl P0 P5 HP0P5); clear HP0P5; rewrite HP0; rewrite HP5; intros HP6; cbn in HP6;
            case_eq (fp P7); intros HP7; try solve [not_bijP | elim_degen_cases fp fl Hfpfl];
    assert (HP0P7:(P0<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P0 P7 HP0P7); clear HP0P7; rewrite HP0; rewrite HP7; intros HP8; cbn in HP8;
 assert (HP1P7:(P1<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P1 P7 HP1P7); clear HP1P7; rewrite HP1; rewrite HP7; intros HP9; cbn in HP9;
  assert (HP2P7:(P2<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P2 P7 HP2P7); clear HP2P7; rewrite HP2; rewrite HP7; intros HP10; cbn in HP10;
assert (HP3P7:(P3<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P3 P7 HP3P7); clear HP3P7; rewrite HP3; rewrite HP7; intros HP11; cbn in HP11;
assert (HP4P7:(P4<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P4 P7 HP4P7); clear HP4P7; rewrite HP4; rewrite HP7; intros HP12; cbn in HP12;
assert (HP5P7:(P5<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P5 P7 HP5P7); clear HP5P7; rewrite HP5; rewrite HP7; intros HP13; cbn in HP13;
assert (HP6P7:(P6<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P6 P7 HP6P7); clear HP6P7; rewrite HP6; rewrite HP7; intros HP14; cbn in HP14;
assert (Hfl:(fl L0 = l_from_points (fp P0) (fp P1) /\
    fl L1 = l_from_points (fp P0) (fp P3) /\
    fl L2 = l_from_points (fp P0) (fp P5) /\
    fl L3 = l_from_points (fp P0) (fp P7) /\
    fl L4 = l_from_points (fp P0) (fp P10) /\
    fl L5 = l_from_points (fp P0) (fp P11) /\
    fl L6 = l_from_points (fp P0) (fp P13) /\
    fl L7 = l_from_points (fp P1) (fp P4) /\
    fl L8 = l_from_points (fp P1) (fp P8) /\
    fl L9 = l_from_points (fp P1) (fp P12) /\
    fl L10 = l_from_points (fp P1) (fp P7) /\
    fl L11 = l_from_points (fp P1) (fp P13) /\
    fl L12 = l_from_points (fp P1) (fp P3) /\
    fl L13 = l_from_points (fp P2) (fp P7) /\
    fl L14 = l_from_points (fp P2) (fp P11) /\
    fl L15 = l_from_points (fp P2) (fp P3) /\
    fl L16 = l_from_points (fp P2) (fp P12) /\
    fl L17 = l_from_points (fp P2) (fp P4) /\
    fl L18 = l_from_points (fp P2) (fp P8) /\
    fl L19 = l_from_points (fp P3) (fp P10) /\
    fl L20 = l_from_points (fp P3) (fp P8) /\
    fl L21 = l_from_points (fp P3) (fp P9) /\
    fl L22 = l_from_points (fp P3) (fp P7) /\
    fl L23 = l_from_points (fp P4) (fp P9) /\
    fl L24 = l_from_points (fp P4) (fp P8) /\
    fl L25 = l_from_points (fp P4) (fp P10) /\
    fl L26 = l_from_points (fp P4) (fp P7) /\
    fl L27 = l_from_points (fp P5) (fp P8) /\
    fl L28 = l_from_points (fp P5) (fp P7) /\
    fl L29 = l_from_points (fp P5) (fp P9) /\
    fl L30 = l_from_points (fp P5) (fp P10) /\
    fl L31 = l_from_points (fp P6) (fp P7) /\
    fl L32 = l_from_points (fp P6) (fp P8) /\
    fl L33 = l_from_points (fp P6) (fp P9) /\
    fl L34 = l_from_points (fp P6) (fp P10))) by (repeat split; (rewrite <- (is_collineation_l_from_points fp fl Hfpfl); [reflexivity | discriminate]));
rewrite HP0 in Hfl; rewrite HP1 in Hfl; rewrite HP2 in Hfl; rewrite HP3 in Hfl; rewrite HP4 in Hfl;
rewrite HP5 in Hfl; rewrite HP6 in Hfl; rewrite HP7 in Hfl; rewrite HP8 in Hfl; rewrite HP9 in Hfl;
rewrite HP10 in Hfl; rewrite HP11 in Hfl; rewrite HP12 in Hfl; rewrite HP13 in Hfl;
destruct Hfl as [HL0 [HL1 [HL2 [HL3 [HL4 [HL5 [HL6 [HL7 [HL8 [HL9 [HL10 [HL11 [HL12 [HL13 [HL14 [HL15 [HL16 [HL17 [HL18 [HL19 [HL20 [HL21 [HL22 [HL23 [HL24 [HL25 [HL26 [HL27 [HL28 [HL29 [HL30 [HL31 [HL32 [HL33 HL34]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
unfold all_c64.
par:time (repeat (match goal with |- In (?fp, ?fl) ((?fp_i,?fl_i)::_) =>
                let HeqP := fresh in assert (HeqP:fp=fp_i) by (apply fp_ext; intros p; destruct p;
                                       solve [rewrite HP0; reflexivity |
                                              rewrite HP1; reflexivity |
                                              rewrite HP2; reflexivity |
                                              rewrite HP3; reflexivity |
                                              rewrite HP4; reflexivity |
                                              rewrite HP5; reflexivity |
                                              rewrite HP6; reflexivity |
                                              rewrite HP7; reflexivity |
                                              rewrite HP8; reflexivity |
                                              rewrite HP9; reflexivity |
                                              rewrite HP10; reflexivity |
                                              rewrite HP11; reflexivity |
                                              rewrite HP12; reflexivity |
                                              rewrite HP13; reflexivity |
                                              rewrite HP14; reflexivity ]);
                let HeqL := fresh in assert (HeqL:fl=fl_i) by (apply fl_ext; intros l; destruct l;
                                       solve [rewrite HL0; reflexivity |
                                              rewrite HL1; reflexivity |
                                              rewrite HL2; reflexivity |
                                              rewrite HL3; reflexivity |
                                              rewrite HL4; reflexivity |
                                              rewrite HL5; reflexivity |
                                              rewrite HL6; reflexivity |
                                              rewrite HL7; reflexivity |
                                              rewrite HL8; reflexivity |
                                              rewrite HL9; reflexivity |
                                              rewrite HL10; reflexivity |
                                              rewrite HL11; reflexivity |
                                              rewrite HL12; reflexivity |
                                              rewrite HL13; reflexivity |
                                              rewrite HL14; reflexivity |
                                              rewrite HL15; reflexivity |
                                              rewrite HL16; reflexivity |
                                              rewrite HL17; reflexivity |
                                              rewrite HL18; reflexivity |
                                              rewrite HL19; reflexivity |
                                              rewrite HL20; reflexivity |
                                              rewrite HL21; reflexivity |
                                              rewrite HL22; reflexivity |
                                              rewrite HL23; reflexivity |
                                              rewrite HL24; reflexivity |
                                              rewrite HL25; reflexivity |
                                              rewrite HL26; reflexivity |
                                              rewrite HL27; reflexivity |
                                              rewrite HL28; reflexivity |
                                              rewrite HL29; reflexivity |
                                              rewrite HL30; reflexivity |
                                              rewrite HL31; reflexivity |
                                              rewrite HL32; reflexivity |
                                              rewrite HL33; reflexivity |                                              
                                              rewrite HL34; reflexivity ]); rewrite HeqL; rewrite HeqP; apply in_eq
end || apply in_cons)).
Qed.

(* P4 P10 *)
Lemma is_collineations_descr_B_P4_P10 :
  forall fp fl, is_collineation fp fl -> fp P0 = P4 -> fp P1 = P10 -> In (fp,fl) all_c65.
Proof.
  intros fp fl Hfpfl HP0 HP1.
    assert (HP0P1:(P0<>P1)) by discriminate;
    generalize (fp_lemma fp fl Hfpfl P0 P1 HP0P1); clear HP0P1; rewrite HP0; rewrite HP1; intros HP2; cbn in HP2; 
    case_eq (fp P3); intros HP3; try solve [not_bijP | elim_degen_cases fp fl Hfpfl];
    assert (HP0P3:(P0<>P3)) by discriminate;
      generalize (fp_lemma fp fl Hfpfl P0 P3 HP0P3); clear HP0P3; rewrite HP0; rewrite HP3; intros HP4; cbn in HP4;
        assert (HP1P3:(P1<>P3)) by discriminate;
        generalize (fp_lemma fp fl Hfpfl P1 P3 HP1P3); clear HP1P3; rewrite HP1; rewrite HP3; intros HP5; cbn in HP5;
          assert (HP0P5:(P0<>P5)) by discriminate;
          generalize (fp_lemma fp fl Hfpfl P0 P5 HP0P5); clear HP0P5; rewrite HP0; rewrite HP5; intros HP6; cbn in HP6;
            case_eq (fp P7); intros HP7; try solve [not_bijP | elim_degen_cases fp fl Hfpfl];
    assert (HP0P7:(P0<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P0 P7 HP0P7); clear HP0P7; rewrite HP0; rewrite HP7; intros HP8; cbn in HP8;
 assert (HP1P7:(P1<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P1 P7 HP1P7); clear HP1P7; rewrite HP1; rewrite HP7; intros HP9; cbn in HP9;
  assert (HP2P7:(P2<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P2 P7 HP2P7); clear HP2P7; rewrite HP2; rewrite HP7; intros HP10; cbn in HP10;
assert (HP3P7:(P3<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P3 P7 HP3P7); clear HP3P7; rewrite HP3; rewrite HP7; intros HP11; cbn in HP11;
assert (HP4P7:(P4<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P4 P7 HP4P7); clear HP4P7; rewrite HP4; rewrite HP7; intros HP12; cbn in HP12;
assert (HP5P7:(P5<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P5 P7 HP5P7); clear HP5P7; rewrite HP5; rewrite HP7; intros HP13; cbn in HP13;
assert (HP6P7:(P6<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P6 P7 HP6P7); clear HP6P7; rewrite HP6; rewrite HP7; intros HP14; cbn in HP14;
assert (Hfl:(fl L0 = l_from_points (fp P0) (fp P1) /\
    fl L1 = l_from_points (fp P0) (fp P3) /\
    fl L2 = l_from_points (fp P0) (fp P5) /\
    fl L3 = l_from_points (fp P0) (fp P7) /\
    fl L4 = l_from_points (fp P0) (fp P10) /\
    fl L5 = l_from_points (fp P0) (fp P11) /\
    fl L6 = l_from_points (fp P0) (fp P13) /\
    fl L7 = l_from_points (fp P1) (fp P4) /\
    fl L8 = l_from_points (fp P1) (fp P8) /\
    fl L9 = l_from_points (fp P1) (fp P12) /\
    fl L10 = l_from_points (fp P1) (fp P7) /\
    fl L11 = l_from_points (fp P1) (fp P13) /\
    fl L12 = l_from_points (fp P1) (fp P3) /\
    fl L13 = l_from_points (fp P2) (fp P7) /\
    fl L14 = l_from_points (fp P2) (fp P11) /\
    fl L15 = l_from_points (fp P2) (fp P3) /\
    fl L16 = l_from_points (fp P2) (fp P12) /\
    fl L17 = l_from_points (fp P2) (fp P4) /\
    fl L18 = l_from_points (fp P2) (fp P8) /\
    fl L19 = l_from_points (fp P3) (fp P10) /\
    fl L20 = l_from_points (fp P3) (fp P8) /\
    fl L21 = l_from_points (fp P3) (fp P9) /\
    fl L22 = l_from_points (fp P3) (fp P7) /\
    fl L23 = l_from_points (fp P4) (fp P9) /\
    fl L24 = l_from_points (fp P4) (fp P8) /\
    fl L25 = l_from_points (fp P4) (fp P10) /\
    fl L26 = l_from_points (fp P4) (fp P7) /\
    fl L27 = l_from_points (fp P5) (fp P8) /\
    fl L28 = l_from_points (fp P5) (fp P7) /\
    fl L29 = l_from_points (fp P5) (fp P9) /\
    fl L30 = l_from_points (fp P5) (fp P10) /\
    fl L31 = l_from_points (fp P6) (fp P7) /\
    fl L32 = l_from_points (fp P6) (fp P8) /\
    fl L33 = l_from_points (fp P6) (fp P9) /\
    fl L34 = l_from_points (fp P6) (fp P10))) by (repeat split; (rewrite <- (is_collineation_l_from_points fp fl Hfpfl); [reflexivity | discriminate]));
rewrite HP0 in Hfl; rewrite HP1 in Hfl; rewrite HP2 in Hfl; rewrite HP3 in Hfl; rewrite HP4 in Hfl;
rewrite HP5 in Hfl; rewrite HP6 in Hfl; rewrite HP7 in Hfl; rewrite HP8 in Hfl; rewrite HP9 in Hfl;
rewrite HP10 in Hfl; rewrite HP11 in Hfl; rewrite HP12 in Hfl; rewrite HP13 in Hfl;
destruct Hfl as [HL0 [HL1 [HL2 [HL3 [HL4 [HL5 [HL6 [HL7 [HL8 [HL9 [HL10 [HL11 [HL12 [HL13 [HL14 [HL15 [HL16 [HL17 [HL18 [HL19 [HL20 [HL21 [HL22 [HL23 [HL24 [HL25 [HL26 [HL27 [HL28 [HL29 [HL30 [HL31 [HL32 [HL33 HL34]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
unfold all_c65.
par:time (repeat (match goal with |- In (?fp, ?fl) ((?fp_i,?fl_i)::_) =>
                let HeqP := fresh in assert (HeqP:fp=fp_i) by (apply fp_ext; intros p; destruct p;
                                       solve [rewrite HP0; reflexivity |
                                              rewrite HP1; reflexivity |
                                              rewrite HP2; reflexivity |
                                              rewrite HP3; reflexivity |
                                              rewrite HP4; reflexivity |
                                              rewrite HP5; reflexivity |
                                              rewrite HP6; reflexivity |
                                              rewrite HP7; reflexivity |
                                              rewrite HP8; reflexivity |
                                              rewrite HP9; reflexivity |
                                              rewrite HP10; reflexivity |
                                              rewrite HP11; reflexivity |
                                              rewrite HP12; reflexivity |
                                              rewrite HP13; reflexivity |
                                              rewrite HP14; reflexivity ]);
                let HeqL := fresh in assert (HeqL:fl=fl_i) by (apply fl_ext; intros l; destruct l;
                                       solve [rewrite HL0; reflexivity |
                                              rewrite HL1; reflexivity |
                                              rewrite HL2; reflexivity |
                                              rewrite HL3; reflexivity |
                                              rewrite HL4; reflexivity |
                                              rewrite HL5; reflexivity |
                                              rewrite HL6; reflexivity |
                                              rewrite HL7; reflexivity |
                                              rewrite HL8; reflexivity |
                                              rewrite HL9; reflexivity |
                                              rewrite HL10; reflexivity |
                                              rewrite HL11; reflexivity |
                                              rewrite HL12; reflexivity |
                                              rewrite HL13; reflexivity |
                                              rewrite HL14; reflexivity |
                                              rewrite HL15; reflexivity |
                                              rewrite HL16; reflexivity |
                                              rewrite HL17; reflexivity |
                                              rewrite HL18; reflexivity |
                                              rewrite HL19; reflexivity |
                                              rewrite HL20; reflexivity |
                                              rewrite HL21; reflexivity |
                                              rewrite HL22; reflexivity |
                                              rewrite HL23; reflexivity |
                                              rewrite HL24; reflexivity |
                                              rewrite HL25; reflexivity |
                                              rewrite HL26; reflexivity |
                                              rewrite HL27; reflexivity |
                                              rewrite HL28; reflexivity |
                                              rewrite HL29; reflexivity |
                                              rewrite HL30; reflexivity |
                                              rewrite HL31; reflexivity |
                                              rewrite HL32; reflexivity |
                                              rewrite HL33; reflexivity |                                              
                                              rewrite HL34; reflexivity ]); rewrite HeqL; rewrite HeqP; apply in_eq
end || apply in_cons)).
Qed.

(* P4 P11 *)
Lemma is_collineations_descr_B_P4_P11 :
  forall fp fl, is_collineation fp fl -> fp P0 = P4 -> fp P1 = P11 -> In (fp,fl) all_c66.
Proof.
  intros fp fl Hfpfl HP0 HP1.
    assert (HP0P1:(P0<>P1)) by discriminate;
    generalize (fp_lemma fp fl Hfpfl P0 P1 HP0P1); clear HP0P1; rewrite HP0; rewrite HP1; intros HP2; cbn in HP2; 
    case_eq (fp P3); intros HP3; try solve [not_bijP | elim_degen_cases fp fl Hfpfl];
    assert (HP0P3:(P0<>P3)) by discriminate;
      generalize (fp_lemma fp fl Hfpfl P0 P3 HP0P3); clear HP0P3; rewrite HP0; rewrite HP3; intros HP4; cbn in HP4;
        assert (HP1P3:(P1<>P3)) by discriminate;
        generalize (fp_lemma fp fl Hfpfl P1 P3 HP1P3); clear HP1P3; rewrite HP1; rewrite HP3; intros HP5; cbn in HP5;
          assert (HP0P5:(P0<>P5)) by discriminate;
          generalize (fp_lemma fp fl Hfpfl P0 P5 HP0P5); clear HP0P5; rewrite HP0; rewrite HP5; intros HP6; cbn in HP6;
            case_eq (fp P7); intros HP7; try solve [not_bijP | elim_degen_cases fp fl Hfpfl];
    assert (HP0P7:(P0<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P0 P7 HP0P7); clear HP0P7; rewrite HP0; rewrite HP7; intros HP8; cbn in HP8;
 assert (HP1P7:(P1<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P1 P7 HP1P7); clear HP1P7; rewrite HP1; rewrite HP7; intros HP9; cbn in HP9;
  assert (HP2P7:(P2<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P2 P7 HP2P7); clear HP2P7; rewrite HP2; rewrite HP7; intros HP10; cbn in HP10;
assert (HP3P7:(P3<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P3 P7 HP3P7); clear HP3P7; rewrite HP3; rewrite HP7; intros HP11; cbn in HP11;
assert (HP4P7:(P4<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P4 P7 HP4P7); clear HP4P7; rewrite HP4; rewrite HP7; intros HP12; cbn in HP12;
assert (HP5P7:(P5<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P5 P7 HP5P7); clear HP5P7; rewrite HP5; rewrite HP7; intros HP13; cbn in HP13;
assert (HP6P7:(P6<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P6 P7 HP6P7); clear HP6P7; rewrite HP6; rewrite HP7; intros HP14; cbn in HP14;
assert (Hfl:(fl L0 = l_from_points (fp P0) (fp P1) /\
    fl L1 = l_from_points (fp P0) (fp P3) /\
    fl L2 = l_from_points (fp P0) (fp P5) /\
    fl L3 = l_from_points (fp P0) (fp P7) /\
    fl L4 = l_from_points (fp P0) (fp P10) /\
    fl L5 = l_from_points (fp P0) (fp P11) /\
    fl L6 = l_from_points (fp P0) (fp P13) /\
    fl L7 = l_from_points (fp P1) (fp P4) /\
    fl L8 = l_from_points (fp P1) (fp P8) /\
    fl L9 = l_from_points (fp P1) (fp P12) /\
    fl L10 = l_from_points (fp P1) (fp P7) /\
    fl L11 = l_from_points (fp P1) (fp P13) /\
    fl L12 = l_from_points (fp P1) (fp P3) /\
    fl L13 = l_from_points (fp P2) (fp P7) /\
    fl L14 = l_from_points (fp P2) (fp P11) /\
    fl L15 = l_from_points (fp P2) (fp P3) /\
    fl L16 = l_from_points (fp P2) (fp P12) /\
    fl L17 = l_from_points (fp P2) (fp P4) /\
    fl L18 = l_from_points (fp P2) (fp P8) /\
    fl L19 = l_from_points (fp P3) (fp P10) /\
    fl L20 = l_from_points (fp P3) (fp P8) /\
    fl L21 = l_from_points (fp P3) (fp P9) /\
    fl L22 = l_from_points (fp P3) (fp P7) /\
    fl L23 = l_from_points (fp P4) (fp P9) /\
    fl L24 = l_from_points (fp P4) (fp P8) /\
    fl L25 = l_from_points (fp P4) (fp P10) /\
    fl L26 = l_from_points (fp P4) (fp P7) /\
    fl L27 = l_from_points (fp P5) (fp P8) /\
    fl L28 = l_from_points (fp P5) (fp P7) /\
    fl L29 = l_from_points (fp P5) (fp P9) /\
    fl L30 = l_from_points (fp P5) (fp P10) /\
    fl L31 = l_from_points (fp P6) (fp P7) /\
    fl L32 = l_from_points (fp P6) (fp P8) /\
    fl L33 = l_from_points (fp P6) (fp P9) /\
    fl L34 = l_from_points (fp P6) (fp P10))) by (repeat split; (rewrite <- (is_collineation_l_from_points fp fl Hfpfl); [reflexivity | discriminate]));
rewrite HP0 in Hfl; rewrite HP1 in Hfl; rewrite HP2 in Hfl; rewrite HP3 in Hfl; rewrite HP4 in Hfl;
rewrite HP5 in Hfl; rewrite HP6 in Hfl; rewrite HP7 in Hfl; rewrite HP8 in Hfl; rewrite HP9 in Hfl;
rewrite HP10 in Hfl; rewrite HP11 in Hfl; rewrite HP12 in Hfl; rewrite HP13 in Hfl;
destruct Hfl as [HL0 [HL1 [HL2 [HL3 [HL4 [HL5 [HL6 [HL7 [HL8 [HL9 [HL10 [HL11 [HL12 [HL13 [HL14 [HL15 [HL16 [HL17 [HL18 [HL19 [HL20 [HL21 [HL22 [HL23 [HL24 [HL25 [HL26 [HL27 [HL28 [HL29 [HL30 [HL31 [HL32 [HL33 HL34]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
unfold all_c66.
par:time (repeat (match goal with |- In (?fp, ?fl) ((?fp_i,?fl_i)::_) =>
                let HeqP := fresh in assert (HeqP:fp=fp_i) by (apply fp_ext; intros p; destruct p;
                                       solve [rewrite HP0; reflexivity |
                                              rewrite HP1; reflexivity |
                                              rewrite HP2; reflexivity |
                                              rewrite HP3; reflexivity |
                                              rewrite HP4; reflexivity |
                                              rewrite HP5; reflexivity |
                                              rewrite HP6; reflexivity |
                                              rewrite HP7; reflexivity |
                                              rewrite HP8; reflexivity |
                                              rewrite HP9; reflexivity |
                                              rewrite HP10; reflexivity |
                                              rewrite HP11; reflexivity |
                                              rewrite HP12; reflexivity |
                                              rewrite HP13; reflexivity |
                                              rewrite HP14; reflexivity ]);
                let HeqL := fresh in assert (HeqL:fl=fl_i) by (apply fl_ext; intros l; destruct l;
                                       solve [rewrite HL0; reflexivity |
                                              rewrite HL1; reflexivity |
                                              rewrite HL2; reflexivity |
                                              rewrite HL3; reflexivity |
                                              rewrite HL4; reflexivity |
                                              rewrite HL5; reflexivity |
                                              rewrite HL6; reflexivity |
                                              rewrite HL7; reflexivity |
                                              rewrite HL8; reflexivity |
                                              rewrite HL9; reflexivity |
                                              rewrite HL10; reflexivity |
                                              rewrite HL11; reflexivity |
                                              rewrite HL12; reflexivity |
                                              rewrite HL13; reflexivity |
                                              rewrite HL14; reflexivity |
                                              rewrite HL15; reflexivity |
                                              rewrite HL16; reflexivity |
                                              rewrite HL17; reflexivity |
                                              rewrite HL18; reflexivity |
                                              rewrite HL19; reflexivity |
                                              rewrite HL20; reflexivity |
                                              rewrite HL21; reflexivity |
                                              rewrite HL22; reflexivity |
                                              rewrite HL23; reflexivity |
                                              rewrite HL24; reflexivity |
                                              rewrite HL25; reflexivity |
                                              rewrite HL26; reflexivity |
                                              rewrite HL27; reflexivity |
                                              rewrite HL28; reflexivity |
                                              rewrite HL29; reflexivity |
                                              rewrite HL30; reflexivity |
                                              rewrite HL31; reflexivity |
                                              rewrite HL32; reflexivity |
                                              rewrite HL33; reflexivity |                                              
                                              rewrite HL34; reflexivity ]); rewrite HeqL; rewrite HeqP; apply in_eq
end || apply in_cons)).
Qed.

(* P4 P12 *)
Lemma is_collineations_descr_B_P4_P12 :
  forall fp fl, is_collineation fp fl -> fp P0 = P4 -> fp P1 = P12 -> In (fp,fl) all_c67.
Proof.
  intros fp fl Hfpfl HP0 HP1.
    assert (HP0P1:(P0<>P1)) by discriminate;
    generalize (fp_lemma fp fl Hfpfl P0 P1 HP0P1); clear HP0P1; rewrite HP0; rewrite HP1; intros HP2; cbn in HP2; 
    case_eq (fp P3); intros HP3; try solve [not_bijP | elim_degen_cases fp fl Hfpfl];
    assert (HP0P3:(P0<>P3)) by discriminate;
      generalize (fp_lemma fp fl Hfpfl P0 P3 HP0P3); clear HP0P3; rewrite HP0; rewrite HP3; intros HP4; cbn in HP4;
        assert (HP1P3:(P1<>P3)) by discriminate;
        generalize (fp_lemma fp fl Hfpfl P1 P3 HP1P3); clear HP1P3; rewrite HP1; rewrite HP3; intros HP5; cbn in HP5;
          assert (HP0P5:(P0<>P5)) by discriminate;
          generalize (fp_lemma fp fl Hfpfl P0 P5 HP0P5); clear HP0P5; rewrite HP0; rewrite HP5; intros HP6; cbn in HP6;
            case_eq (fp P7); intros HP7; try solve [not_bijP | elim_degen_cases fp fl Hfpfl];
    assert (HP0P7:(P0<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P0 P7 HP0P7); clear HP0P7; rewrite HP0; rewrite HP7; intros HP8; cbn in HP8;
 assert (HP1P7:(P1<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P1 P7 HP1P7); clear HP1P7; rewrite HP1; rewrite HP7; intros HP9; cbn in HP9;
  assert (HP2P7:(P2<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P2 P7 HP2P7); clear HP2P7; rewrite HP2; rewrite HP7; intros HP10; cbn in HP10;
assert (HP3P7:(P3<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P3 P7 HP3P7); clear HP3P7; rewrite HP3; rewrite HP7; intros HP11; cbn in HP11;
assert (HP4P7:(P4<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P4 P7 HP4P7); clear HP4P7; rewrite HP4; rewrite HP7; intros HP12; cbn in HP12;
assert (HP5P7:(P5<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P5 P7 HP5P7); clear HP5P7; rewrite HP5; rewrite HP7; intros HP13; cbn in HP13;
assert (HP6P7:(P6<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P6 P7 HP6P7); clear HP6P7; rewrite HP6; rewrite HP7; intros HP14; cbn in HP14;
assert (Hfl:(fl L0 = l_from_points (fp P0) (fp P1) /\
    fl L1 = l_from_points (fp P0) (fp P3) /\
    fl L2 = l_from_points (fp P0) (fp P5) /\
    fl L3 = l_from_points (fp P0) (fp P7) /\
    fl L4 = l_from_points (fp P0) (fp P10) /\
    fl L5 = l_from_points (fp P0) (fp P11) /\
    fl L6 = l_from_points (fp P0) (fp P13) /\
    fl L7 = l_from_points (fp P1) (fp P4) /\
    fl L8 = l_from_points (fp P1) (fp P8) /\
    fl L9 = l_from_points (fp P1) (fp P12) /\
    fl L10 = l_from_points (fp P1) (fp P7) /\
    fl L11 = l_from_points (fp P1) (fp P13) /\
    fl L12 = l_from_points (fp P1) (fp P3) /\
    fl L13 = l_from_points (fp P2) (fp P7) /\
    fl L14 = l_from_points (fp P2) (fp P11) /\
    fl L15 = l_from_points (fp P2) (fp P3) /\
    fl L16 = l_from_points (fp P2) (fp P12) /\
    fl L17 = l_from_points (fp P2) (fp P4) /\
    fl L18 = l_from_points (fp P2) (fp P8) /\
    fl L19 = l_from_points (fp P3) (fp P10) /\
    fl L20 = l_from_points (fp P3) (fp P8) /\
    fl L21 = l_from_points (fp P3) (fp P9) /\
    fl L22 = l_from_points (fp P3) (fp P7) /\
    fl L23 = l_from_points (fp P4) (fp P9) /\
    fl L24 = l_from_points (fp P4) (fp P8) /\
    fl L25 = l_from_points (fp P4) (fp P10) /\
    fl L26 = l_from_points (fp P4) (fp P7) /\
    fl L27 = l_from_points (fp P5) (fp P8) /\
    fl L28 = l_from_points (fp P5) (fp P7) /\
    fl L29 = l_from_points (fp P5) (fp P9) /\
    fl L30 = l_from_points (fp P5) (fp P10) /\
    fl L31 = l_from_points (fp P6) (fp P7) /\
    fl L32 = l_from_points (fp P6) (fp P8) /\
    fl L33 = l_from_points (fp P6) (fp P9) /\
    fl L34 = l_from_points (fp P6) (fp P10))) by (repeat split; (rewrite <- (is_collineation_l_from_points fp fl Hfpfl); [reflexivity | discriminate]));
rewrite HP0 in Hfl; rewrite HP1 in Hfl; rewrite HP2 in Hfl; rewrite HP3 in Hfl; rewrite HP4 in Hfl;
rewrite HP5 in Hfl; rewrite HP6 in Hfl; rewrite HP7 in Hfl; rewrite HP8 in Hfl; rewrite HP9 in Hfl;
rewrite HP10 in Hfl; rewrite HP11 in Hfl; rewrite HP12 in Hfl; rewrite HP13 in Hfl;
destruct Hfl as [HL0 [HL1 [HL2 [HL3 [HL4 [HL5 [HL6 [HL7 [HL8 [HL9 [HL10 [HL11 [HL12 [HL13 [HL14 [HL15 [HL16 [HL17 [HL18 [HL19 [HL20 [HL21 [HL22 [HL23 [HL24 [HL25 [HL26 [HL27 [HL28 [HL29 [HL30 [HL31 [HL32 [HL33 HL34]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
unfold all_c67.
par:time (repeat (match goal with |- In (?fp, ?fl) ((?fp_i,?fl_i)::_) =>
                let HeqP := fresh in assert (HeqP:fp=fp_i) by (apply fp_ext; intros p; destruct p;
                                       solve [rewrite HP0; reflexivity |
                                              rewrite HP1; reflexivity |
                                              rewrite HP2; reflexivity |
                                              rewrite HP3; reflexivity |
                                              rewrite HP4; reflexivity |
                                              rewrite HP5; reflexivity |
                                              rewrite HP6; reflexivity |
                                              rewrite HP7; reflexivity |
                                              rewrite HP8; reflexivity |
                                              rewrite HP9; reflexivity |
                                              rewrite HP10; reflexivity |
                                              rewrite HP11; reflexivity |
                                              rewrite HP12; reflexivity |
                                              rewrite HP13; reflexivity |
                                              rewrite HP14; reflexivity ]);
                let HeqL := fresh in assert (HeqL:fl=fl_i) by (apply fl_ext; intros l; destruct l;
                                       solve [rewrite HL0; reflexivity |
                                              rewrite HL1; reflexivity |
                                              rewrite HL2; reflexivity |
                                              rewrite HL3; reflexivity |
                                              rewrite HL4; reflexivity |
                                              rewrite HL5; reflexivity |
                                              rewrite HL6; reflexivity |
                                              rewrite HL7; reflexivity |
                                              rewrite HL8; reflexivity |
                                              rewrite HL9; reflexivity |
                                              rewrite HL10; reflexivity |
                                              rewrite HL11; reflexivity |
                                              rewrite HL12; reflexivity |
                                              rewrite HL13; reflexivity |
                                              rewrite HL14; reflexivity |
                                              rewrite HL15; reflexivity |
                                              rewrite HL16; reflexivity |
                                              rewrite HL17; reflexivity |
                                              rewrite HL18; reflexivity |
                                              rewrite HL19; reflexivity |
                                              rewrite HL20; reflexivity |
                                              rewrite HL21; reflexivity |
                                              rewrite HL22; reflexivity |
                                              rewrite HL23; reflexivity |
                                              rewrite HL24; reflexivity |
                                              rewrite HL25; reflexivity |
                                              rewrite HL26; reflexivity |
                                              rewrite HL27; reflexivity |
                                              rewrite HL28; reflexivity |
                                              rewrite HL29; reflexivity |
                                              rewrite HL30; reflexivity |
                                              rewrite HL31; reflexivity |
                                              rewrite HL32; reflexivity |
                                              rewrite HL33; reflexivity |                                              
                                              rewrite HL34; reflexivity ]); rewrite HeqL; rewrite HeqP; apply in_eq
end || apply in_cons)).
Qed.

(* P4 P13 *)
Lemma is_collineations_descr_B_P4_P13 :
  forall fp fl, is_collineation fp fl -> fp P0 = P4 -> fp P1 = P13 -> In (fp,fl) all_c68.
Proof.
  intros fp fl Hfpfl HP0 HP1.
    assert (HP0P1:(P0<>P1)) by discriminate;
    generalize (fp_lemma fp fl Hfpfl P0 P1 HP0P1); clear HP0P1; rewrite HP0; rewrite HP1; intros HP2; cbn in HP2; 
    case_eq (fp P3); intros HP3; try solve [not_bijP | elim_degen_cases fp fl Hfpfl];
    assert (HP0P3:(P0<>P3)) by discriminate;
      generalize (fp_lemma fp fl Hfpfl P0 P3 HP0P3); clear HP0P3; rewrite HP0; rewrite HP3; intros HP4; cbn in HP4;
        assert (HP1P3:(P1<>P3)) by discriminate;
        generalize (fp_lemma fp fl Hfpfl P1 P3 HP1P3); clear HP1P3; rewrite HP1; rewrite HP3; intros HP5; cbn in HP5;
          assert (HP0P5:(P0<>P5)) by discriminate;
          generalize (fp_lemma fp fl Hfpfl P0 P5 HP0P5); clear HP0P5; rewrite HP0; rewrite HP5; intros HP6; cbn in HP6;
            case_eq (fp P7); intros HP7; try solve [not_bijP | elim_degen_cases fp fl Hfpfl];
    assert (HP0P7:(P0<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P0 P7 HP0P7); clear HP0P7; rewrite HP0; rewrite HP7; intros HP8; cbn in HP8;
 assert (HP1P7:(P1<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P1 P7 HP1P7); clear HP1P7; rewrite HP1; rewrite HP7; intros HP9; cbn in HP9;
  assert (HP2P7:(P2<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P2 P7 HP2P7); clear HP2P7; rewrite HP2; rewrite HP7; intros HP10; cbn in HP10;
assert (HP3P7:(P3<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P3 P7 HP3P7); clear HP3P7; rewrite HP3; rewrite HP7; intros HP11; cbn in HP11;
assert (HP4P7:(P4<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P4 P7 HP4P7); clear HP4P7; rewrite HP4; rewrite HP7; intros HP12; cbn in HP12;
assert (HP5P7:(P5<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P5 P7 HP5P7); clear HP5P7; rewrite HP5; rewrite HP7; intros HP13; cbn in HP13;
assert (HP6P7:(P6<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P6 P7 HP6P7); clear HP6P7; rewrite HP6; rewrite HP7; intros HP14; cbn in HP14;
assert (Hfl:(fl L0 = l_from_points (fp P0) (fp P1) /\
    fl L1 = l_from_points (fp P0) (fp P3) /\
    fl L2 = l_from_points (fp P0) (fp P5) /\
    fl L3 = l_from_points (fp P0) (fp P7) /\
    fl L4 = l_from_points (fp P0) (fp P10) /\
    fl L5 = l_from_points (fp P0) (fp P11) /\
    fl L6 = l_from_points (fp P0) (fp P13) /\
    fl L7 = l_from_points (fp P1) (fp P4) /\
    fl L8 = l_from_points (fp P1) (fp P8) /\
    fl L9 = l_from_points (fp P1) (fp P12) /\
    fl L10 = l_from_points (fp P1) (fp P7) /\
    fl L11 = l_from_points (fp P1) (fp P13) /\
    fl L12 = l_from_points (fp P1) (fp P3) /\
    fl L13 = l_from_points (fp P2) (fp P7) /\
    fl L14 = l_from_points (fp P2) (fp P11) /\
    fl L15 = l_from_points (fp P2) (fp P3) /\
    fl L16 = l_from_points (fp P2) (fp P12) /\
    fl L17 = l_from_points (fp P2) (fp P4) /\
    fl L18 = l_from_points (fp P2) (fp P8) /\
    fl L19 = l_from_points (fp P3) (fp P10) /\
    fl L20 = l_from_points (fp P3) (fp P8) /\
    fl L21 = l_from_points (fp P3) (fp P9) /\
    fl L22 = l_from_points (fp P3) (fp P7) /\
    fl L23 = l_from_points (fp P4) (fp P9) /\
    fl L24 = l_from_points (fp P4) (fp P8) /\
    fl L25 = l_from_points (fp P4) (fp P10) /\
    fl L26 = l_from_points (fp P4) (fp P7) /\
    fl L27 = l_from_points (fp P5) (fp P8) /\
    fl L28 = l_from_points (fp P5) (fp P7) /\
    fl L29 = l_from_points (fp P5) (fp P9) /\
    fl L30 = l_from_points (fp P5) (fp P10) /\
    fl L31 = l_from_points (fp P6) (fp P7) /\
    fl L32 = l_from_points (fp P6) (fp P8) /\
    fl L33 = l_from_points (fp P6) (fp P9) /\
    fl L34 = l_from_points (fp P6) (fp P10))) by (repeat split; (rewrite <- (is_collineation_l_from_points fp fl Hfpfl); [reflexivity | discriminate]));
rewrite HP0 in Hfl; rewrite HP1 in Hfl; rewrite HP2 in Hfl; rewrite HP3 in Hfl; rewrite HP4 in Hfl;
rewrite HP5 in Hfl; rewrite HP6 in Hfl; rewrite HP7 in Hfl; rewrite HP8 in Hfl; rewrite HP9 in Hfl;
rewrite HP10 in Hfl; rewrite HP11 in Hfl; rewrite HP12 in Hfl; rewrite HP13 in Hfl;
destruct Hfl as [HL0 [HL1 [HL2 [HL3 [HL4 [HL5 [HL6 [HL7 [HL8 [HL9 [HL10 [HL11 [HL12 [HL13 [HL14 [HL15 [HL16 [HL17 [HL18 [HL19 [HL20 [HL21 [HL22 [HL23 [HL24 [HL25 [HL26 [HL27 [HL28 [HL29 [HL30 [HL31 [HL32 [HL33 HL34]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
unfold all_c68.
par:time (repeat (match goal with |- In (?fp, ?fl) ((?fp_i,?fl_i)::_) =>
                let HeqP := fresh in assert (HeqP:fp=fp_i) by (apply fp_ext; intros p; destruct p;
                                       solve [rewrite HP0; reflexivity |
                                              rewrite HP1; reflexivity |
                                              rewrite HP2; reflexivity |
                                              rewrite HP3; reflexivity |
                                              rewrite HP4; reflexivity |
                                              rewrite HP5; reflexivity |
                                              rewrite HP6; reflexivity |
                                              rewrite HP7; reflexivity |
                                              rewrite HP8; reflexivity |
                                              rewrite HP9; reflexivity |
                                              rewrite HP10; reflexivity |
                                              rewrite HP11; reflexivity |
                                              rewrite HP12; reflexivity |
                                              rewrite HP13; reflexivity |
                                              rewrite HP14; reflexivity ]);
                let HeqL := fresh in assert (HeqL:fl=fl_i) by (apply fl_ext; intros l; destruct l;
                                       solve [rewrite HL0; reflexivity |
                                              rewrite HL1; reflexivity |
                                              rewrite HL2; reflexivity |
                                              rewrite HL3; reflexivity |
                                              rewrite HL4; reflexivity |
                                              rewrite HL5; reflexivity |
                                              rewrite HL6; reflexivity |
                                              rewrite HL7; reflexivity |
                                              rewrite HL8; reflexivity |
                                              rewrite HL9; reflexivity |
                                              rewrite HL10; reflexivity |
                                              rewrite HL11; reflexivity |
                                              rewrite HL12; reflexivity |
                                              rewrite HL13; reflexivity |
                                              rewrite HL14; reflexivity |
                                              rewrite HL15; reflexivity |
                                              rewrite HL16; reflexivity |
                                              rewrite HL17; reflexivity |
                                              rewrite HL18; reflexivity |
                                              rewrite HL19; reflexivity |
                                              rewrite HL20; reflexivity |
                                              rewrite HL21; reflexivity |
                                              rewrite HL22; reflexivity |
                                              rewrite HL23; reflexivity |
                                              rewrite HL24; reflexivity |
                                              rewrite HL25; reflexivity |
                                              rewrite HL26; reflexivity |
                                              rewrite HL27; reflexivity |
                                              rewrite HL28; reflexivity |
                                              rewrite HL29; reflexivity |
                                              rewrite HL30; reflexivity |
                                              rewrite HL31; reflexivity |
                                              rewrite HL32; reflexivity |
                                              rewrite HL33; reflexivity |                                              
                                              rewrite HL34; reflexivity ]); rewrite HeqL; rewrite HeqP; apply in_eq
end || apply in_cons)).
Qed.

(* P4 P14 *)
Lemma is_collineations_descr_B_P4_P14 :
  forall fp fl, is_collineation fp fl -> fp P0 = P4 -> fp P1 = P14 -> In (fp,fl) all_c69.
Proof.
  intros fp fl Hfpfl HP0 HP1.
    assert (HP0P1:(P0<>P1)) by discriminate;
    generalize (fp_lemma fp fl Hfpfl P0 P1 HP0P1); clear HP0P1; rewrite HP0; rewrite HP1; intros HP2; cbn in HP2; 
    case_eq (fp P3); intros HP3; try solve [not_bijP | elim_degen_cases fp fl Hfpfl];
    assert (HP0P3:(P0<>P3)) by discriminate;
      generalize (fp_lemma fp fl Hfpfl P0 P3 HP0P3); clear HP0P3; rewrite HP0; rewrite HP3; intros HP4; cbn in HP4;
        assert (HP1P3:(P1<>P3)) by discriminate;
        generalize (fp_lemma fp fl Hfpfl P1 P3 HP1P3); clear HP1P3; rewrite HP1; rewrite HP3; intros HP5; cbn in HP5;
          assert (HP0P5:(P0<>P5)) by discriminate;
          generalize (fp_lemma fp fl Hfpfl P0 P5 HP0P5); clear HP0P5; rewrite HP0; rewrite HP5; intros HP6; cbn in HP6;
            case_eq (fp P7); intros HP7; try solve [not_bijP | elim_degen_cases fp fl Hfpfl];
    assert (HP0P7:(P0<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P0 P7 HP0P7); clear HP0P7; rewrite HP0; rewrite HP7; intros HP8; cbn in HP8;
 assert (HP1P7:(P1<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P1 P7 HP1P7); clear HP1P7; rewrite HP1; rewrite HP7; intros HP9; cbn in HP9;
  assert (HP2P7:(P2<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P2 P7 HP2P7); clear HP2P7; rewrite HP2; rewrite HP7; intros HP10; cbn in HP10;
assert (HP3P7:(P3<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P3 P7 HP3P7); clear HP3P7; rewrite HP3; rewrite HP7; intros HP11; cbn in HP11;
assert (HP4P7:(P4<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P4 P7 HP4P7); clear HP4P7; rewrite HP4; rewrite HP7; intros HP12; cbn in HP12;
assert (HP5P7:(P5<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P5 P7 HP5P7); clear HP5P7; rewrite HP5; rewrite HP7; intros HP13; cbn in HP13;
assert (HP6P7:(P6<>P7)) by discriminate;
  generalize (fp_lemma fp fl Hfpfl P6 P7 HP6P7); clear HP6P7; rewrite HP6; rewrite HP7; intros HP14; cbn in HP14;
assert (Hfl:(fl L0 = l_from_points (fp P0) (fp P1) /\
    fl L1 = l_from_points (fp P0) (fp P3) /\
    fl L2 = l_from_points (fp P0) (fp P5) /\
    fl L3 = l_from_points (fp P0) (fp P7) /\
    fl L4 = l_from_points (fp P0) (fp P10) /\
    fl L5 = l_from_points (fp P0) (fp P11) /\
    fl L6 = l_from_points (fp P0) (fp P13) /\
    fl L7 = l_from_points (fp P1) (fp P4) /\
    fl L8 = l_from_points (fp P1) (fp P8) /\
    fl L9 = l_from_points (fp P1) (fp P12) /\
    fl L10 = l_from_points (fp P1) (fp P7) /\
    fl L11 = l_from_points (fp P1) (fp P13) /\
    fl L12 = l_from_points (fp P1) (fp P3) /\
    fl L13 = l_from_points (fp P2) (fp P7) /\
    fl L14 = l_from_points (fp P2) (fp P11) /\
    fl L15 = l_from_points (fp P2) (fp P3) /\
    fl L16 = l_from_points (fp P2) (fp P12) /\
    fl L17 = l_from_points (fp P2) (fp P4) /\
    fl L18 = l_from_points (fp P2) (fp P8) /\
    fl L19 = l_from_points (fp P3) (fp P10) /\
    fl L20 = l_from_points (fp P3) (fp P8) /\
    fl L21 = l_from_points (fp P3) (fp P9) /\
    fl L22 = l_from_points (fp P3) (fp P7) /\
    fl L23 = l_from_points (fp P4) (fp P9) /\
    fl L24 = l_from_points (fp P4) (fp P8) /\
    fl L25 = l_from_points (fp P4) (fp P10) /\
    fl L26 = l_from_points (fp P4) (fp P7) /\
    fl L27 = l_from_points (fp P5) (fp P8) /\
    fl L28 = l_from_points (fp P5) (fp P7) /\
    fl L29 = l_from_points (fp P5) (fp P9) /\
    fl L30 = l_from_points (fp P5) (fp P10) /\
    fl L31 = l_from_points (fp P6) (fp P7) /\
    fl L32 = l_from_points (fp P6) (fp P8) /\
    fl L33 = l_from_points (fp P6) (fp P9) /\
    fl L34 = l_from_points (fp P6) (fp P10))) by (repeat split; (rewrite <- (is_collineation_l_from_points fp fl Hfpfl); [reflexivity | discriminate]));
rewrite HP0 in Hfl; rewrite HP1 in Hfl; rewrite HP2 in Hfl; rewrite HP3 in Hfl; rewrite HP4 in Hfl;
rewrite HP5 in Hfl; rewrite HP6 in Hfl; rewrite HP7 in Hfl; rewrite HP8 in Hfl; rewrite HP9 in Hfl;
rewrite HP10 in Hfl; rewrite HP11 in Hfl; rewrite HP12 in Hfl; rewrite HP13 in Hfl;
destruct Hfl as [HL0 [HL1 [HL2 [HL3 [HL4 [HL5 [HL6 [HL7 [HL8 [HL9 [HL10 [HL11 [HL12 [HL13 [HL14 [HL15 [HL16 [HL17 [HL18 [HL19 [HL20 [HL21 [HL22 [HL23 [HL24 [HL25 [HL26 [HL27 [HL28 [HL29 [HL30 [HL31 [HL32 [HL33 HL34]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
unfold all_c69.
par:time (repeat (match goal with |- In (?fp, ?fl) ((?fp_i,?fl_i)::_) =>
                let HeqP := fresh in assert (HeqP:fp=fp_i) by (apply fp_ext; intros p; destruct p;
                                       solve [rewrite HP0; reflexivity |
                                              rewrite HP1; reflexivity |
                                              rewrite HP2; reflexivity |
                                              rewrite HP3; reflexivity |
                                              rewrite HP4; reflexivity |
                                              rewrite HP5; reflexivity |
                                              rewrite HP6; reflexivity |
                                              rewrite HP7; reflexivity |
                                              rewrite HP8; reflexivity |
                                              rewrite HP9; reflexivity |
                                              rewrite HP10; reflexivity |
                                              rewrite HP11; reflexivity |
                                              rewrite HP12; reflexivity |
                                              rewrite HP13; reflexivity |
                                              rewrite HP14; reflexivity ]);
                let HeqL := fresh in assert (HeqL:fl=fl_i) by (apply fl_ext; intros l; destruct l;
                                       solve [rewrite HL0; reflexivity |
                                              rewrite HL1; reflexivity |
                                              rewrite HL2; reflexivity |
                                              rewrite HL3; reflexivity |
                                              rewrite HL4; reflexivity |
                                              rewrite HL5; reflexivity |
                                              rewrite HL6; reflexivity |
                                              rewrite HL7; reflexivity |
                                              rewrite HL8; reflexivity |
                                              rewrite HL9; reflexivity |
                                              rewrite HL10; reflexivity |
                                              rewrite HL11; reflexivity |
                                              rewrite HL12; reflexivity |
                                              rewrite HL13; reflexivity |
                                              rewrite HL14; reflexivity |
                                              rewrite HL15; reflexivity |
                                              rewrite HL16; reflexivity |
                                              rewrite HL17; reflexivity |
                                              rewrite HL18; reflexivity |
                                              rewrite HL19; reflexivity |
                                              rewrite HL20; reflexivity |
                                              rewrite HL21; reflexivity |
                                              rewrite HL22; reflexivity |
                                              rewrite HL23; reflexivity |
                                              rewrite HL24; reflexivity |
                                              rewrite HL25; reflexivity |
                                              rewrite HL26; reflexivity |
                                              rewrite HL27; reflexivity |
                                              rewrite HL28; reflexivity |
                                              rewrite HL29; reflexivity |
                                              rewrite HL30; reflexivity |
                                              rewrite HL31; reflexivity |
                                              rewrite HL32; reflexivity |
                                              rewrite HL33; reflexivity |                                              
                                              rewrite HL34; reflexivity ]); rewrite HeqL; rewrite HeqP; apply in_eq
end || apply in_cons)).
Qed.

Lemma is_collineations_descr_B_P4 :
  forall fp fl, is_collineation fp fl -> fp P0 = P4 -> In (fp,fl) (all_c56++all_c57++all_c58++all_c59++all_c60++all_c61++all_c62++all_c63++all_c64++all_c65++all_c66++all_c67++all_c68++all_c69).
Proof.
  intros fp fl Hfpfl HP0.
  repeat rewrite in_app_iff.
  case_eq (fp P1); intros HP1;
    try (apply False_ind; match goal with H:?fp ?P = ?Q, H':?fp ?R = ?Q |- _ =>
                                          eapply (is_c_diffP fp fl Hfpfl P R Q); solve [assumption | discriminate] end).
  left; apply is_collineations_descr_B_P4_P0; assumption.
  do 1 right; left; apply is_collineations_descr_B_P4_P1; assumption.
  do 2 right; left; apply is_collineations_descr_B_P4_P2; assumption.
  do 3 right; left; apply is_collineations_descr_B_P4_P3; assumption.
  do 4 right; left; apply is_collineations_descr_B_P4_P5; assumption.
  do 5 right; left; apply is_collineations_descr_B_P4_P6; assumption.
  do 6 right; left; apply is_collineations_descr_B_P4_P7; assumption.
  do 7 right; left; apply is_collineations_descr_B_P4_P8; assumption.
  do 8 right; left; apply is_collineations_descr_B_P4_P9; assumption.
  do 9 right; left; apply is_collineations_descr_B_P4_P10; assumption.
  do 10 right; left; apply is_collineations_descr_B_P4_P11; assumption.
  do 11 right; left; apply is_collineations_descr_B_P4_P12; assumption.
  do 12 right; left; apply is_collineations_descr_B_P4_P13; assumption.
  do 13 right; apply is_collineations_descr_B_P4_P14; assumption.
Qed.
  
