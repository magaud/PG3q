Require Import ssreflect ssrfun ssrbool.

Require Import PG32.pg32_inductive PG32.pg32_proofs.
Require Import PG32.pg32_spreads.
Require Import PG32.pg32_spreads_collineations.
Require Import PG32.pg32_spreads_packings.
Require Import PG32.pg32_packings_collineations.
Require Import PG32.pg32_automorphisms.

Require Import List.
Import ListNotations.

Lemma l_can_be_built_from_two_points : forall l, exists p1 p2, p1<>p2 /\ l = l_from_points p1 p2.
Proof.
intros l; destruct l.
exists P0; exists P1; split; [discriminate | reflexivity].
exists P0; exists P3; split; [discriminate | reflexivity].
exists P0; exists P6; split; [discriminate | reflexivity].
exists P0; exists P7; split; [discriminate | reflexivity].
exists P0; exists P10; split; [discriminate | reflexivity].
exists P0; exists P11; split; [discriminate | reflexivity].
exists P0; exists P13; split; [discriminate | reflexivity].
exists P1; exists P4; split; [discriminate | reflexivity].
exists P1; exists P8; split; [discriminate | reflexivity].
exists P1; exists P12; split; [discriminate | reflexivity].
exists P1; exists P7; split; [discriminate | reflexivity].
exists P1; exists P13; split; [discriminate | reflexivity].
exists P1; exists P3; split; [discriminate | reflexivity].
exists P2; exists P7; split; [discriminate | reflexivity].
exists P2; exists P11; split; [discriminate | reflexivity].
exists P2; exists P3; split; [discriminate | reflexivity].
exists P2; exists P12; split; [discriminate | reflexivity].
exists P2; exists P4; split; [discriminate | reflexivity].
exists P2; exists P8; split; [discriminate | reflexivity].
exists P3; exists P10; split; [discriminate | reflexivity].
exists P3; exists P8; split; [discriminate | reflexivity].
exists P3; exists P9; split; [discriminate | reflexivity].
exists P3; exists P7; split; [discriminate | reflexivity].
exists P4; exists P9; split; [discriminate | reflexivity].
exists P4; exists P8; split; [discriminate | reflexivity].
exists P4; exists P10; split; [discriminate | reflexivity].
exists P4; exists P7; split; [discriminate | reflexivity].
exists P5; exists P8; split; [discriminate | reflexivity].
exists P5; exists P7; split; [discriminate | reflexivity].
exists P5; exists P9; split; [discriminate | reflexivity].
exists P5; exists P10; split; [discriminate | reflexivity].
exists P6; exists P7; split; [discriminate | reflexivity].
exists P6; exists P8; split; [discriminate | reflexivity].
exists P6; exists P9; split; [discriminate | reflexivity].
exists P6; exists P10; split; [discriminate | reflexivity].
Qed.

Lemma fp_ext :
  forall (fp:Point->Point) (fp':Point->Point), (forall (p:Point), fp p = fp' p) -> fp = fp'.
Admitted.

Lemma fl_ext :
  forall (fl:Line->Line) (fl':Line->Line), (forall (l:Line), fl l = fl' l) -> fl = fl'.
Admitted.

Lemma is_c_diffP : forall fp fl, is_collineation fp fl -> forall x y z, x<>y -> fp x = z -> fp y = z -> False.
Proof.
intros fp fl Hcol x y z  Hyz fp_x fp_z.
destruct Hcol as [[Hinjfp Hsurjfp][HinjL1 Hincid1]].
rewrite <- fp_z in fp_x.
apply Hyz; apply Hinjfp; assumption.
Qed.

Lemma is_c_diffL : forall fp fl, is_collineation fp fl -> forall  x y z, x<>y -> fl x = z -> fl y = z -> False.
Proof.
intros fp fl Hcol x y z Hyz fp_x fp_z.
destruct Hcol as [HbijP [[Hinjl Hsurjl] Hincid]].
rewrite <- fp_z in fp_x.
apply Hyz; apply Hinjl; assumption.
Qed.

Ltac not_bijP :=
  match goal with H:?fp ?P = ?Q, H':?fp ?R = ?Q |- _ =>
                  eapply (is_c_diffP fp _ _ P R Q); solve [assumption | discriminate] end.

Ltac not_bijL :=
  match goal with H:?fl ?P = ?Q, H':?fl ?R = ?Q |- _ =>
                  eapply (is_c_diffL _ fl _ P R Q); solve [assumption | discriminate] end.

Lemma is_collineation_l_from_points :
  forall fp fl, is_collineation fp fl ->
                forall Pa Pb, Pa<>Pb -> fl (l_from_points Pa Pb) = l_from_points (fp Pa) (fp Pb).
Proof.
intros fp fl [HbijP [HbijL Hincid]].
intros Pa Pb HPaPb.
assert (HPa : (incid_lp Pa (l_from_points Pa Pb))) by apply incid_lp_l_from_point1.
assert (HPb : (incid_lp Pb (l_from_points Pa Pb))) by apply incid_lp_l_from_point2.
generalize (Hincid Pa (l_from_points Pa Pb) HPa); clear HPa; intros HPa.
generalize (Hincid Pb (l_from_points Pa Pb) HPb); clear HPb; intros Hpb.
assert (HPa' : incid_lp (fp Pa) (l_from_points (fp Pa) (fp Pb))) by apply incid_lp_l_from_point1.
assert (HPb' : incid_lp (fp Pb) (l_from_points (fp Pa) (fp Pb))) by apply incid_lp_l_from_point2.
eapply (a1_unique (fp Pa)  (fp Pb)); try assumption.
intro; apply HPaPb; destruct HbijP as [HinjP HsurjP]; apply HinjP; assumption.
Qed.

Lemma Point_dec' : forall T U:Point, {T=U}+{~T=U}.
Proof.
  intros T U; case T; case U;
    solve [left; exact (@erefl Point _) | right; discriminate].
Defined.

Definition points_from_line (l:Line) := 
match l with 
| L0  =>  [P0;P1;P2] 
| L1  =>  [P0;P3;P4] 
| L2  =>  [P0;P5;P6] 
| L3  =>  [P0;P7;P8] 
| L4  =>  [P0;P10;P9] 
| L5  =>  [P0;P11;P12] 
| L6  =>  [P0;P13;P14] 
| L7  =>  [P1;P4;P6] 
| L8  =>  [P1;P8;P10] 
| L9  =>  [P1;P12;P14] 
| L10  =>  [P1;P7;P9] 
| L11  =>  [P1;P13;P11] 
| L12  =>  [P1;P3;P5] 
| L13  =>  [P2;P7;P10] 
| L14  =>  [P2;P11;P14] 
| L15  =>  [P2;P3;P6] 
| L16  =>  [P2;P12;P13] 
| L17  =>  [P2;P4;P5] 
| L18  =>  [P2;P8;P9] 
| L19  =>  [P3;P10;P14] 
| L20  =>  [P3;P8;P12] 
| L21  =>  [P3;P9;P13] 
| L22  =>  [P3;P7;P11] 
| L23  =>  [P4;P9;P14] 
| L24  =>  [P4;P8;P11] 
| L25  =>  [P4;P10;P13] 
| L26  =>  [P4;P7;P12] 
| L27  =>  [P5;P8;P14] 
| L28  =>  [P5;P7;P13] 
| L29  =>  [P5;P9;P11] 
| L30  =>  [P5;P10;P12] 
| L31  =>  [P6;P7;P14] 
| L32  =>  [P6;P8;P13] 
| L33  =>  [P6;P9;P12] 
| L34  =>  [P6;P10;P11] 
end.

Definition third (A B:Point) :=
  match (points_from_line (l_from_points A B)) with
    [x1;x2;x3] =>
    if (Point_dec' x1 A)
    then
      if (Point_dec' x2 B)
      then x3
      else x2
    else
      if (Point_dec' x1 B) then
        if (Point_dec' x2 A)
        then x3
        else x2
      else x1 | _ => P0 end.                        

Lemma incid_lp_l_from_points : forall A B, A<>B -> forall x, incid_lp x (l_from_points A B) -> x=A \/ x=B \/x=third A B.
Proof.  
intros A B HAB.
destruct A; destruct B; try (apply False_ind; apply HAB; reflexivity);
intros x Hx; destruct x; try solve [left; reflexivity | right; left; reflexivity | right; right; reflexivity | discriminate Hx].
Qed.

Lemma fp_lemma : forall fp fl, is_collineation fp fl -> forall X Y, X<>Y -> fp (third X Y) = third (fp X) (fp Y).
Proof.
intros fp fl Hfpfl X Y HXY.
pose (l:=l_from_points X Y).
assert (Hi: (incid_lp (third X Y) l)) by (destruct X; destruct Y; unfold l; try solve [ reflexivity | (apply False_ind; apply HXY; reflexivity)]).
assert (Hi':(incid_lp (fp (third X Y)) (fl l))) by (destruct Hfpfl as [HbijP [HbijL Hincid]]; apply Hincid; assumption).
assert (HFXFY:fp X <> fp Y) by (intro Heq; destruct Hfpfl as [[HinjP _] [HbijL Hincid]]; apply HXY;  apply (HinjP _ _ Heq)).
rewrite (is_collineation_l_from_points fp fl Hfpfl  _ _ HXY) in Hi'.
destruct (incid_lp_l_from_points (fp X) (fp Y) HFXFY (fp (third X Y)) Hi') as [Heq | [Heq | Heq]].
revert Heq; destruct X; destruct Y;
  try solve [apply False_ind; apply HXY; reflexivity | 
             intros Heq; destruct Hfpfl as [[HinjP _] [HbijL Hincid]]; apply HinjP in Heq; discriminate Heq].
revert Heq; destruct X; destruct Y;
  try solve [apply False_ind; apply HXY; reflexivity | 
             intros Heq; destruct Hfpfl as [[HinjP _] [HbijL Hincid]]; apply HinjP in Heq; discriminate Heq].
assumption.
Qed.

Lemma simple_rewrite : forall fp fl , is_collineation fp fl -> forall (T U Z:Point), fp T=Z -> fp U=Z -> T=U.
Proof.
  intros fp fl Hfpfl T U Z HTZ HUZ.
  assert (fp T=fp U).
  transitivity Z; [assumption | symmetry; assumption].
  destruct Hfpfl as [[HinjP _]]; apply HinjP in H; assumption.
Qed.

Ltac elim_degen_cases fp fl Hfpfl := match goal with HX : fp ?X = _, HY : fp ?Y = _ |- _ =>
                  let Hnew := fresh in
                  assert (Hnew:(fp (third X Y)) = third (fp X) (fp Y))
                    by (apply (fp_lemma fp fl Hfpfl); discriminate);  rewrite HX in Hnew; rewrite HY in Hnew; cbn in Hnew  end;
                  match goal with HT : fp ?T = ?Z, HU : fp ?U = ?Z |- _ => 
                      let Hnew2 := fresh in assert (Hnew2:T =U) by (apply (simple_rewrite fp fl Hfpfl T U Z HT HU));
                      discriminate end.
