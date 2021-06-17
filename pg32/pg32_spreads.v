Require Import ssreflect ssrfun ssrbool.
Require Import Generic.lemmas Generic.wlog.
Require Import PG32.pg32_inductive PG32.pg32_spreads_packings.

Require Import Lia.
Require Import List.
Import ListNotations.

Lemma Point_dec : forall p q : Point, {p=q}+{p<>q}.
Proof.
intros p q; case p; case q; solve [left; reflexivity | right; discriminate].
Defined.

Lemma Line_dec : forall p q : Line, {p=q}+{p<>q}.
Proof.
intros p q; case p; case q; solve [left; reflexivity | right; discriminate].
Defined.

Definition eqL (p q : Line) : bool :=
  match (Line_dec p q) with left _ => true | right _ => false end.

Definition add_points_list (l:Line) (acc:list Point) :=
  match (points_from_line l) with
  (p,q,r) =>(* p::q::r::acc*)
  if (in_dec Point_dec r acc)
  then
    if (in_dec Point_dec q acc)
    then
      if (in_dec Point_dec p acc)
      then acc
      else p::acc
    else
      if (in_dec Point_dec p acc)
      then q::acc
      else p::q::acc
  else
    if (in_dec Point_dec q acc)
    then
      if (in_dec Point_dec p acc)
      then r::acc
      else p::r::acc
    else
      if (in_dec Point_dec p acc)
      then q::r::acc
      else p::q::r::acc
  end.

Definition all_points_of_line (l:  Line) := match (points_from_line l) with (A,B,C) => [A;B;C] end.

Definition all_points_of_lines (l: list Line) := fold_right add_points_list (@nil Point) l.

Eval compute in all_points_of_lines (L0::L1::L2::L3::L4::nil).

Definition dist_5l  (A B C D E:Line) : bool :=
    (negb (eqL A B)) && (negb (eqL A C)) && (negb (eqL A D)) && (negb (eqL A E))
                     && (negb (eqL B C)) && (negb (eqL B D)) && (negb (eqL B E))
                     && (negb (eqL C D)) && (negb (eqL C E))
                     && (negb (eqL D E)).

Definition inter (l1 l2:Line) : option Point :=
    match (points_from_line l1) with ((X,Y),Z) =>
      match (points_from_line l2) with (X',Y',Z') =>
              if (Point_dec X X') then Some (X) else
                if (Point_dec X Y') then Some (X) else
                  if (Point_dec X Z') then Some (X) else
                    if (Point_dec Y X') then Some (Y) else
                      if (Point_dec Y Y') then Some (Y) else
                        if (Point_dec Y Z') then (Some Y) else
                          if (Point_dec Z X') then (Some Z) else
                            if (Point_dec Z Y') then (Some Z) else
                              if (Point_dec Z Z') then (Some Z) else None end end.

Definition disjoint (l1 l2:Line) : bool :=
  match inter l1 l2 with
  | None => true
  | Some _ => false
  end.

Definition disj_5l (A B C D E:Line) : bool :=
    (disjoint A B) && (disjoint A C) && (disjoint A D) && (disjoint A E)
                     && (disjoint B C) && (disjoint B D) && (disjoint B E)
                     && (disjoint C D) && (disjoint C E)
                     && (disjoint D E).

Definition forall_Point (f:Point -> bool) : bool :=
  f P0 && f P1 && f P2 && f P3 && f P4 && f P5 && f P6 && f P7 && f P8 && f P9 && f P10 && f P11 && f P12 && f P13 && f P14.

Lemma forall_forall_Point : forall P:Point->bool, (forall p:Point, P p) <-> forall_Point P.
Proof.
  intros P; split.
  intros H; unfold forall_Point; repeat apply foo; apply H.
  unfold forall_Point; intros Hf.
  induction p; revert Hf; repeat rewrite and_bool; intros Hf; intuition.
Qed.

Definition inb := in_dec Point_dec.
                                              
Definition is_partition5 (p q r s t: list Point) :bool :=
  (forall_Point (fun x => inb x p || inb x q || inb x r || inb x s || inb x t))
    && (forall_Point (fun x => negb (inb x p && inb x q && inb x r && inb x s && inb x t))).

Definition is_spread5 (l1 l2 l3 l4 l5:Line) : bool :=
  disj_5l l1 l2 l3 l4 l5  &&
          is_partition5 (all_points_of_line l1) (all_points_of_line l2) (all_points_of_line l3) (all_points_of_line l4) (all_points_of_line l5).

(*
Lemma simpler : forall l1 l2 l3 l4 l5:Line, is_partition5 (all_points_of_lines (l1::nil)) (all_points_of_lines (l2::nil)) (all_points_of_lines (l3::nil)) (all_points_of_lines (l4::nil)) (all_points_of_lines (l5::nil)) -> disj_5l l1 l2 l3 l4 l5.
Proof.
  intros l1 l2 l3 l4 l5 Hpart; destruct l1; destruct l2.
  unfold is_partition5 in Hpart. 
  revert Hpart; rewrite and_bool; intros [Hpart1 Hpart2].
  unfold forall_Point in Hpart1, Hpart2; try solve [exact (degen_bool _ Hpart1) | exact (degen_bool _ Hpart2)].
  unfold disj_5l, is_partition5 in *.
  unfold forall_Point in H; simpl in H.
revert H; rewrite and_bool; intros H.
rewrite <- forall_forall_Point in H.
rewrite <- forall_forall_Point in H.
destruct H as [HA HB].
destruct l3; destruct l4; destruct l5; try solve [exact (degen_bool _ HA) | exact (degen_bool _ HB) | exact (erefl true)].
  destruct (and_bool_lr _  _ H).
 (* simpl in H1.

; destruct l3; destruct l4; destruct l5.*)


           (abstract (destruct l3; abstract (solve [exact (degen_bool _ Hle) | exact (degen_bool _ His) | destruct l4;
                                                                                                 abstract (solve [exact (degen_bool _ Hle) | exact (degen_bool _ His)
                                                                                                                  | destruct l5;
                                                                                                                   abstract (solve [ exact (degen_bool _ Hle) | exact (degen_bool _ His) |
                                           exact (erefl true)])])]))).
Show Proof.
 *)

(* there are only 56 spreads - try_pg32.c finds them all *)

Lemma eqL_eq : forall x y, eqL x y -> x=y.
Proof.
intros.
destruct x; destruct y;solve [reflexivity | discriminate].
Qed.

Lemma is_spread_descr_A :
  forall l1 l2 l3 l4 l5 : Line, In [l1;l2;l3;l4;l5] spreads -> (is_spread5 l1 l2 l3 l4 l5).
Proof.
  intros l1 l2 l3 l4 l5 HIn_S.
  repeat (destruct HIn_S as [HeqL | HIn_S]; [unfold S0 in *; inversion HeqL; reflexivity | idtac]).
inversion HIn_S.
Qed.

Lemma equiv_spreads_def : forall l1 l2 l3 l4 l5:Line,
    In [l1;l2;l3;l4;l5] spreads <->
    (((eqL l1 L0) &&(eqL l2 L19) && (eqL l3 L24) && (eqL l4 L28) && (eqL l5 L33)) || 
     ((eqL l1 L0) &&(eqL l2 L19) && (eqL l3 L26) && (eqL l4 L29) && (eqL l5 L32)) || 
     ((eqL l1 L0) &&(eqL l2 L20) && (eqL l3 L23) && (eqL l4 L28) && (eqL l5 L34)) || 
     ((eqL l1 L0) &&(eqL l2 L20) && (eqL l3 L25) && (eqL l4 L29) && (eqL l5 L31)) || 
     ((eqL l1 L0) &&(eqL l2 L21) && (eqL l3 L24) && (eqL l4 L30) && (eqL l5 L31)) || 
     ((eqL l1 L0) &&(eqL l2 L21) && (eqL l3 L26) && (eqL l4 L27) && (eqL l5 L34)) || 
     ((eqL l1 L0) &&(eqL l2 L22) && (eqL l3 L23) && (eqL l4 L30) && (eqL l5 L32)) || 
     ((eqL l1 L0) &&(eqL l2 L22) && (eqL l3 L25) && (eqL l4 L27) && (eqL l5 L33)) || 
     ((eqL l1 L1) &&(eqL l2 L8) && (eqL l3 L14) && (eqL l4 L28) && (eqL l5 L33)) || 
     ((eqL l1 L1) &&(eqL l2 L8) && (eqL l3 L16) && (eqL l4 L29) && (eqL l5 L31)) || 
     ((eqL l1 L1) &&(eqL l2 L9) && (eqL l3 L13) && (eqL l4 L29) && (eqL l5 L32)) || 
     ((eqL l1 L1) &&(eqL l2 L9) && (eqL l3 L18) && (eqL l4 L28) && (eqL l5 L34)) || 
     ((eqL l1 L1) &&(eqL l2 L10) && (eqL l3 L14) && (eqL l4 L30) && (eqL l5 L32)) || 
     ((eqL l1 L1) &&(eqL l2 L10) && (eqL l3 L16) && (eqL l4 L27) && (eqL l5 L34)) || 
     ((eqL l1 L1) &&(eqL l2 L11) && (eqL l3 L13) && (eqL l4 L27) && (eqL l5 L33)) || 
     ((eqL l1 L1) &&(eqL l2 L11) && (eqL l3 L18) && (eqL l4 L30) && (eqL l5 L31)) || 
     ((eqL l1 L2) &&(eqL l2 L8) && (eqL l3 L14) && (eqL l4 L21) && (eqL l5 L26)) || 
     ((eqL l1 L2) &&(eqL l2 L8) && (eqL l3 L16) && (eqL l4 L22) && (eqL l5 L23)) || 
     ((eqL l1 L2) &&(eqL l2 L9) && (eqL l3 L13) && (eqL l4 L21) && (eqL l5 L24)) || 
     ((eqL l1 L2) &&(eqL l2 L9) && (eqL l3 L18) && (eqL l4 L22) && (eqL l5 L25)) || 
     ((eqL l1 L2) &&(eqL l2 L10) && (eqL l3 L14) && (eqL l4 L20) && (eqL l5 L25)) || 
     ((eqL l1 L2) &&(eqL l2 L10) && (eqL l3 L16) && (eqL l4 L19) && (eqL l5 L24)) || 
     ((eqL l1 L2) &&(eqL l2 L11) && (eqL l3 L13) && (eqL l4 L20) && (eqL l5 L23)) || 
     ((eqL l1 L2) &&(eqL l2 L11) && (eqL l3 L18) && (eqL l4 L19) && (eqL l5 L26)) || 
     ((eqL l1 L3) &&(eqL l2 L7) && (eqL l3 L14) && (eqL l4 L21) && (eqL l5 L30)) || 
     ((eqL l1 L3) &&(eqL l2 L7) && (eqL l3 L16) && (eqL l4 L19) && (eqL l5 L29)) || 
     ((eqL l1 L3) &&(eqL l2 L9) && (eqL l3 L15) && (eqL l4 L25) && (eqL l5 L29)) || 
     ((eqL l1 L3) &&(eqL l2 L9) && (eqL l3 L17) && (eqL l4 L21) && (eqL l5 L34)) || 
     ((eqL l1 L3) &&(eqL l2 L11) && (eqL l3 L15) && (eqL l4 L23) && (eqL l5 L30)) || 
     ((eqL l1 L3) &&(eqL l2 L11) && (eqL l3 L17) && (eqL l4 L19) && (eqL l5 L33)) || 
     ((eqL l1 L3) &&(eqL l2 L12) && (eqL l3 L14) && (eqL l4 L25) && (eqL l5 L33)) || 
     ((eqL l1 L3) &&(eqL l2 L12) && (eqL l3 L16) && (eqL l4 L23) && (eqL l5 L34)) || 
     ((eqL l1 L4) &&(eqL l2 L7) && (eqL l3 L14) && (eqL l4 L20) && (eqL l5 L28)) || 
     ((eqL l1 L4) &&(eqL l2 L7) && (eqL l3 L16) && (eqL l4 L22) && (eqL l5 L27)) || 
     ((eqL l1 L4) &&(eqL l2 L9) && (eqL l3 L15) && (eqL l4 L24) && (eqL l5 L28)) || 
     ((eqL l1 L4) &&(eqL l2 L9) && (eqL l3 L17) && (eqL l4 L22) && (eqL l5 L32)) || 
     ((eqL l1 L4) &&(eqL l2 L11) && (eqL l3 L15) && (eqL l4 L26) && (eqL l5 L27)) || 
     ((eqL l1 L4) &&(eqL l2 L11) && (eqL l3 L17) && (eqL l4 L20) && (eqL l5 L31)) || 
     ((eqL l1 L4) &&(eqL l2 L12) && (eqL l3 L14) && (eqL l4 L26) && (eqL l5 L32)) || 
     ((eqL l1 L4) &&(eqL l2 L12) && (eqL l3 L16) && (eqL l4 L24) && (eqL l5 L31)) || 
     ((eqL l1 L5) &&(eqL l2 L7) && (eqL l3 L13) && (eqL l4 L21) && (eqL l5 L27)) || 
     ((eqL l1 L5) &&(eqL l2 L7) && (eqL l3 L18) && (eqL l4 L19) && (eqL l5 L28)) || 
     ((eqL l1 L5) &&(eqL l2 L8) && (eqL l3 L15) && (eqL l4 L23) && (eqL l5 L28)) || 
     ((eqL l1 L5) &&(eqL l2 L8) && (eqL l3 L17) && (eqL l4 L21) && (eqL l5 L31)) || 
     ((eqL l1 L5) &&(eqL l2 L10) && (eqL l3 L15) && (eqL l4 L25) && (eqL l5 L27)) || 
     ((eqL l1 L5) &&(eqL l2 L10) && (eqL l3 L17) && (eqL l4 L19) && (eqL l5 L32)) || 
     ((eqL l1 L5) &&(eqL l2 L12) && (eqL l3 L13) && (eqL l4 L23) && (eqL l5 L32)) || 
     ((eqL l1 L5) &&(eqL l2 L12) && (eqL l3 L18) && (eqL l4 L25) && (eqL l5 L31)) || 
     ((eqL l1 L6) &&(eqL l2 L7) && (eqL l3 L13) && (eqL l4 L20) && (eqL l5 L29)) || 
     ((eqL l1 L6) &&(eqL l2 L7) && (eqL l3 L18) && (eqL l4 L22) && (eqL l5 L30)) || 
     ((eqL l1 L6) &&(eqL l2 L8) && (eqL l3 L15) && (eqL l4 L26) && (eqL l5 L29)) || 
     ((eqL l1 L6) &&(eqL l2 L8) && (eqL l3 L17) && (eqL l4 L22) && (eqL l5 L33)) || 
     ((eqL l1 L6) &&(eqL l2 L10) && (eqL l3 L15) && (eqL l4 L24) && (eqL l5 L30)) || 
     ((eqL l1 L6) &&(eqL l2 L10) && (eqL l3 L17) && (eqL l4 L20) && (eqL l5 L34)) || 
     ((eqL l1 L6) &&(eqL l2 L12) && (eqL l3 L13) && (eqL l4 L24) && (eqL l5 L33)) || 
     ((eqL l1 L6) &&(eqL l2 L12) && (eqL l3 L18) && (eqL l4 L26) && (eqL l5 L34)) ).
Proof.                         
  intros l1 l2 l3 l4 l5.
  split.
  intros HIn_S.
  repeat (destruct HIn_S as [HeqL | HIn_S]; [unfold S0 in *; inversion HeqL; reflexivity | idtac]).
  inversion HIn_S.
  repeat rewrite or_bool;repeat rewrite ab5_bool.
  intros Hor; repeat destruct Hor as [Hor | Hor];
    destruct Hor as [Hand1  [Hand2 [Hand3 [Hand4 Hand5]]]];
    rewrite (eqL_eq _  _ Hand1);
    rewrite (eqL_eq _  _ Hand2);
    rewrite (eqL_eq _  _ Hand3);
    rewrite (eqL_eq _  _ Hand4);
    rewrite (eqL_eq _  _ Hand5); solve [repeat apply in_eq || apply in_cons].
Qed.

Lemma is_spread_descr_1 :  forall l1 l2 l3 l4 l5,
    (*56 cases*)
    (((eqL l1 L0) &&(eqL l2 L19) && (eqL l3 L24) && (eqL l4 L28) && (eqL l5 L33)) || 
((eqL l1 L0) &&(eqL l2 L19) && (eqL l3 L26) && (eqL l4 L29) && (eqL l5 L32)) || 
((eqL l1 L0) &&(eqL l2 L20) && (eqL l3 L23) && (eqL l4 L28) && (eqL l5 L34)) || 
((eqL l1 L0) &&(eqL l2 L20) && (eqL l3 L25) && (eqL l4 L29) && (eqL l5 L31)) || 
((eqL l1 L0) &&(eqL l2 L21) && (eqL l3 L24) && (eqL l4 L30) && (eqL l5 L31)) || 
((eqL l1 L0) &&(eqL l2 L21) && (eqL l3 L26) && (eqL l4 L27) && (eqL l5 L34)) || 
((eqL l1 L0) &&(eqL l2 L22) && (eqL l3 L23) && (eqL l4 L30) && (eqL l5 L32)) || 
((eqL l1 L0) &&(eqL l2 L22) && (eqL l3 L25) && (eqL l4 L27) && (eqL l5 L33)) || 
((eqL l1 L1) &&(eqL l2 L8) && (eqL l3 L14) && (eqL l4 L28) && (eqL l5 L33)) || 
((eqL l1 L1) &&(eqL l2 L8) && (eqL l3 L16) && (eqL l4 L29) && (eqL l5 L31)) || 
((eqL l1 L1) &&(eqL l2 L9) && (eqL l3 L13) && (eqL l4 L29) && (eqL l5 L32)) || 
((eqL l1 L1) &&(eqL l2 L9) && (eqL l3 L18) && (eqL l4 L28) && (eqL l5 L34)) || 
((eqL l1 L1) &&(eqL l2 L10) && (eqL l3 L14) && (eqL l4 L30) && (eqL l5 L32)) || 
((eqL l1 L1) &&(eqL l2 L10) && (eqL l3 L16) && (eqL l4 L27) && (eqL l5 L34)) || 
((eqL l1 L1) &&(eqL l2 L11) && (eqL l3 L13) && (eqL l4 L27) && (eqL l5 L33)) || 
((eqL l1 L1) &&(eqL l2 L11) && (eqL l3 L18) && (eqL l4 L30) && (eqL l5 L31)) || 
((eqL l1 L2) &&(eqL l2 L8) && (eqL l3 L14) && (eqL l4 L21) && (eqL l5 L26)) || 
((eqL l1 L2) &&(eqL l2 L8) && (eqL l3 L16) && (eqL l4 L22) && (eqL l5 L23)) || 
((eqL l1 L2) &&(eqL l2 L9) && (eqL l3 L13) && (eqL l4 L21) && (eqL l5 L24)) || 
((eqL l1 L2) &&(eqL l2 L9) && (eqL l3 L18) && (eqL l4 L22) && (eqL l5 L25)) || 
((eqL l1 L2) &&(eqL l2 L10) && (eqL l3 L14) && (eqL l4 L20) && (eqL l5 L25)) || 
((eqL l1 L2) &&(eqL l2 L10) && (eqL l3 L16) && (eqL l4 L19) && (eqL l5 L24)) || 
((eqL l1 L2) &&(eqL l2 L11) && (eqL l3 L13) && (eqL l4 L20) && (eqL l5 L23)) || 
((eqL l1 L2) &&(eqL l2 L11) && (eqL l3 L18) && (eqL l4 L19) && (eqL l5 L26)) || 
((eqL l1 L3) &&(eqL l2 L7) && (eqL l3 L14) && (eqL l4 L21) && (eqL l5 L30)) || 
((eqL l1 L3) &&(eqL l2 L7) && (eqL l3 L16) && (eqL l4 L19) && (eqL l5 L29)) || 
((eqL l1 L3) &&(eqL l2 L9) && (eqL l3 L15) && (eqL l4 L25) && (eqL l5 L29)) || 
((eqL l1 L3) &&(eqL l2 L9) && (eqL l3 L17) && (eqL l4 L21) && (eqL l5 L34)) || 
((eqL l1 L3) &&(eqL l2 L11) && (eqL l3 L15) && (eqL l4 L23) && (eqL l5 L30)) || 
((eqL l1 L3) &&(eqL l2 L11) && (eqL l3 L17) && (eqL l4 L19) && (eqL l5 L33)) || 
((eqL l1 L3) &&(eqL l2 L12) && (eqL l3 L14) && (eqL l4 L25) && (eqL l5 L33)) || 
((eqL l1 L3) &&(eqL l2 L12) && (eqL l3 L16) && (eqL l4 L23) && (eqL l5 L34)) || 
((eqL l1 L4) &&(eqL l2 L7) && (eqL l3 L14) && (eqL l4 L20) && (eqL l5 L28)) || 
((eqL l1 L4) &&(eqL l2 L7) && (eqL l3 L16) && (eqL l4 L22) && (eqL l5 L27)) || 
((eqL l1 L4) &&(eqL l2 L9) && (eqL l3 L15) && (eqL l4 L24) && (eqL l5 L28)) || 
((eqL l1 L4) &&(eqL l2 L9) && (eqL l3 L17) && (eqL l4 L22) && (eqL l5 L32)) || 
((eqL l1 L4) &&(eqL l2 L11) && (eqL l3 L15) && (eqL l4 L26) && (eqL l5 L27)) || 
((eqL l1 L4) &&(eqL l2 L11) && (eqL l3 L17) && (eqL l4 L20) && (eqL l5 L31)) || 
((eqL l1 L4) &&(eqL l2 L12) && (eqL l3 L14) && (eqL l4 L26) && (eqL l5 L32)) || 
((eqL l1 L4) &&(eqL l2 L12) && (eqL l3 L16) && (eqL l4 L24) && (eqL l5 L31)) || 
((eqL l1 L5) &&(eqL l2 L7) && (eqL l3 L13) && (eqL l4 L21) && (eqL l5 L27)) || 
((eqL l1 L5) &&(eqL l2 L7) && (eqL l3 L18) && (eqL l4 L19) && (eqL l5 L28)) || 
((eqL l1 L5) &&(eqL l2 L8) && (eqL l3 L15) && (eqL l4 L23) && (eqL l5 L28)) || 
((eqL l1 L5) &&(eqL l2 L8) && (eqL l3 L17) && (eqL l4 L21) && (eqL l5 L31)) || 
((eqL l1 L5) &&(eqL l2 L10) && (eqL l3 L15) && (eqL l4 L25) && (eqL l5 L27)) || 
((eqL l1 L5) &&(eqL l2 L10) && (eqL l3 L17) && (eqL l4 L19) && (eqL l5 L32)) || 
((eqL l1 L5) &&(eqL l2 L12) && (eqL l3 L13) && (eqL l4 L23) && (eqL l5 L32)) || 
((eqL l1 L5) &&(eqL l2 L12) && (eqL l3 L18) && (eqL l4 L25) && (eqL l5 L31)) || 
((eqL l1 L6) &&(eqL l2 L7) && (eqL l3 L13) && (eqL l4 L20) && (eqL l5 L29)) || 
((eqL l1 L6) &&(eqL l2 L7) && (eqL l3 L18) && (eqL l4 L22) && (eqL l5 L30)) || 
((eqL l1 L6) &&(eqL l2 L8) && (eqL l3 L15) && (eqL l4 L26) && (eqL l5 L29)) || 
((eqL l1 L6) &&(eqL l2 L8) && (eqL l3 L17) && (eqL l4 L22) && (eqL l5 L33)) || 
((eqL l1 L6) &&(eqL l2 L10) && (eqL l3 L15) && (eqL l4 L24) && (eqL l5 L30)) || 
((eqL l1 L6) &&(eqL l2 L10) && (eqL l3 L17) && (eqL l4 L20) && (eqL l5 L34)) || 
((eqL l1 L6) &&(eqL l2 L12) && (eqL l3 L13) && (eqL l4 L24) && (eqL l5 L33)) || 
((eqL l1 L6) &&(eqL l2 L12) && (eqL l3 L18) && (eqL l4 L26) && (eqL l5 L34)) )
 -> (is_spread5 l1 l2 l3 l4 l5).
Proof.
  intros l1 l2 l3 l4 l5; rewrite <- equiv_spreads_def; apply is_spread_descr_A.
Qed.  

Lemma is_spread_descr_2 : forall l1 l2 l3 l4 l5,
    leL l1 l2 && leL l2 l3 && leL l3 l4 && leL l4 l5 ->
   (* disj_5l l1 l2 l3 l4 l5 -> *)
    (is_spread5 l1 l2 l3 l4 l5 -> 
    (*56 cases*)
    ((eqL l1 L0) &&(eqL l2 L19) && (eqL l3 L24) && (eqL l4 L28) && (eqL l5 L33)) || 
((eqL l1 L0) &&(eqL l2 L19) && (eqL l3 L26) && (eqL l4 L29) && (eqL l5 L32)) || 
((eqL l1 L0) &&(eqL l2 L20) && (eqL l3 L23) && (eqL l4 L28) && (eqL l5 L34)) || 
((eqL l1 L0) &&(eqL l2 L20) && (eqL l3 L25) && (eqL l4 L29) && (eqL l5 L31)) || 
((eqL l1 L0) &&(eqL l2 L21) && (eqL l3 L24) && (eqL l4 L30) && (eqL l5 L31)) || 
((eqL l1 L0) &&(eqL l2 L21) && (eqL l3 L26) && (eqL l4 L27) && (eqL l5 L34)) || 
((eqL l1 L0) &&(eqL l2 L22) && (eqL l3 L23) && (eqL l4 L30) && (eqL l5 L32)) || 
((eqL l1 L0) &&(eqL l2 L22) && (eqL l3 L25) && (eqL l4 L27) && (eqL l5 L33)) || 
((eqL l1 L1) &&(eqL l2 L8) && (eqL l3 L14) && (eqL l4 L28) && (eqL l5 L33)) || 
((eqL l1 L1) &&(eqL l2 L8) && (eqL l3 L16) && (eqL l4 L29) && (eqL l5 L31)) || 
((eqL l1 L1) &&(eqL l2 L9) && (eqL l3 L13) && (eqL l4 L29) && (eqL l5 L32)) || 
((eqL l1 L1) &&(eqL l2 L9) && (eqL l3 L18) && (eqL l4 L28) && (eqL l5 L34)) || 
((eqL l1 L1) &&(eqL l2 L10) && (eqL l3 L14) && (eqL l4 L30) && (eqL l5 L32)) || 
((eqL l1 L1) &&(eqL l2 L10) && (eqL l3 L16) && (eqL l4 L27) && (eqL l5 L34)) || 
((eqL l1 L1) &&(eqL l2 L11) && (eqL l3 L13) && (eqL l4 L27) && (eqL l5 L33)) || 
((eqL l1 L1) &&(eqL l2 L11) && (eqL l3 L18) && (eqL l4 L30) && (eqL l5 L31)) || 
((eqL l1 L2) &&(eqL l2 L8) && (eqL l3 L14) && (eqL l4 L21) && (eqL l5 L26)) || 
((eqL l1 L2) &&(eqL l2 L8) && (eqL l3 L16) && (eqL l4 L22) && (eqL l5 L23)) || 
((eqL l1 L2) &&(eqL l2 L9) && (eqL l3 L13) && (eqL l4 L21) && (eqL l5 L24)) || 
((eqL l1 L2) &&(eqL l2 L9) && (eqL l3 L18) && (eqL l4 L22) && (eqL l5 L25)) || 
((eqL l1 L2) &&(eqL l2 L10) && (eqL l3 L14) && (eqL l4 L20) && (eqL l5 L25)) || 
((eqL l1 L2) &&(eqL l2 L10) && (eqL l3 L16) && (eqL l4 L19) && (eqL l5 L24)) || 
((eqL l1 L2) &&(eqL l2 L11) && (eqL l3 L13) && (eqL l4 L20) && (eqL l5 L23)) || 
((eqL l1 L2) &&(eqL l2 L11) && (eqL l3 L18) && (eqL l4 L19) && (eqL l5 L26)) || 
((eqL l1 L3) &&(eqL l2 L7) && (eqL l3 L14) && (eqL l4 L21) && (eqL l5 L30)) || 
((eqL l1 L3) &&(eqL l2 L7) && (eqL l3 L16) && (eqL l4 L19) && (eqL l5 L29)) || 
((eqL l1 L3) &&(eqL l2 L9) && (eqL l3 L15) && (eqL l4 L25) && (eqL l5 L29)) || 
((eqL l1 L3) &&(eqL l2 L9) && (eqL l3 L17) && (eqL l4 L21) && (eqL l5 L34)) || 
((eqL l1 L3) &&(eqL l2 L11) && (eqL l3 L15) && (eqL l4 L23) && (eqL l5 L30)) || 
((eqL l1 L3) &&(eqL l2 L11) && (eqL l3 L17) && (eqL l4 L19) && (eqL l5 L33)) || 
((eqL l1 L3) &&(eqL l2 L12) && (eqL l3 L14) && (eqL l4 L25) && (eqL l5 L33)) || 
((eqL l1 L3) &&(eqL l2 L12) && (eqL l3 L16) && (eqL l4 L23) && (eqL l5 L34)) || 
((eqL l1 L4) &&(eqL l2 L7) && (eqL l3 L14) && (eqL l4 L20) && (eqL l5 L28)) || 
((eqL l1 L4) &&(eqL l2 L7) && (eqL l3 L16) && (eqL l4 L22) && (eqL l5 L27)) || 
((eqL l1 L4) &&(eqL l2 L9) && (eqL l3 L15) && (eqL l4 L24) && (eqL l5 L28)) || 
((eqL l1 L4) &&(eqL l2 L9) && (eqL l3 L17) && (eqL l4 L22) && (eqL l5 L32)) || 
((eqL l1 L4) &&(eqL l2 L11) && (eqL l3 L15) && (eqL l4 L26) && (eqL l5 L27)) || 
((eqL l1 L4) &&(eqL l2 L11) && (eqL l3 L17) && (eqL l4 L20) && (eqL l5 L31)) || 
((eqL l1 L4) &&(eqL l2 L12) && (eqL l3 L14) && (eqL l4 L26) && (eqL l5 L32)) || 
((eqL l1 L4) &&(eqL l2 L12) && (eqL l3 L16) && (eqL l4 L24) && (eqL l5 L31)) || 
((eqL l1 L5) &&(eqL l2 L7) && (eqL l3 L13) && (eqL l4 L21) && (eqL l5 L27)) || 
((eqL l1 L5) &&(eqL l2 L7) && (eqL l3 L18) && (eqL l4 L19) && (eqL l5 L28)) || 
((eqL l1 L5) &&(eqL l2 L8) && (eqL l3 L15) && (eqL l4 L23) && (eqL l5 L28)) || 
((eqL l1 L5) &&(eqL l2 L8) && (eqL l3 L17) && (eqL l4 L21) && (eqL l5 L31)) || 
((eqL l1 L5) &&(eqL l2 L10) && (eqL l3 L15) && (eqL l4 L25) && (eqL l5 L27)) || 
((eqL l1 L5) &&(eqL l2 L10) && (eqL l3 L17) && (eqL l4 L19) && (eqL l5 L32)) || 
((eqL l1 L5) &&(eqL l2 L12) && (eqL l3 L13) && (eqL l4 L23) && (eqL l5 L32)) || 
((eqL l1 L5) &&(eqL l2 L12) && (eqL l3 L18) && (eqL l4 L25) && (eqL l5 L31)) || 
((eqL l1 L6) &&(eqL l2 L7) && (eqL l3 L13) && (eqL l4 L20) && (eqL l5 L29)) || 
((eqL l1 L6) &&(eqL l2 L7) && (eqL l3 L18) && (eqL l4 L22) && (eqL l5 L30)) || 
((eqL l1 L6) &&(eqL l2 L8) && (eqL l3 L15) && (eqL l4 L26) && (eqL l5 L29)) || 
((eqL l1 L6) &&(eqL l2 L8) && (eqL l3 L17) && (eqL l4 L22) && (eqL l5 L33)) || 
((eqL l1 L6) &&(eqL l2 L10) && (eqL l3 L15) && (eqL l4 L24) && (eqL l5 L30)) || 
((eqL l1 L6) &&(eqL l2 L10) && (eqL l3 L17) && (eqL l4 L20) && (eqL l5 L34)) || 
((eqL l1 L6) &&(eqL l2 L12) && (eqL l3 L13) && (eqL l4 L24) && (eqL l5 L33)) || 
((eqL l1 L6) &&(eqL l2 L12) && (eqL l3 L18) && (eqL l4 L26) && (eqL l5 L34)) ).
Proof.
  intros l1 l2 l3 l4 l5 Hle (*Hdist*) His;
    destruct l1; (destruct l2;
      solve  [exact (degen_bool _ Hle)  | exact (degen_bool _ His) | (*idtac].  ;*)
      (*par:*)          (* 280 cases to deal with *)
abstract
          (destruct l3;  (solve [exact (degen_bool _ Hle) | exact (degen_bool _ His) |
           destruct l4;  (solve [exact (degen_bool _ Hle) |  exact (degen_bool _ His) |
           destruct l5;  (solve [ exact (degen_bool _ Hle) |  exact (degen_bool _ His) | exact (erefl true)])])]))]).
Optimize Heap.
Optimize Proof.
Admitted. (* Qed fails *)


(* main theorem *)
Lemma is_spread_descr : forall l1 l2 l3 l4 l5,
    leL l1 l2 && leL l2 l3 && leL l3 l4 && leL l4 l5 ->
    (is_spread5 l1 l2 l3 l4 l5 <-> In [l1;l2;l3;l4;l5] spreads).
Proof.
  intros; rewrite equiv_spreads_def.  
  intros; split; [apply is_spread_descr_2 ; assumption| apply is_spread_descr_1].
Qed.
