Require Import ssreflect ssrfun ssrbool.
Require Import Generic.lemmas Generic.wlog.
Require Import PG32.pg32_inductive PG32.pg32_proofs PG32.pg32_spreads_packings.

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

Definition all_points :=
  P0::P1::P2::P3::P4::P5::P6::P7::P8::P9::P10::P11::P12::P13::P14::nil.
Definition all_points' :=
  P0::P12::P1::P3::P4::P5::P6::P7::P8::P9::P14::P11::P2::P13::P10::nil.

Definition all_lines :=
  L0::L1::L2::L3::L4::L5::L6::L7::L8::L9::L10::L11::L12::L13::L14::L15::L16::L17::L18::L19::L20::L21::L22::L23::L24::L25::L26::L27::L28::L29::L30::L31::L32::L33::L34::nil.

Fixpoint complement (l:list Point) (ref:list Point) : (list Point) :=
  match l with
    nil => ref
  | x::xs => complement xs (remove Point_dec x ref)
  end.

Eval compute in complement (all_points) (all_points').

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

(*Lemma foo : forall a b:bool, a -> b -> a && b. 
Proof.
  intros a b; case a; case b; solve [reflexivity | discriminate].
Qed.
 *)
Check forall_Point.

Lemma forall_forall_Point : forall P:Point->bool, (forall p:Point, P p) <-> forall_Point P.
Proof.
  intros P; split.
  intros H; unfold forall_Point; repeat apply foo; apply H.
  unfold forall_Point; intros Hf.
  induction p; revert Hf; repeat rewrite and_bool; intros Hf; intuition.
Qed.

(*Definition forall_Line (f:Line-> bool) : bool := f L0 && f L1 && f L2 && f L3 && f L4 && f L5 && f L6 && f L7 && f L8 && f L9 && f L10 && f L11 && f L12 && f L13 && f L14 &&
f L15 && f L16 && f L17 && f L18 && f L19 && f L20 && f L21 && f L22 && f L23 && f L24 && f L25 && f L26 && f L27 && f L28 && f L29 && f L30 && f L31 && f L32 && f L33 && f L34.
 *)

Definition inb := in_dec Point_dec.

Definition is_partition2 (p q : list Point) : bool  :=
  (forall_Point (fun x => inb x p || inb x q))
    && (forall_Point (fun x => negb (inb x p && inb x q))).

(*Definition is_spread (l1 l2 l3 l4 l5:Line) : bool :=
  disj_5l l1 l2 l3 l4 l5  &&
          is_partition2 (all_points_of_lines (l1::l2::l3::l4::l5::nil))
          nil. (*(complement (all_points_of_lines (l1::l2::l3::l4::l5::nil)) all_points).*)*)
                                              
Definition is_partition5 (p q r s t: list Point) :bool :=
  (forall_Point (fun x => inb x p || inb x q || inb x r || inb x s || inb x t))
    && (forall_Point (fun x => negb (inb x p && inb x q && inb x r && inb x s && inb x t))).

Definition is_spread5 (l1 l2 l3 l4 l5:Line) : bool :=
  disj_5l l1 l2 l3 l4 l5  &&
          is_partition5 (all_points_of_line l1) (all_points_of_line l2) (all_points_of_line l3) (all_points_of_line l4) (all_points_of_line l5).


(* Lemma is_spread_L0_L1_L2_L3_L4 : is_spread L0 L1 L2 L3 L4.
Proof.
  unfold is_spread, is_partition2;
  apply foo;
    [solve [trivial] | apply foo; (apply forall_forall_Point; intros p; case p; reflexivity)].
Qed.*)

Lemma and_bool' : forall a b : bool, a || b <-> a \/ b.
Proof.
  intros a b; destruct a; destruct b; split; intuition.
Qed.  

(*
Lemma is_spread_L4_L7_L14_L20_L28 : is_spread L4 L7 L14 L20 L28.
Proof.
  unfold is_spread, is_partition2;
  apply foo;
  [solve [trivial] | apply foo; (apply forall_forall_Point; intros p; case p; reflexivity)].
Qed.

Lemma is_spread5_L4_L7_L14_L20_L28 : is_spread5 L4 L7 L14 L20 L28.
Proof.
  unfold is_spread5, is_partition5;
  apply foo;
  [solve [trivial] | apply foo; (apply forall_forall_Point; intros p; case p; reflexivity)].
  Qed.
*)

(* there are only 56 spreads - try_pg32.c finds them all *)

Lemma eqL_eq : forall x y, eqL x y -> x=y.
Proof.
intros.
destruct x; destruct y;solve [reflexivity | discriminate].
Qed.

Lemma and_bool_lr : forall a b, a && b -> a /\ b.
Proof.
  intros a b; case a; case b; intros H; inversion H; split; assumption.
Qed.

Lemma and_bool : forall a b, a && b <-> a /\ b.
Proof.
  intros a b; split.
  apply and_bool_lr.
  case a;case b; intros (ha,hb); solve [inversion ha | inversion hb | reflexivity].
Qed.

Lemma ab5_bool : forall a b c d e, a && b && c && d && e <-> a /\ b /\ c /\ d /\ e. 
  intros a b c d e; split.
  repeat rewrite and_bool; intros; tauto.
  case a; case b; case c; case d; case e; intros ; solve [reflexivity | decompose [and] H; discriminate].
Qed.


Definition all_isomorphic (P:(list Point)->(list Point)->Prop) l :=
  forall t1 t2: (list Point), In t1 l -> In t2 l -> P t1 t2.
Check all_isomorphic.

Definition all_iso_decomp  (P:(list Point)->(list Point)->Prop) (l:list (list Point)) :=
  forall n:nat, (length l <> 0) -> P (nth (Nat.modulo n (length l)) l []) (nth (Nat.modulo (S n) (length l)) l []).

Check all_iso_decomp.
Check nth.

Section P.

  Variable l:list (list Point).
  Variable P:(list Point -> list Point -> Prop).
  Hypothesis length_l : length l <> 0 .

  Hypothesis P_refl : forall a, P a a.
  Hypothesis P_sym : forall a b, P a b -> P b a.
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
apply P_sym.
apply induction_step_1.
apply H; assumption.
(* <- *)
intros.
apply H.
Qed.

Lemma all_equiv : all_isomorphic P l <-> all_iso_decomp P l.
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

Print spreads.

Lemma is_spread_descr_A :
  forall l1 l2 l3 l4 l5 : Line, In [l1;l2;l3;l4;l5] spreads -> (is_spread5 l1 l2 l3 l4 l5).
Proof.
  intros l1 l2 l3 l4 l5 HIn_S.
  repeat (destruct HIn_S as [HeqL | HIn_S]; [unfold S0 in *; inversion HeqL; reflexivity | idtac]).
inversion HIn_S.
Qed.

Lemma equiv_def : forall l1 l2 l3 l4 l5:Line, In [l1;l2;l3;l4;l5] spreads <-> (((eqL l1 L0) &&(eqL l2 L19) && (eqL l3 L24) && (eqL l4 L28) && (eqL l5 L33)) || 
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
repeat rewrite and_bool';repeat rewrite ab5_bool.
intros Hor; repeat destruct Hor as [Hor | Hor]; destruct Hor as [Hand1  [Hand2 [Hand3 [Hand4 Hand5]]]];
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
  intros l1 l2 l3 l4 l5; repeat rewrite and_bool';
    intros Hor; repeat destruct Hor as [Hor | HeqL];
      try revert Hor; try revert HeqL; rewrite ab5_bool;
  intros (Hand1, (Hand2,(Hand3,(Hand4,Hand5)))); 
    rewrite (eqL_eq _  _ Hand1);
    rewrite (eqL_eq _  _ Hand2);
    rewrite (eqL_eq _  _ Hand3);
    rewrite (eqL_eq _  _ Hand4);
    rewrite (eqL_eq _  _ Hand5);
    reflexivity.
Qed.



Definition eq_s (l1 l2 l3 l4 l5:Line) (m1 m2 m3 m4 m5:Line) :=
    eqL l1 m1 &&  eqL l2 m2 &&  eqL l3 m3 &&  eqL l4 m4 &&  eqL l5 m5.
(*
Lemma is_spread_descr_B :
  forall l1 l2 l3 l4 l5 : Line,
    leL l1 l2 && leL l2 l3 && leL l3 l4 && leL l4 l5 ->
    (is_spread5 l1 l2 l3 l4 l5) ->  In [l1;l2;l3;l4;l5] spreads.
Proof.
  intros l1 l2 l3 l4 l5 Hle (*Hdist*) His.
  destruct l1; destruct l2.
par:  try solve  [exact (degen_bool _ Hle)  | exact (degen_bool _ His) |idtac].

destruct l3; destruct l4;destruct l5; try 
solve [exact (degen_bool _ Hle) | exact (degen_bool _ His)].
  abstract
          (destruct l3;  (solve [exact (degen_bool _ Hle) | exact (degen_bool _ His) |
           destruct l4;  (solve [exact (degen_bool _ Hle) |  exact (degen_bool _ His) |
                                 destruct l5;  (solve [ exact (degen_bool _ Hle) |  exact (degen_bool _ His) | exact (erefl true)])])])).

                                                                                                                                          
    destruct l1; (destruct l2;
      solve  [exact (degen_bool _ Hle)  | exact (degen_bool _ His) | (*idtac].  ;*)
      (*par:*)          (* 280 cases to deal with *)
abstract
          (destruct l3;  (solve [exact (degen_bool _ Hle) | exact (degen_bool _ His) |
           destruct l4;  (solve [exact (degen_bool _ Hle) |  exact (degen_bool _ His) |
           destruct l5;  (solve [ exact (degen_bool _ Hle) |  exact (degen_bool _ His) | exact (erefl true)])])]))]).
Optimize Heap.
Optimize Proof.
Time Qed.
  intros l1 l2 l3 l4 l5 HIn_S.
  repeat (destruct HIn_S as [HeqL | HIn_S]; [unfold S0 in *; inversion HeqL; reflexivity | idtac]).
inversion HIn_S.
Qed.

*)

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
intros.
Admitted. (* Qed fails *)
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
Print forall_Point.
  destruct (and_bool_lr _  _ H).
 (* simpl in H1.
Print is_partition5.

; destruct l3; destruct l4; destruct l5.*)
Admitted.

           (abstract (destruct l3; abstract (solve [exact (degen_bool _ Hle) | exact (degen_bool _ His) | destruct l4;
                                                                                                 abstract (solve [exact (degen_bool _ Hle) | exact (degen_bool _ His)
                                                                                                                  | destruct l5;
                                                                                                                   abstract (solve [ exact (degen_bool _ Hle) | exact (degen_bool _ His) |
                                           exact (erefl true)])])]))).
Show Proof.
*)
Check is_spread_descr_2.

Lemma is_spread_descr : forall l1 l2 l3 l4 l5,
    leL l1 l2 && leL l2 l3 && leL l3 l4 && leL l4 l5 ->
    (is_spread5 l1 l2 l3 l4 l5 <-> 
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
  intros; split; [apply is_spread_descr_2 ; assumption| apply is_spread_descr_1].
Qed.


  (*forall P: spread -> spread -> Prop, forall a b, (In a l /\ In b l -> P a b) <-> forall a na, P a na*)
