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

Definition inb := in_dec Point_dec.
Definition inbL := in_dec Line_dec.

Definition forall_Line (f:Line -> bool) : bool :=
  f L0 && f L1 && f L2 && f L3 && f L4 && f L5 && f L6 && f L7 && f L8 && f L9 &&
  f L10 && f L11 && f L12 && f L13 && f L14 && f L15 && f L16 && f L17 && f L18 && f L19 && 
  f L20 && f L21 && f L22 && f L23 && f L24 && f L25 && f L26 && f L27 && f L28 && f L29 &&
  f L30 && f L31 && f L32 && f L33 && f L34.

Lemma forall_forall_Line : forall P:Line->bool, (forall p:Line, P p) <-> forall_Line P.
Proof.
  intros P; split.
  intros H; unfold forall_Line; repeat apply foo; apply H.
  unfold forall_Line; intros Hf.
  induction p; revert Hf; repeat rewrite and_bool; intros Hf; intuition.
Qed.

Definition is_partition7 (p q r s t u v: list Line) : bool :=
  (forall_Line (fun x => inbL x p || inbL x q || inbL x r || inbL x s || inbL x t || inbL x u || inbL x v))
  && (forall_Line (fun x => negb (inbL x p && inbL x q && inbL x r && inbL x s && inbL x t && inbL x u && inbL x v))).

Definition intersection (l1 l2 : list Line) : list Line :=
  List.filter (fun n => List.existsb (eqL n) l2) l1.

Lemma eqL_eq : forall x y:Line, eqL x y = true <-> x=y.
Proof.
  intros x y.
  split.
  destruct x; destruct y; intros H; solve [inversion H | reflexivity ].
intros Hxy; rewrite Hxy; destruct y; solve [trivial].
Qed.

Lemma intersectionL l1 l2 n : In n (intersection l1 l2) <-> In n l1 /\ In n l2.
Proof.
unfold intersection.
rewrite filter_In; rewrite existsb_exists; split.
- intros [H1 [m [H2 e]]]; split; trivial.
  revert e; rewrite eqL_eq; intros e; congruence.
- intros [H1 H2]; split; trivial.
  exists n; split; trivial.
  destruct n; trivial.
Qed.

Definition disjointL (l1 l2:list Line) : bool :=
  match intersection l1 l2 with
  | [] => true
  | _ => false
  end.

Definition disj_7s (A B C D E F G:list Line) : bool :=
  (disjointL A B) && (disjointL A C) && (disjointL A D) && (disjointL A E) && (disjointL A F) && (disjointL A G)
  && (disjointL B C) && (disjointL B D) && (disjointL B E) && (disjointL B F) && (disjointL B G)
  && (disjointL C D) && (disjointL C E) && (disjointL C F) && (disjointL C G)
  && (disjointL D E) &&  (disjointL D F) && (disjointL D G)
  && (disjointL E F) && (disjointL E G)
  && (disjointL F G).

Definition is_packing7 (s1 s2 s3 s4 s5 s6 s7:list Line) : bool :=
  disj_7s s1 s2 s3 s4 s5 s6 s7 &&
          is_partition7 s1 s2 s3 s4 s5 s6 s7.

Lemma is_packing_descr_A :
  forall s1 s2 s3 s4 s5 s6 s7 : list Line, In [s1;s2;s3;s4;s5;s6;s7] packings -> (is_packing7 s1 s2 s3 s4 s5 s6 s7).
Proof.
  intros s1 s2 s3 s4 s5 s6 s7 HIn_P.
  repeat (destruct HIn_P as [HeqL | HIn_P]; [ inversion HeqL; reflexivity | idtac]).
  inversion HIn_P.
Qed.

