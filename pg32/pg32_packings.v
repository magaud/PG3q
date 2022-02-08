Require Import ssreflect ssrfun ssrbool.
Require Import Generic.lemmas Generic.wlog.
Require Import PG32.pg32_inductive PG32.pg32_spreads_packings.

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

(*Definition inb := in_dec Point_dec.*)
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
  induction p; revert Hf; repeat rewrite and_bool; intros Hf; tauto.
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

Lemma In_spreads_decomp :
  forall s:list Line, In s spreads ->
                      S0=s \/ S1=s \/ S2=s \/ S3=s \/ S4=s \/ S5=s \/ S6=s \/ S7=s \/ S8=s \/ S9=s \/
                      S10=s \/ S11=s \/ S12=s \/ S13=s \/ S14=s \/ S15=s \/ S16=s \/ S17=s \/ S18=s \/ S19=s \/
                      S20=s \/ S21=s \/ S22=s \/ S23=s \/ S24=s \/ S25=s \/ S26=s \/ S27=s \/ S28=s \/ S29=s \/
                      S30=s \/ S31=s \/ S32=s \/ S33=s \/ S34=s \/ S35=s \/ S36=s \/ S37=s \/ S38=s \/ S39=s \/
                      S40=s \/ S41=s \/ S42=s \/ S43=s \/ S44=s \/ S45=s \/ S46=s \/ S47=s \/ S48=s \/ S49=s \/
                      S50=s \/ S51=s \/ S52=s \/ S53=s \/ S54=s \/ S55=s.
Proof.
  intros s Hs; unfold spreads in Hs.
  repeat (match goal with Hs: In s _ |- _ => inversion Hs;clear Hs; [tauto | idtac] end).
  inversion H0.
Qed.

Definition ltL (x y:Line) := PeanoNat.Nat.ltb (L2nat x) (L2nat y).

Fixpoint ltS (s1 s2: list Line) : bool :=
  match (s1,s2) with
  | ([],_) => false
  | (_,[]) => false
  | (x::xs,y::ys) => (ltL x y) || (eqL x y && ltS xs ys)
  end.
Lemma andb_andP : forall A B C D E F G H I J K L M N O P Q R S T U, A && B && C && D && E &&
        F && G && H && I && 
        J && K && L && M && 
        N && O && P && Q && 
        R && S && T && U -> A /\ B /\ C /\ D /\ E /\
        F /\ G /\ H /\ I /\ 
        J /\ K /\ L /\ M /\ 
        N /\ O /\ P /\ Q /\ 
        R /\ S /\ T /\ U.
Proof.
  intros a b c d e f g h i j k l m n o p q r s t u Hu'.
destruct  (and_bool_lr _ _ Hu') as [Ht' Hu].
destruct (and_bool_lr _ _ Ht') as [Hs' Ht]. 
destruct (and_bool_lr _ _ Hs') as [Hr' Hs].
destruct (and_bool_lr _ _ Hr') as [Hq' Hr].
destruct (and_bool_lr _ _ Hq') as [Hp' Hq].
destruct (and_bool_lr _ _ Hp') as [Ho' Hp].
destruct (and_bool_lr _ _ Ho') as [Hn' Ho].
destruct (and_bool_lr _ _ Hn') as [Hm' Hn].
destruct (and_bool_lr _ _ Hm') as [Hl' Hm].
destruct (and_bool_lr _ _ Hl') as [Hk' Hl].
destruct (and_bool_lr _ _ Hk') as [Hj' Hk].
destruct (and_bool_lr _ _ Hj') as [Hi' Hj].
destruct (and_bool_lr _ _ Hi') as [Hh' Hi].
destruct (and_bool_lr _ _ Hh') as [Hg' Hh].
destruct (and_bool_lr _ _ Hg') as [Hf' Hg].
destruct (and_bool_lr _ _ Hf') as [He' Hf].
destruct (and_bool_lr _ _ He') as [Hd' He].
destruct (and_bool_lr _ _ Hd') as [Hc' Hd].
destruct (and_bool_lr _ _ Hc') as [Hb' Hc].
destruct (and_bool_lr _ _ Hb') as [Ha Hb].
repeat split; assumption.
Qed.

Ltac inversions Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10
     Hd11 Hd12 Hd13 Hd14 Hd15 Hd16 Hd17 Hd18 Hd19 Hd20 Hd21 :=
  solve [inversion Hd1 |
         inversion Hd2 |
         inversion Hd3 |
         inversion Hd4 |
         inversion Hd5 |
         inversion Hd6 |
         inversion Hd7 |
         inversion Hd8 |
         inversion Hd9 |
         inversion Hd10 |
         inversion Hd11 |
         inversion Hd12 |
         inversion Hd13 |
         inversion Hd14 |
         inversion Hd15 |
         inversion Hd16 |
         inversion Hd17 |
         inversion Hd18 |
         inversion Hd19 |
         inversion Hd20 |
         inversion Hd21 ].

Ltac solve_In := solve [apply in_eq | apply in_cons; solve_In].

Definition statement_packings s := forall s2 s3 s4 s5 s6 s7 : list Line,
    In s2 spreads -> In s3 spreads -> In s4 spreads -> In s5 spreads -> In s6 spreads -> In s7 spreads ->
    ltS s s2 -> ltS s2 s3 -> ltS s3 s4 -> ltS s4 s5 -> ltS s5 s6 -> ltS s6 s7 ->
    is_packing7 s s2 s3 s4 s5 s6 s7 -> In [s;s2;s3;s4;s5;s6;s7] packings.
(*
Lemma aux_S0 : statement_packings S0.
Proof.
  intros s2 s3 s4 s5 s6 s7 Hs2 Hs3 Hs4 Hs5 Hs6 Hs7 le12 le23 le34 le45 le56 le67 Hp.
  specialize (and_bool_lr  _ _ Hp) as [Hp1 Hp2]; clear Hp.
  destruct (andb_andP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hp1)
    as [Hd1 [Hd2 [Hd3 [Hd4 [Hd5 [ Hd6 [Hd7 [Hd8 [Hd9 [Hd10 [Hd11 [ Hd12 [Hd13 [Hd14 [Hd15 [Hd16 [Hd17 [Hd18 [Hd19 [Hd20 Hd21]]]]]]]]]]]]]]]]]]]]; clear Hp1 Hp2.
  Set Ltac Profiling.
  (* specialize (and_bool_lr  _ _ Hp2) as [Hp2a Hp2b].
  Search forall_Line.
  rewrite <- forall_forall_Line in Hp2a.
  rewrite <- forall_forall_Line in Hp2b.*)
  decompose [or] (In_spreads_decomp s2 Hs2); clear Hs2; subst s2;
    try solve [inversion le12 | inversions Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10
                                           Hd11 Hd12 Hd13 Hd14 Hd15 Hd16 Hd17 Hd18 Hd19 Hd20 Hd21]; 
    decompose [or] (In_spreads_decomp s3 Hs3); clear Hs3; subst s3;
      try solve [inversion le23 | inversions Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10
                                             Hd11 Hd12 Hd13 Hd14 Hd15 Hd16 Hd17 Hd18 Hd19 Hd20 Hd21].
  (* 225 cases to handle*)
  par:time( decompose [or] (In_spreads_decomp s4 Hs4); clear Hs4; subst s4;
          try solve [inversion le34
                    | inversions Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14 Hd15 Hd16 Hd17 Hd18 Hd19 Hd20 Hd21
                    | (decompose [or] (In_spreads_decomp s5 Hs5); clear Hs5; subst s5;
                       solve  [ inversion le45
                              | inversions Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14 Hd15 Hd16 Hd17 Hd18 Hd19 Hd20 Hd21 
                              | (decompose [or] (In_spreads_decomp s6 Hs6); clear Hs6; subst s6;
                                 solve [inversion le56
                                       | inversions Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14 Hd15 Hd16 Hd17 Hd18 Hd19 Hd20 Hd21
                                       | (decompose [or] (In_spreads_decomp s7 Hs7); clear Hs7; subst s7;
                                          solve [ inversion le67 | inversions Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14 Hd15 Hd16 Hd17 Hd18 Hd19 Hd20 Hd21 | solve_In])])])]).
Qed.
 *)

(*Ltac subst' r := match goal with H:_=r |- _ => rewrite <- H in *; clear H end.*)

Ltac solve_goal1 :=
 let s2 := fresh "s2" in
  let s3 := fresh "s3" in
  let s4 := fresh "s4" in
  let s5 := fresh "s5" in
  let s6 := fresh "s6" in
  let s7 := fresh "s7" in
  let Hs2 := fresh "Hs2" in
  let Hs3 := fresh "Hs3" in
  let Hs4 := fresh "Hs4" in
  let Hs5 := fresh "Hs5" in 
  let Hs6 := fresh "Hs6" in
  let Hs7 := fresh "Hs7" in
  let le12 := fresh "le12" in
  let le23 := fresh "le23" in
  let le34 := fresh "le34" in
  let le45 := fresh "le45" in
  let le56 := fresh "le56" in
  let le67 := fresh "le67" in
  let Hp := fresh "Hp" in
  let Hp1 := fresh "Hp1" in
  let Hp2 := fresh "Hp2" in
  let Hd1 := fresh "Hd1" in
  let Hd2 := fresh "Hd2" in
  let Hd3 := fresh "Hd3" in
  let Hd4 := fresh "Hd4" in
  let Hd5 := fresh "Hd5" in
  let Hd6 := fresh "Hd6" in
  let Hd7 := fresh "Hd7" in
  let Hd8 := fresh "Hd8" in
  let Hd9 := fresh "Hd9" in
  let Hd10 := fresh "Hd10" in
  let Hd11 := fresh "Hd11" in
  let Hd12 := fresh "Hd12" in
  let Hd13 := fresh "Hd13" in
  let Hd14 := fresh "Hd14" in
  let Hd15 := fresh "Hd15" in
  let Hd16 := fresh "Hd16" in
  let Hd17 := fresh "Hd17" in
  let Hd18 := fresh "Hd18" in
  let Hd19 := fresh "Hd19" in
  let Hd20 := fresh "Hd20" in
  let Hd21 := fresh "Hd21" in
  intros s2 s3 s4 s5 s6 s7 Hs2 Hs3 Hs4 Hs5 Hs6 Hs7 le12 le23 le34 le45 le56 le67 Hp;
  destruct (and_bool_lr  _ _ Hp) as [Hp1 Hp2]; clear Hp;
  destruct (andb_andP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hp1)
    as [Hd1 [Hd2 [Hd3 [Hd4 [Hd5 [ Hd6 [Hd7 [Hd8 [Hd9 [Hd10 [Hd11 [ Hd12 [Hd13 [Hd14 [Hd15 [Hd16 [Hd17 [Hd18 [Hd19 [Hd20 Hd21]]]]]]]]]]]]]]]]]]]]; clear Hp1 Hp2;
  decompose [or] (In_spreads_decomp s2 Hs2); clear Hs2; subst s2;
  try solve [inversion le12
            | inversions Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14 Hd15 Hd16 Hd17 Hd18 Hd19 Hd20 Hd21
            ];clear le12;
  decompose [or] (In_spreads_decomp s3 Hs3); clear Hs3; subst s3;
  try solve [inversion le23
        | inversions Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14 Hd15 Hd16 Hd17 Hd18 Hd19 Hd20 Hd21
            ]; clear le23.

Ltac solve_goal2 s4 s5 s6 s7 Hs4 Hs5 Hs6 Hs7 (*le12 le23*) le34 le45 le56 le67 
     (*Hp1 Hp2*) Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14 Hd15 Hd16 Hd17 Hd18 Hd19 Hd20 Hd21 :=
  
  time(decompose [or] (In_spreads_decomp s4 Hs4); clear Hs4; subst s4;
        solve [inversion le34
              | inversions Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14 Hd15 Hd16 Hd17 Hd18 Hd19 Hd20 Hd21
              | (clear le34; decompose [or] (In_spreads_decomp s5 Hs5); clear Hs5; subst s5;
                 solve  [ inversion le45
                        | inversions Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14 Hd15 Hd16 Hd17 Hd18 Hd19 Hd20 Hd21 
                        | (clear le45; decompose [or] (In_spreads_decomp s6 Hs6); clear Hs6; subst s6;
                           solve [inversion le56
                                 | inversions Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14 Hd15 Hd16 Hd17 Hd18 Hd19 Hd20 Hd21
                                 | (clear le56; decompose [or] (In_spreads_decomp s7 Hs7); clear Hs7; subst s7;
                                    solve [ inversion le67 | inversions Hd1 Hd2 Hd3 Hd4 Hd5 Hd6 Hd7 Hd8 Hd9 Hd10 Hd11 Hd12 Hd13 Hd14 Hd15 Hd16 Hd17 Hd18 Hd19 Hd20 Hd21 | solve_In])])])]).
