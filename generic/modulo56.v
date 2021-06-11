Require Import Arith.
Require Import Lia.

Lemma modulo_S56 : forall n:nat,
(Nat.modulo n 56 = 55 /\ (Nat.modulo (S n) 56 = 0)) \/ (Nat.modulo (S n) 56 = S (Nat.modulo n 56)).
Proof.
intros n.
pattern n.
pose (P:=(fun n0 : nat => n0 mod 56 = 55 /\ S n0 mod 56 = 0 \/ S n0 mod 56 = S (n0 mod 56))).
fold P.
assert (P (0+n) /\P (1+n) /\P (2+n) /\P (3+n) /\P (4+n) /\P (5+n) /\P (6+n) /\P (7+n) /\P (8+n) /\P (9+n) /\P (10+n) /\P (11+n) /\P (12+n) /\P (13+n) /\P (14+n) /\P (15+n) /\P (16+n) /\P (17+n) /\P (18+n) /\P (19+n) /\P (20+n) /\P (21+n) /\P (22+n) /\P (23+n) /\P (24+n) /\P (25+n) /\P (26+n) /\P (27+n) /\P (28+n) /\P (29+n) /\P (30+n) /\P (31+n) /\P (32+n) /\P (33+n) /\P (34+n) /\P (35+n) /\P (36+n) /\P (37+n) /\P (38+n) /\P (39+n) /\P (40+n) /\P (41+n) /\P (42+n) /\P (43+n) /\P (44+n) /\P (45+n) /\P (46+n) /\P (47+n) /\P (48+n) /\P (49+n) /\P (50+n) /\P (51+n) /\P (52+n) /\P (53+n) /\P (54+n) /\P (55+n)).
unfold P.
induction n.
repeat split; try solve [right; simpl; trivial | left; split; reflexivity].
decompose [and] IHn; clear IHn.
repeat (split; [assumption | idtac]).
replace (S (55  + S n)) with ((S n)+(1*56)) by lia.
replace (55  + S n) with (n+(1*56)) by lia.
rewrite PeanoNat.Nat.mod_add.
rewrite PeanoNat.Nat.mod_add.
assumption.
lia.
lia.
intuition.
Qed.

