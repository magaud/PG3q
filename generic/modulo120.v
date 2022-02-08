Require Import Arith.
Require Import ArithRing.
Require Import Lia.

Lemma modulo_S120 : forall n:nat,
(Nat.modulo n 120 = 119 /\ (Nat.modulo (S n) 120 = 0)) \/ (Nat.modulo (S n) 120 = S (Nat.modulo n 120)).
Proof.
intros n.
pattern n.
pose (P:=(fun n0 : nat => n0 mod 120 = 119 /\ S n0 mod 120 = 0 \/ S n0 mod 120 = S (n0 mod 120))).
fold P.
assert (P (0+n) /\P (1+n) /\P (2+n) /\P (3+n) /\P (4+n) /\P (5+n) /\P (6+n) /\P (7+n) /\P (8+n) /\P (9+n) /\P (10+n) /\P (11+n) /\P (12+n) /\P (13+n) /\P (14+n) /\P (15+n) /\P (16+n) /\P (17+n) /\P (18+n) /\P (19+n) /\P (20+n) /\P (21+n) /\P (22+n) /\P (23+n) /\P (24+n) /\P (25+n) /\P (26+n) /\P (27+n) /\P (28+n) /\P (29+n) /\P (30+n) /\P (31+n) /\P (32+n) /\P (33+n) /\P (34+n) /\P (35+n) /\P (36+n) /\P (37+n) /\P (38+n) /\P (39+n) /\P (40+n) /\P (41+n) /\P (42+n) /\P (43+n) /\P (44+n) /\P (45+n) /\P (46+n) /\P (47+n) /\P (48+n) /\P (49+n) /\P (50+n) /\P (51+n) /\P (52+n) /\P (53+n) /\P (54+n) /\P (55+n) /\P (56+n) /\P (57+n) /\P (58+n) /\P (59+n) /\P (60+n) /\P (61+n) /\P (62+n) /\P (63+n) /\P (64+n) /\P (65+n) /\P (66+n) /\P (67+n) /\P (68+n) /\P (69+n) /\P (70+n) /\P (71+n) /\P (72+n) /\P (73+n) /\P (74+n) /\P (75+n) /\P (76+n) /\P (77+n) /\P (78+n) /\P (79+n) /\P (80+n) /\P (81+n) /\P (82+n) /\P (83+n) /\P (84+n) /\P (85+n) /\P (86+n) /\P (87+n) /\P (88+n) /\P (89+n) /\P (90+n) /\P (91+n) /\P (92+n) /\P (93+n) /\P (94+n) /\P (95+n) /\P (96+n) /\P (97+n) /\P (98+n) /\P (99+n) /\P (100+n) /\P (101+n) /\P (102+n) /\P (103+n) /\P (104+n) /\P (105+n) /\P (106+n) /\P (107+n) /\P (108+n) /\P (109+n) /\P (110+n) /\P (111+n) /\P (112+n) /\P (113+n) /\P (114+n) /\P (115+n) /\P (116+n) /\P (117+n) /\P (118+n) /\P (119+n)).
unfold P.
induction n.
repeat split; try solve [right; simpl; trivial | left; split; reflexivity].
decompose [and] IHn.
repeat split; try assumption.
replace (S (119  + S n)) with ((S n)+(1*120)) by ring.
replace (119  + S n) with (n+(1*120)) by ring.
rewrite PeanoNat.Nat.mod_add.
rewrite PeanoNat.Nat.mod_add.
assumption.
intro; discriminate. 
intro; discriminate.
intuition.
Qed.

