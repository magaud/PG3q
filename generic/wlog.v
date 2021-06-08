Require Import Setoid ssrbool ssreflect.
Require Import Generic.lemmas.
   
Lemma wrapperAB : forall S:Type, forall A B:S,forall le:S->S->bool, forall le_total:(forall x y:S, le x y || le y x), forall P:S-> S -> Type, forall Pwlog:(forall x y:S, le x y -> P x y), forall Psym:(forall x y:S,  P y x -> P x y),  P A B.
  Proof.
    intros S A B le le_total P Pwlog Psym; 
      destruct (Bool.orb_true_elim _ _ (le_total A B)) as [i | i];
    [exact (Pwlog _ _ i) | exact  (Psym _ _ (Pwlog _ _ i))].
  Defined.

(*Ltac revert_all_except1 x :=
  repeat match goal with
           [ H : _ |- _ ]  =>
           match H with x => fail 1 | _ => revert H end end.

Ltac revert_all_except2 x y :=
  repeat match goal with
           [ H : _ |- _ ]  =>
           match H with x => fail 1 | y=> fail 1 | _ => revert H end end.

Ltac revert_all_except3 x y  z:=
  repeat match goal with
           [ H : _ |- _ ]  =>
           match H with x => fail 1 | y => fail 1 | z => fail 1 | _ => revert H end end.
*)

Ltac wlog2 vA vB vle vle_total tac_sym tac_wlog:=
  let X:= fresh "X" in
  let Y:= fresh "Y" in
  let Xsym := fresh "Xsym" in
  let Xle := fresh "Xle" in
  pattern vA,vB; 
  match goal with vA:?ty |- (?P vA vB) =>
                  cbv beta;
                  revert vA vB; 
                  assert (Xle:forall x y:ty, vle x y -> P x y);
                  [first [tac_wlog | idtac "You have to prove " Xle "."] |
                   assert (Xsym:forall x y:ty, P y x -> P x y);
                   [first [tac_sym |  idtac "You have to prove " Xsym "."] |
                    intros X Y; apply (wrapperAB  _ X Y vle vle_total _ Xle Xsym)
                  ]]
  end.

Lemma wrapABC : forall S:Type, forall A B C:S,
      forall le:S->S->bool, forall le_total:(forall x y:S, le x y || le y x),
          forall P:S->S->S->Type,
            forall Pwlog: (forall x y z : S, le x y && le y z -> P x y z),
      (forall x y z : S, P x z y -> P x y z) ->
      (forall x y z : S, P y x z -> P x y z) ->
      (forall x y z : S, P y z x -> P x y z) ->
      (forall x y z : S, P z x y -> P x y z) ->
      (forall x y z : S, P z y x -> P x y z) ->
      P A B C.
Proof.
  intros S A B C le le_total P Pwlog Psym1 Psym2 Psym3 Psym4 Psym5;
    destruct (Bool.orb_true_elim _ _ (le_total A B)) as [i | i];
    destruct (Bool.orb_true_elim _ _ (le_total A C)) as [j | j];
    destruct (Bool.orb_true_elim _ _ (le_total B C)) as [k | k];
    [
      apply Pwlog; try rewrite i; try rewrite j; try rewrite k; reflexivity
    | apply Psym1; apply Pwlog; try rewrite i; try rewrite j; try rewrite k; reflexivity
    | apply Pwlog; try rewrite i; try rewrite j; try rewrite k; reflexivity
    | apply Psym4; apply Pwlog; try rewrite i; try rewrite j; try rewrite k; reflexivity
    | apply Psym2; apply Pwlog; try rewrite i; try rewrite j; try rewrite k; reflexivity
    | apply Psym2; apply Pwlog; try rewrite i; try rewrite j; try rewrite k; reflexivity
    | apply Psym3; apply Pwlog; try rewrite i; try rewrite j; try rewrite k; reflexivity
    | apply Psym5; apply Pwlog; try rewrite i; try rewrite j; try rewrite k; reflexivity
    ].
Qed.

Ltac wlog3 vA vB vC vle vle_total tac_sym tac_wlog :=
  let X:= fresh "A" in
  let Y:= fresh "B" in
  let Z:= fresh "C" in
  let Xsym := fresh "Xsym" in
  let Xsym1 := fresh "Xsym1" in
  let Xsym2 := fresh "Xsym2" in
  let Xle := fresh "Xle" in
  pattern vA,vB,vC; 
  match goal with vA:?ty |- (?P vA vB vC) =>
                  cbv beta;
                  revert vA vB vC;
                  assert (Xle:forall A B C:ty, vle A B && vle B C -> P A B C) ;
                  [ tac_wlog |
                    intros X Y Z; apply (wrapABC _ X Y Z vle vle_total _ Xle);clear Xle; tac_sym]
  end.
