Require Import ssreflect ssrfun ssrbool.

Section hyperplanes.
  
Variable Point : Type.
Variable eq_point : Point -> Point -> bool.

Variable Line : Type.
Variable Incid : Point -> Line -> bool.

Definition pset := Point -> bool.

Definition pempty : pset := fun (x:Point) => false.
Definition pspace : pset := fun (x:Point) => true.
Definition psingleton (x:Point) : pset := fun (y:Point) => eq_point x y.
Definition pline (l:Line) : pset := fun (x:Point) => Incid x l.

Definition Intersect_In (l1 l2 : Line) (P:Point) := Incid P l1 && Incid P l2.
Definition Intersect (l1 l2:Line) := exists P:Point, Incid P l1 && Incid P l2.

Parameter Intersect_dec :
  forall (l1 l2:Line),
    {exists P:Point, Incid P l1 && Incid P l2}+
    {~exists P:Point, Incid P l1 && Incid P l2}.

Check exist.
Print isSome.
Print is_left.
Parameter pplane_dec : forall x:Point, forall (l1 l2 : Line),
    {exists l:Line, (Incid x l && is_left (Intersect_dec l l1) && is_left (Intersect_dec l l2))}+
    {~exists l:Line, (Incid x l && is_left (Intersect_dec l l1) && is_left (Intersect_dec l l2))}.          
                     
Definition pplane (l1 l2 : Line) (H1 : l1<>l2) (H2 : Intersect l1 l2) : pset := 
  fun (x:Point) => is_left (pplane_dec x l1 l2).
