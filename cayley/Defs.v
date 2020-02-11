
Definition π1 {A : Type} {P : A -> Prop} (x : {x | P x}) : A        := proj1_sig x.
Definition π2 {A : Type} {P : A -> Prop} (x : {x | P x}) : P (π1 x) := proj2_sig x.
