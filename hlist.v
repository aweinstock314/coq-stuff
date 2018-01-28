(*
Coq < Print list.
Inductive list (A : Type) : Type :=
    nil : list A | cons : A -> list A -> list A
*)

Module HList.

Inductive hlist : Type := hnil : hlist | hcons : forall A : Type, A -> hlist -> hlist.
Inductive hlist' : Type := hnil' : hlist' | hcons' (A : Type) : A -> hlist' -> hlist'.

End HList.
Import HList.

Check hcons nat 1 (hcons (list nat) (cons 1 nil) hnil).
