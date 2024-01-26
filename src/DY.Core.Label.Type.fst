module DY.Core.Label.Type

noeq
type order (a:Type) = {
  rel: a -> a -> prop;
  refl: x:a -> Lemma (rel x x);
  trans: x:a -> y:a -> z:a -> Lemma (requires rel x y /\ rel y z) (ensures rel x z);
}

type principal = string

type pre_label =
  | P: principal -> pre_label
  | S: principal -> nat -> pre_label

val get_principal: pre_label -> option principal
let get_principal l =
  match l with
  | P p -> Some p
  | S p _ -> Some p

val get_session: pre_label -> option nat
let get_session l =
  match l with
  | P _ -> None
  | S _ s -> Some s

val pre_label_order: order pre_label
let pre_label_order = {
  rel = (fun x y ->
    match y with
    | P p -> Some p == get_principal x
    | S p s -> Some p == get_principal x /\ Some s == get_session x
  );
  refl = (fun x -> ());
  trans = (fun x y z -> ());
}

type label =
  | Secret: label
  | State: pre_label -> label
  | Meet: label -> label -> label
  | Join: label -> label -> label
  | Public: label
