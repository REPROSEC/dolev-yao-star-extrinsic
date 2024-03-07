module DY.Core.Label.Type

/// This module defines the types associated with labels.
/// It is separated from functions and predicates on labels
/// in order to avoid dependency cycles.

// TODO remove me, this is an artifact of the previous `can_flow` construction
noeq
type order (a:Type) = {
  rel: a -> a -> prop;
  refl: x:a -> Lemma (rel x x);
  trans: x:a -> y:a -> z:a -> Lemma (requires rel x y /\ rel y z) (ensures rel x z);
}

/// Principals are described using strings (such as "Alice").

type principal = string

/// Pre-labels are used to refer to a particular state of a principal that may be compromised by the attacker,
/// that is, a principal name and a session id (the `S` constructor).
///
/// Pre-labels also include more general labels, such as the `P` constructor
/// that is used to refer to any state of a principal.
/// A pre-label for a principal (`P`) is weaker than a pre-label for principal and state (`S`).
/// This is because `P prin` is considered to be corrupt when there exists any state of `prin` that is corrupt,
/// whereas `S prin sess_id` is corrupt only when this particular state is corrupted by the attacker.
/// For example, Alice may store her long-term private key in some state (with session id 0),
/// and ephemeral keys in another state (with session id 1).
/// If the ephemeral keys state is corrupt by the attacker, then
/// - `P "Alice"` is corrupt
/// - `S "Alice" 0` is not corrupt
/// - `S "Alice" 1` is corrupt.
/// We then see why `P "Alice"` is a weaker pre-label than `S "Alice" 0`.
///
/// Advanced note: `P prin` roughly corresponds to an "infinite join":
/// it is in practice behaving like `join (S prin 0) (join (S prin 1) (join ...))`.
/// It is hard-coded like this because infinite joins are not supported:
/// only finite joins are supported (via the binary join that can be folded on a list).

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

// TODO move me, I am lost and have nothing to do in this file
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

/// Labels are roughly a free lattice on pre-labels,
/// with lower bound (meet) and upper bound (join),
/// as well as a minima (secret) and maxima (public).

type label =
  | Secret: label
  | State: pre_label -> label
  | Meet: label -> label -> label
  | Join: label -> label -> label
  | Public: label
