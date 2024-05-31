module DY.Core.Label.Type

/// This module defines the types associated with labels.
/// It is separated from functions and predicates on labels
/// in order to avoid dependency cycles.

/// Principals are described using strings (such as "Alice").

type principal = string

/// Type for session identifiers

type state_id = { the_id: nat; }

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
  | S: principal -> state_id -> pre_label

/// Labels are roughly a free lattice on pre-labels,
/// with lower bound (meet) and upper bound (join),
/// as well as a minima (secret) and maxima (public).

type label =
  | Secret: label
  | State: pre_label -> label
  | Meet: label -> label -> label
  | Join: label -> label -> label
  | Public: label

open DY.Core.Internal.Ord

instance integer_encodable_pre_label: integer_encodable pre_label = {
  encode = (fun x ->
    match x with
    | P p -> 0::(encode p)
    | S p s -> 1::(encode [encode p; encode s.the_id])
  );
  encode_inj = (fun x y ->
    encode_inj_forall (list (list int)) ();
    encode_inj_forall string ();
    encode_inj_forall nat ()
  );
}

val encode_label: label -> list int
let rec encode_label l =
  match l with
  | Secret -> 0::[]
  | State s -> 1::(encode [encode s])
  | Meet l1 l2 -> 2::(encode [encode_label l1; encode_label l2])
  | Join l1 l2 -> 3::(encode [encode_label l1; encode_label l2])
  | Public -> 4::[]

val encode_label_inj:
  l1:label -> l2:label ->
  Lemma
  (requires encode_label l1 == encode_label l2)
  (ensures l1 == l2)
let rec encode_label_inj l1 l2 =
  introduce forall l1' l2'. l1' << l1 /\ l2' << l2 /\ encode_label l1' == encode_label l2' ==> l1' == l2' with (
    introduce _ ==> _ with _. (
      encode_label_inj l1' l2'
    )
  );
  encode_inj_forall (list (list int)) ();
  encode_inj_forall pre_label ();
  allow_inversion label

instance integer_encodable_label: integer_encodable label = {
  encode = encode_label;
  encode_inj = encode_label_inj;
}
