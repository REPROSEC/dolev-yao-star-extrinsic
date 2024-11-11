module DY.Core.Trace.Type

open DY.Core.Bytes.Type

/// This module defines the trace type.
/// It is separated from functions and predicates on trace (manipulation, invariants)
/// in order to avoid dependency cycles.
///
/// The trace is a log of every event that has happened during a protocol execution,
/// such as messages sent on the network, state storage or corruption by the attacker,
/// as is standard is symbolic analysis tools to express security properties.
///
/// Given a trace, we can for example deduce:
/// - what bytestrings are known by the attacker (see DY.Core.Attacker.Knowledge.attacker_knows),
/// - what principals are corrupt (see DY.Core.Label.is_corrupt),
/// - what protocol steps have been reached by some principals,
/// - and more!
///
/// In turn, the set of traces that are reachable by executions of the protocol
/// can be used to express security properties.
/// For example, confidentiality can often be expressed as:
///   in every trace resulting from an execution of the protocol,
///   if the attacker knows some secret key,
///   then it must have corrupt some principal.
/// As another example, authentication can often be expressed as:
///   in every trace resulting from an execution of the protocol,
///   if Alice has finished a handshake with Bob,
///   then Bob must have initiated a handshake with Alice.
///
/// The trace type is parametrized by the label type
/// as a trick to avoid problems with the positivity checker.
/// See `DY.Core.Label.Type` for more information.

/// Principals are described using strings (such as "Alice").

type principal = string

/// Type for session identifiers

type state_id = { the_id: nat; }

/// a type macro for timestamps (indices on the trace)

type timestamp = nat

/// The type for entries in the trace.

noeq
type trace_entry_ (label_t:Type) =
  // A message has been sent on the network.
  | MsgSent: bytes -> trace_entry_ label_t
  // A random number has been generated, with some usage and label.
  | RandGen: usg:usage -> label_t -> len:nat{len <> 0} -> trace_entry_ label_t
  // A state of a principal has been corrupt.
  | Corrupt: time:timestamp -> trace_entry_ label_t
  // A principal stored some state.
  | SetState: prin:principal -> sess_id:state_id -> content:bytes -> trace_entry_ label_t
  // A custom and protocol-specific event has been triggered by a principal.
  | Event: prin:principal -> tag:string -> content:bytes -> trace_entry_ label_t

/// The trace is a list of trace entries.
/// Because the trace grows with time and the time is often represented going from left to right,
/// the trace is actually a reversed list.
/// To avoid confusions, we define a custom inductive to swap the arguments of the "cons" constructor.

noeq
type trace_ (label_t:Type) =
  | Nil: trace_ label_t
  | Snoc: trace_ label_t -> trace_entry_ label_t -> trace_ label_t
