module DY.Core

/// This module groups all the modules of the "core" DY*:
/// this is the minimal set of modules required to
/// write a cryptographic protocol specification
/// and prove its security in the Dolev-Yao model.
/// Although doable, conducting such a proof using only "core" functions and theorems
/// might not be highly convenient.
/// To alleviate this problem,
/// the module DY.Lib will define higher-level and user-friendly
/// functions and theorems above DY.Core.
/// However, to understand the DY* approach of security proofs,
/// it is only necessary to read and understand DY.Core.
///
/// Here is a high-level overview of DY.Core modules,
/// and the DY* approach to symbolic security proofs.
///
/// Participants in a cryptographic protocols can be thought as state machines,
/// that receive some data from the network,
/// modify their internal state,
/// send back a message on the network,
/// then wait for the next message.
/// We could to connect protocol participants with each other via the network,
/// resulting in a honest execution of the protocol.
/// However we are interested in active attacks,
/// therefore the attacker will be in charge of connecting participants with each other,
/// and decide whether to be evil or not,
/// for example by dropping messages,
/// sending some messages twice,
/// or modifying them on the fly.
/// A cryptographic protocol will then be secure,
/// when no matter how the attacker behaves,
/// some security properties are met.
/// These security properties will depend on the protocol being analyzed,
/// but some usual security properties are
/// confidentiality (the attacker cannot compute some secret value)
/// or authentication (if Alice respond to Bob, then Bob initiated conversation with Alice before).
///
/// In DY*, protocols are defined by a set of stateful functions
/// that are run by the different protocol participants.
/// These functions can read and send messages on the network,
/// or store and retrieve state,
/// hence implementing the state machine described above.
/// (These functions are sometimes called "oracles".)
/// The attacker will then be an F* function
/// that may call the various functions defined by the protocol specification,
/// compute cryptographic functions,
/// and so on.
///
/// Because we want to reason on the functions exposed by the protocol,
/// we will not actually have them perform stateful, impure actions
/// (such as sending messages to the actual network).
/// Instead, every impure action performed by the protocol
/// will be stored as an event in a trace (see DY.Core.Trace.Type.trace).
/// The trace is a log of every event that has happened during a protocol execution.
/// From this trace can be deduced many facts,
/// such as the set of bytestrings that can be computed by the attacker
/// (see DY.Core.Attacker.Knowledge.attacker_knows).
/// The security properties of a protocol will then be described
/// as properties met by all the traces that are reachable by a protocol execution.
///
/// Until now, explanations on how to specify a cryptographic protocol
/// and how we express security theorems
/// are standard in symbolic security analysis
/// and is not specific to DY* itself.
///
/// The unique approach of DY* lies in how we prove the security properties.
/// We want to reason on all traces reachable
/// by an attacker interacting with the protocol functions.
/// To do so, we prove that all reachable trace satisfy some trace invariant
/// (see DY.Core.Trace.Invariant.trace_invariant),
/// and then that this trace invariant imply the desired security properties.
/// To prove that all reachable trace satisfy the trace invariant,
/// we prove that every protocol function preserve the trace invariant,
/// hence because every function used by the attacker preserve the invariants,
/// the attacker function has no choice but to preserve the invariants.
///
/// To show that every protocol function preserve the trace invariant,
/// we will prove that every honest participant has a hygienic use of cryptography,
/// for example they may only sign bytestrings that verify some property
/// (which is specific to each protocol, and capture the meaning of the signature),
/// or they may only encrypt messages to keys that are more secret than the message
/// (to ensure you cannot use the ciphertext and the key you know
/// to learn something you are not allowed to).
/// This hygienic use of cryptography will be concretized in the so-called bytes invariant
/// (see DY.Core.Bytes.bytes_invariant),
/// an invariant on all the bytes being used in a protocol execution.
/// The notion of "more secret" will be captured by labels
/// (see DY.Core.Label.Type.label and DY.Core.Label.can_flow).
///
/// In the real world, secret state stored by a participant may leak to the attacker.
/// To capture this, the DY* attacker may corrupt the state of protocol participants,
/// hence extending its knowledge of bytestrings.
/// Therefore, all security properties will be expressed "modulo corruption",
/// for example we will not say that the attacker never knows a secret value,
/// but that the attacker has to perform some corruption
/// in order to compute a secret value.
/// To express this kind of properties,
/// the corruption will be represented as a corruption event in the trace.
/// Therefore, many DY* predicates will depend on the trace to account for such corruptions.
/// All predicates and relations in DY* will satisfy a key property
/// being that they stay true when the trace is extended,
/// i.e. when a propertie is true, is will stay true in the future.
/// For example, if the attacker is able to compute a bytestring now,
/// it will be also able to compute it in the future.

include DY.Core.Attacker.Knowledge
include DY.Core.Label
include DY.Core.Label.Type
include DY.Core.Label.Derived
include DY.Core.Trace.Invariant
include DY.Core.Trace.Manipulation
include DY.Core.Trace.Type
// include Bytes after Trace because of shadowing `length` function
include DY.Core.Bytes
include DY.Core.Bytes.Type

//include DY.Core.Trace.Experiments
include DY.Core.Trace.State.Aux
