# Communication Layer Core Documentation

The communication layer core (`DY.Lib.Communication.Core`) provides ready-to-use
send and receive functions for three communication modes:
**confidential**, **authenticated**, and **confidential-authenticated** messaging.
It abstracts away the underlying cryptographic operations (public-key encryption and digital signatures)
and exposes a simple API that protocol developers can use directly in their stateful protocol code.

This document explains the module structure, the API, and the steps required to
integrate the communication layer into a DY\* protocol analysis.

## Module Overview

| Module | Purpose |
|---|---|
| `DY.Lib.Communication.Data` | Shared data types: message formats, configuration typeclass |
| `DY.Lib.Communication.Core` | Send/receive functions and key initialization |
| `DY.Lib.Communication.Core.Invariants` | Crypto predicates, event predicates, and higher-layer predicate hooks |
| `DY.Lib.Communication.Core.Lemmas` | Proof lemmas for every send/receive function (with SMT patterns) |
| `DY.Lib.Communication.Core.Properties` | High-level security properties (secrecy, authentication) |

## Configuration

Every protocol that uses the communication layer must provide a
`comm_layer_core_config` instance for its payload type `a`.
The typeclass is defined in `DY.Lib.Communication.Data`:

```fstar
class comm_layer_core_config (a:Type) = {
  core_tag: string;
  core_ps_a: parser_serializer bytes a;
}
```

- **`core_tag`** – A unique string tag used to derive PKE and signature key tags
  (e.g., `"DY.Lib.Communication.Layer.Core.Protocol"`).
  It must be unique across all protocol instances in the analysis.
- **`core_ps_a`** – A Comparse `parser_serializer` for the payload type `a`.

### Example

Given a protocol message type:

```fstar
[@@with_bytes bytes]
type single_message = {
  secret: bytes;
}

%splice [ps_single_message] (gen_parser (`single_message))
%splice [ps_single_message_is_well_formed] (gen_is_well_formed_lemma (`single_message))
```

The configuration instance is:

```fstar
instance comm_layer_core_config_protocol: comm_layer_core_config single_message = {
  core_tag = "DY.Lib.Communication.Layer.Core.Protocol";
  core_ps_a = ps_single_message;
}
```

## Key Management

### `communication_keys_sess_ids`

The communication layer identifies a principal's keys through a record of
session IDs:

```fstar
type communication_keys_sess_ids = {
  pki: state_id;
  private_keys: state_id;
}
```

These point to the PKI and private-key stores that hold the principal's
long-term encryption and signing keys.

### Initialization

`initialize_communication_core` sets up both principals for communication.
It generates long-term PKE and signing key pairs for the sender and receiver,
installs the corresponding public keys in each other's PKI stores, and returns
the `communication_keys_sess_ids` for both parties:

```fstar
val initialize_communication_core:
  a:Type -> {|comm_layer_core_config a|} ->
  principal -> principal ->
  traceful (option (communication_keys_sess_ids & communication_keys_sess_ids))
```

The key tags are derived from `core_tag` automatically
(`core_tag ^ ".PkEnc.PublicKey"` for PKE, `core_tag ^ ".Sign.PublicKey"` for signatures).

## Send and Receive API

All send functions return `traceful (option timestamp)` (the message ID on success).
All receive functions return a `traceful (option ...)` with the payload or a
`communication_message` record containing `sender`, `receiver`, and `payload` fields.

### Communication Modes

#### Confidential (`send_confidential` / `receive_confidential`)

Provides **confidentiality** of the payload between sender and receiver using
public-key encryption.

```fstar
val send_confidential:
  #a:Type0 -> {|comm_layer_core_config a|} ->
  communication_keys_sess_ids ->
  principal -> principal -> a ->
  traceful (option timestamp)

val receive_confidential:
  #a:Type0 -> {|comm_layer_core_config a|} ->
  communication_keys_sess_ids ->
  principal -> timestamp ->
  traceful (option a)
```

- The sender encrypts the payload with the receiver's public encryption key.
- The sender triggers a `CommConfSendMsg` event before sending.
- The receiver decrypts with their private key and triggers a `CommConfReceiveMsg` event.
- **Security guarantee:** The payload is knowable by the receiver.
  If the payload is not publishable, then some honest sender sent it to that receiver.
- **No sender authentication:** An attacker who knows the receiver's public key
  can encrypt a message to the receiver. Therefore, the receiver cannot
  verify **who** sent the message.

#### Authenticated (`send_authenticated` / `receive_authenticated`)

Provides **sender authentication** using digital signatures.
The payload is sent in the clear (signed, not encrypted).

```fstar
val send_authenticated:
  #a:Type0 -> {|comm_layer_core_config a|} ->
  communication_keys_sess_ids ->
  principal -> principal -> a ->
  traceful (option timestamp)

val receive_authenticated:
  #a:Type0 -> {|comm_layer_core_config a|} ->
  communication_keys_sess_ids ->
  principal -> timestamp ->
  traceful (option (communication_message a))
```

- The sender signs the payload (along with sender/receiver identifiers)
  using their private signing key and triggers a `CommAuthSendMsg` event.
- The receiver extracts the sender from the signed message, looks up the
  sender's verification key, verifies the signature, and triggers
  a `CommAuthReceiveMsg` event.
- **Security guarantee:** Either the stated sender indeed triggered
  `CommAuthSendMsg` with the received payload, or the sender's long-term
  key is corrupt.
- **No confidentiality:** The payload is publishable (sent in the clear).

#### Confidential and Authenticated (`send_confidential_authenticated` / `receive_confidential_authenticated`)

Combines **confidentiality** and **sender authentication** by first encrypting
the payload under the receiver's public key and then signing the ciphertext with
the sender's signing key.

```fstar
val send_confidential_authenticated:
  #a:Type0 -> {|comm_layer_core_config a|} ->
  communication_keys_sess_ids ->
  principal -> principal -> a ->
  traceful (option timestamp)

val receive_confidential_authenticated:
  #a:Type0 -> {|comm_layer_core_config a|} ->
  communication_keys_sess_ids ->
  principal -> timestamp ->
  traceful (option (communication_message a))
```

- The sender encrypts the payload (including sender/receiver identifiers)
  under the receiver's PKE key, signs the ciphertext with the sender's
  signing key, and triggers a `CommConfAuthSendMsg` event.
- The receiver verifies the signature, decrypts, and triggers
  a `CommConfAuthReceiveMsg` event.
- **Security guarantee:** The payload is knowable by sender and receiver.
  Either the stated sender triggered `CommConfAuthSendMsg` with this
  payload, or the sender's long-term key is corrupt.

### Communication Events Summary

The communication layer triggers the following events (defined as the
`communication_core_event` type):

| Event | Triggered by | Parameters |
|---|---|---|
| `CommConfSendMsg` | Sender (confidential) | `sender`, `receiver`, `payload` |
| `CommConfReceiveMsg` | Receiver (confidential) | `receiver`, `payload` |
| `CommAuthSendMsg` | Sender (authenticated) | `sender`, `payload` |
| `CommAuthReceiveMsg` | Receiver (authenticated) | `sender`, `receiver`, `payload` |
| `CommConfAuthSendMsg` | Sender (conf+auth) | `sender`, `receiver`, `payload` |
| `CommConfAuthReceiveMsg` | Receiver (conf+auth) | `sender`, `receiver`, `payload` |

## Setting Up Invariants and Proofs

Using the communication layer in a protocol analysis requires the following
steps. The overall structure mirrors standard DY\* protocol analyses, with
additional hooks for the communication layer predicates.

### Step 1: Define Payload Type and Configuration (Protocol.Total)

Define your message type, generate the Comparse parser, and provide the
`comm_layer_core_config` instance (see [Configuration](#configuration)).

### Step 2: Define States, Events, and Stateful Code (Protocol.Stateful)

Define protocol-specific state and event types as usual.
In the stateful send/receive functions, call the communication layer API
instead of manually constructing cryptographic operations:

```fstar
val send_message:
  communication_keys_sess_ids -> principal -> principal -> state_id ->
  traceful (option timestamp)
let send_message comm_keys_ids sender receiver state_id =
  let*? st: my_state = get_state sender state_id in
  (* ... extract payload from state ... *)
  send_authenticated comm_keys_ids sender receiver payload
  (* or: send_confidential / send_confidential_authenticated *)
```

For receive functions, pattern match on the result. Note that
`receive_confidential` returns `option a` (just the payload),
while `receive_authenticated` and `receive_confidential_authenticated`
return `option (communication_message a)` which includes the `sender` field:

```fstar
val receive_message:
  communication_keys_sess_ids -> principal -> timestamp ->
  traceful (option state_id)
let receive_message comm_keys_ids receiver msg_id =
  let*? msg: communication_message my_type =
    receive_authenticated comm_keys_ids receiver msg_id in
  (* msg.sender, msg.receiver, msg.payload are available *)
  ...
```

### Step 3: Set Up Cryptographic Invariants (Protocol.Total.Proof)

Include the communication layer's crypto predicates in the protocol's
predicate lists:

```fstar
let pke_pred_list_protocol: list (string & pke_crypto_predicate) = [
  pke_crypto_predicates_and_tag_communication_layer_core my_message_type;
  (* ... additional protocol-specific PKE predicates ... *)
]

let sign_pred_list_protocol: list (string & sign_crypto_predicate) = [
  sign_crypto_predicate_and_tag_communication_layer_core my_message_type;
  (* ... additional protocol-specific sign predicates ... *)
]

let crypto_predicates_protocol: crypto_predicates = {
  default_crypto_predicates with
  pke_pred = mk_pke_predicate pke_pred_list_protocol;
  sign_pred = mk_sign_predicate sign_pred_list_protocol;
}

instance crypto_invariants_protocol: crypto_invariants = {
  usages = crypto_usages_protocol;
  preds = crypto_predicates_protocol;
}

let _ = do_split_boilerplate mk_pke_predicate_correct pke_pred_list_protocol
let _ = do_split_boilerplate mk_sign_predicate_correct sign_pred_list_protocol
```

### Step 4: Define Higher-Layer Event Predicates and Trace Invariants (Protocol.Stateful.Proof)

The communication layer provides a hook called
`comm_core_higher_layer_event_preds` that lets the protocol specify
**additional conditions** that must hold whenever a communication layer
event is triggered. This is the key mechanism for connecting protocol-level
invariants to the communication layer's security guarantees.

```fstar
noeq
type comm_core_higher_layer_event_preds (a:Type) {|comm_layer_core_config a|} = {
  send_conf: tr:trace -> sender:principal -> receiver:principal -> payload:a -> prop;
  send_conf_later: ...;   (* monotonicity lemma *)
  send_auth: tr:trace -> sender:principal -> payload:a -> prop;
  send_auth_later: ...;   (* monotonicity lemma *)
  send_conf_auth: tr:trace -> sender:principal -> receiver:principal -> payload:a -> prop;
  send_conf_auth_later: ...; (* monotonicity lemma *)
}
```

Each `send_*` predicate specifies what the protocol must prove before
it is allowed to call the corresponding send function. Each `send_*_later`
is a monotonicity lemma stating that the predicate is preserved as the trace grows.

A `default_comm_core_higher_layer_event_preds` is provided with all predicates
set to `False` — use it as a base and override only the modes your protocol uses.

**Example (authenticated messages):**

```fstar
let comm_layer_event_preds: comm_core_higher_layer_event_preds single_message = {
  default_comm_core_higher_layer_event_preds single_message with
  send_auth = (fun tr sender payload ->
    event_triggered tr sender (SenderSendMsg sender payload)
  );
  send_auth_later = (fun tr1 tr2 sender payload -> ())
}
```

**Example (confidential messages with additional label requirements):**

The `send_conf` predicate can also be used to enforce specific label
constraints on parts of the payload, which can then be leveraged on the
receiver side to establish stronger secrecy properties:

```fstar
let comm_layer_event_preds: comm_core_higher_layer_event_preds single_message = {
  default_comm_core_higher_layer_event_preds single_message with
  send_conf = (fun tr sender receiver (payload: single_message) ->
    event_triggered tr sender (SenderSendMsg sender receiver payload) /\
    is_secret (comm_label sender receiver) tr payload.secret
  );
  send_conf_later = (fun tr1 tr2 sender receiver payload -> ())
}
```

Then assemble the trace invariants as usual, including the communication layer
event predicates in the `all_events` list:

```fstar
let all_events = [
  event_predicate_and_tag_communication_layer_core comm_layer_event_preds;
  mk_event_tag_and_pred event_predicate_protocol
]
```

And include the standard PKI and private-key session invariants in `all_sessions`:

```fstar
let all_sessions = [
  pki_tag_and_invariant;
  private_keys_tag_and_invariant;
  mk_local_state_tag_and_pred state_predicate_protocol;
]
```

### Step 5: Write Stateful Proofs (Protocol.Stateful.Proof)

The communication layer provides proof lemmas with SMT patterns for every
send and receive function. To activate these lemmas for a specific set of
higher-layer predicates, call `enable_core_comm_layer_lemmas` at the
beginning of each proof:

```fstar
let send_message_proof tr comm_keys_ids sender receiver state_id =
  enable_core_comm_layer_lemmas comm_layer_event_preds;
  ()

let receive_message_proof tr comm_keys_ids receiver msg_id =
  enable_core_comm_layer_lemmas comm_layer_event_preds;
  ()
```

The SMT patterns are set up so that once the lemmas are enabled and the
preconditions are met, the proofs often go through with minimal or no
additional manual proof effort.

**Preconditions for send proofs:**

| Function | Preconditions |
|---|---|
| `send_confidential` | `higher_layer_preds.send_conf tr sender receiver payload` and `is_well_formed a (is_knowable_by (comm_label sender receiver) tr) payload` |
| `send_authenticated` | `higher_layer_preds.send_auth tr sender payload` and `is_well_formed a (is_publishable tr) payload` |
| `send_confidential_authenticated` | `higher_layer_preds.send_conf_auth tr sender receiver payload` and `is_well_formed a (is_knowable_by (comm_label sender receiver) tr) payload` |

**Postconditions of receive proofs:**

| Function | Postconditions on success |
|---|---|
| `receive_confidential` | `trace_invariant tr_out`, `CommConfReceiveMsg` event triggered, payload `is_well_formed` and knowable by receiver |
| `receive_authenticated` | `trace_invariant tr_out`, `CommAuthReceiveMsg` event triggered, payload `is_well_formed` and publishable |
| `receive_confidential_authenticated` | `trace_invariant tr_out`, `CommConfAuthReceiveMsg` event triggered |

### Step 6: Prove Security Properties (SecurityProperties)

The module `DY.Lib.Communication.Core.Properties` provides reusable
security property lemmas that can be instantiated for any protocol:

**Confidential messages (`conf_message_properties`):**

Given that a receiver triggered `CommConfReceiveMsg receiver payload`, then:
- The payload is well-formed and knowable by the receiver.
- Either some sender satisfied `higher_layer_preds.send_conf` for this payload,
  or the payload is publishable (i.e., the attacker could have produced it).

**Authenticated messages (`sender_authentication`):**

Given that a receiver triggered `CommAuthReceiveMsg sender receiver payload` at timestamp `i`, then
at `prefix tr i`:
- Either the sender triggered `CommAuthSendMsg sender payload`, or
- The sender's long-term key is corrupt.

**Confidential + Authenticated messages (`confauth_message_properties`):**

Given that a receiver triggered `CommConfAuthReceiveMsg sender receiver payload`, then:
- The payload is well-formed and knowable by `comm_label sender receiver`.
- Either `higher_layer_preds.send_conf_auth` holds for the payload, or
  the sender's long-term key is corrupt.

An alternative variant `confauth_message_properties'` establishes either
the higher-layer predicate holds or the payload is publishable.

## Label: `comm_label`

The communication layer defines a convenience label:

```fstar
val comm_label: principal -> principal -> label
let comm_label sender receiver = join (principal_label sender) (principal_label receiver)
```

This label is used as the confidentiality bound for encrypted payloads.
A value labeled with `comm_label sender receiver` is readable by both the
sender and the receiver (and by anyone who can corrupt either of them).

## Worked Example Overview

The repository includes three minimal examples demonstrating each communication mode:

- **SingleAuthMessage** — sends an authenticated (signed) message using
  `send_authenticated` / `receive_authenticated`.
  Proves sender authentication.
- **SingleConfMessage** — sends a confidential (encrypted) message using
  `send_confidential` / `receive_confidential`.
  Proves secrecy from the sender's perspective. Demonstrates using
  `send_conf` higher-layer predicates to enforce label requirements.
- **SingleConfAuthMessage** — sends a confidential and authenticated message using
  `send_confidential_authenticated` / `receive_confidential_authenticated`.
  Proves both sender authentication and secrecy.

Each example follows the file structure outlined in this document:
`Protocol.Total` (types + config), `Protocol.Stateful` (stateful code),
`Protocol.Total.Proof` (crypto invariants), `Protocol.Stateful.Proof`
(trace invariants + stateful proofs), and `SecurityProperties`
(high-level security lemmas).
