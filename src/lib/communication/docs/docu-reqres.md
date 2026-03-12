# Communication Layer: Request-Response Documentation

This document describes the **request-response** functionality of the DY\* communication layer.
It explains the module structure, the API, the required invariant setup,
and how to write protocol implementations together with corresponding proofs.

A running example is provided by the `DY.Example.RequestResponse.*` modules in the
[communication-layer-examples repository](https://github.com/REPROSEC/dolev-yao-star-communication-layer-examples).

---

## Table of Contents

1. [Overview](#1-overview)
2. [Module Structure](#2-module-structure)
3. [Configuration](#3-configuration)
4. [API Functions](#4-api-functions)
5. [Internal State and Events](#5-internal-state-and-events)
6. [Setting Up Invariants](#6-setting-up-invariants)
7. [Writing Stateful Proofs](#7-writing-stateful-proofs)
8. [Security Properties](#8-security-properties)
9. [Helper Functions](#9-helper-functions)
10. [End-to-End Example Walkthrough](#10-end-to-end-example-walkthrough)

---

## 1. Overview

The request-response layer lets a **client** send a request to a **server** and
receive a response that is cryptographically bound to the original request.

### Message Flow

```
Client                                    Server
  |                                         |
  |--- enc_{pk_server}(request, key) ------>|   (1) send_request
  |                                         |   (2) receive_request
  |                                         |
  |<-------- enc_{key}(response) -----------|   (3) send_response
  |                                         |   (4) receive_response
```

1. The client generates a fresh symmetric (AEAD) key and sends it together with
   the request payload, encrypted under the server's public key (using the core
   communication layer's confidential send).
2. The server decrypts the message, obtains the request and the AEAD key.
3. The server encrypts the response with the AEAD key and sends it back.
4. The client decrypts the response using the AEAD key it generated in step 1.

### Security Guarantees

Assuming neither the client nor the server are corrupt:

| Property | Guarantee |
|---|---|
| **Confidentiality of the request** | Only the server can read the request (PKE). |
| **Confidentiality of the response** | Only client and server know the AEAD key. |
| **Server authentication** | If the client successfully receives a response, the server must have sent it (or one of them is corrupt). |
| **Request-response binding** | The response the client receives is bound to the request it originally sent. |

---

## 2. Module Structure

The request-response functionality is spread across four library modules
and (typically) seven protocol-level modules.

### Library Modules (`DY.Lib.Communication.RequestResponse.*`)

| Module | Purpose |
|---|---|
| `DY.Lib.Communication.RequestResponse` | API functions (`send_request`, `receive_request`, `send_response`, `receive_response`), internal state types, event types, and layer initialisation. |
| `DY.Lib.Communication.RequestResponse.Invariants` | AEAD crypto predicates, state predicates, event predicates, and the `comm_reqres_preds` typeclass that users must instantiate. |
| `DY.Lib.Communication.RequestResponse.Lemmas` | Proofs that every API function preserves the trace invariant (with SMT patterns). Helper lemmas such as `get_response_label_eq_key_label`. |
| `DY.Lib.Communication.RequestResponse.Properties` | Ready-made security-property lemmas (`server_authentication`, `key_secrecy_client`, `response_message_properties`, …). |

### Protocol-Level Modules (Example: `DY.Example.RequestResponse.*`)

| Module | Purpose |
|---|---|
| `Protocol.Total` | Define the application-level message type and the `comm_layer_reqres_config` instance. |
| `Protocol.Stateful` | Protocol state definitions and stateful protocol functions that call the communication-layer API. |
| `Protocol.Total.Proof` | Cryptographic invariant setup (crypto usages, crypto predicates). |
| `Protocol.Stateful.Proof` | State predicates, event predicates (`comm_reqres_preds`), combine all invariants, and prove each protocol step preserves the trace invariant. |
| `SecurityProperties` | High-level security properties (secrecy, authentication) proven from the communication-layer guarantees. |
| `Debug` | An executable test trace that runs the protocol. |
| `Debug.Proof` | Proof that the debug trace preserves the trace invariant. |

---

## 3. Configuration

Before using the request-response API you must provide an instance of the
`comm_layer_reqres_config` typeclass for your application-level message type.

### The `comm_layer_reqres_config` Typeclass

```fstar
class comm_layer_reqres_config (a:Type) = {
  reqres_tag: string;          // unique tag to distinguish this protocol's predicates
  reqres_ps_a: parser_serializer bytes a;  // Comparse parser/serializer for a
}
```

### Example

Define your message type and generate a parser with Comparse, then provide the
instance:

```fstar
module DY.Example.RequestResponse.Protocol.Total

open Comparse
open DY.Core
open DY.Lib

[@@with_bytes bytes]
type request = {
  client: principal;
  nonce: bytes;
}

%splice [ps_request] (gen_parser (`request))
%splice [ps_request_is_well_formed] (gen_is_well_formed_lemma (`request))

[@@with_bytes bytes]
type message_t =
  | Request: request -> message_t
  | Response: bytes -> message_t

%splice [ps_message_t] (gen_parser (`message_t))
%splice [ps_message_t_is_well_formed] (gen_is_well_formed_lemma (`message_t))

instance comm_layer_reqres_config_protocol: comm_layer_reqres_config message_t = {
  reqres_tag = "DY.Lib.Communication.Layer.Reqres.Protocol";
  reqres_ps_a = ps_message_t;
}
```

> **Important:** The `reqres_tag` must be unique across all communication-layer
> instances in your analysis to avoid predicate collisions.

---

## 4. API Functions

All API functions live in `DY.Lib.Communication.RequestResponse` and are
parameterised over a message type `a` with a `comm_layer_reqres_config a`
instance. They are all marked `opaque_to_smt` to ensure proofs go through the
corresponding lemmas rather than unfolding definitions.

### Initialisation

```fstar
val initialize_communication_reqres:
  a:Type -> {|comm_layer_reqres_config a|} ->
  principal -> principal ->
  traceful (option (communication_keys_sess_ids & communication_keys_sess_ids))
```

Sets up PKI keys (public-key encryption and signing) for a client-server pair.
Returns a pair of `communication_keys_sess_ids` — one for each party — that
must be passed to `send_request` / `receive_request`.

### `send_request`

```fstar
val send_request:
  #a:Type0 -> {|comm_layer_reqres_config a|} ->
  communication_keys_sess_ids ->
  principal -> principal -> a ->
  traceful (option (timestamp & comm_meta_data a))
```

Called by the **client**. Internally:

1. Generates a fresh AEAD key with label `comm_label client server`.
2. Triggers a `CommClientSendRequest` event.
3. Stores a `ClientSendRequest` state.
4. Encrypts the request and key under the server's public key via
   `send_confidential` (core layer).

Returns a message id (the `timestamp`) and a `comm_meta_data a` record
that must be kept by the client and passed to `receive_response` later.

### `receive_request`

```fstar
val receive_request:
  #a:Type -> {|comm_layer_reqres_config a|} ->
  communication_keys_sess_ids ->
  principal -> timestamp ->
  traceful (option (a & comm_meta_data a))
```

Called by the **server**. Internally:

1. Decrypts the ciphertext via `receive_confidential` (core layer).
2. Parses the request and the AEAD key.
3. Triggers a `CommServerReceiveRequest` event.
4. Stores a `ServerReceiveRequest` state.

Returns the parsed request payload together with a `comm_meta_data a`
that must be passed to `send_response`.

### `send_response`

```fstar
val send_response:
  #a:eqtype -> {|comm_layer_reqres_config a|} ->
  principal -> comm_meta_data a -> a -> traceful (option timestamp)
```

Called by the **server**. Internally:

1. Retrieves the `ServerReceiveRequest` state via the session id stored in the
   metadata and checks consistency.
2. Triggers a `CommServerSendResponse` event.
3. AEAD-encrypts the response with the key from the metadata
   (authenticated data = server identity).
4. Sends the ciphertext on the network.

### `receive_response`

```fstar
val receive_response:
  #a:Type -> {|comm_layer_reqres_config a|} ->
  principal -> comm_meta_data a -> timestamp ->
  traceful (option (a & comm_meta_data a))
```

Called by the **client**. Internally:

1. Retrieves the `ClientSendRequest` state via the session id in the metadata
   and checks consistency.
2. AEAD-decrypts the response using the key and the server identity as
   authenticated data.
3. Stores a `ClientReceiveResponse` state.
4. Triggers a `CommClientReceiveResponse` event.

### The `comm_meta_data` Record

The opaque `comm_meta_data` record threads context between the four API calls:

```fstar
type comm_meta_data (a:Type) {|config:comm_layer_reqres_config a|} = {
  key: bytes;        // the AEAD key shared between client and server
  server: principal; // the server's identity
  sid: state_id;     // the session id for the communication-layer state
  request: a;        // the original request payload
}
```

The client receives it from `send_request` and passes it to `receive_response`.
The server receives it from `receive_request` and passes it to `send_response`.

### The `communication_keys_sess_ids` Record

```fstar
type communication_keys_sess_ids = {
  pki: state_id;
  private_keys: state_id;
}
```

Obtained from `initialize_communication_reqres`. Each party gets its own
record, pointing to its PKI and private-key state sessions.

---

## 5. Internal State and Events

The communication layer automatically manages its own state and events.
You usually do not interact with these directly, but understanding them is
important for setting up invariants.

### States (`communication_states a`)

```fstar
type communication_states (a:Type) =
  | ClientSendRequest:  client_send_request a  -> communication_states a
  | ServerReceiveRequest: server_receive_request a -> communication_states a
  | ClientReceiveResponse: client_receive_response a -> communication_states a
```

These track the protocol progress and bind the AEAD key to the
client/server/request context.

### Events (`communication_reqres_event a`)

```fstar
type communication_reqres_event (a:Type) =
  | CommClientSendRequest:   client -> server -> request -> key -> …
  | CommServerReceiveRequest: server -> request -> key -> …
  | CommServerSendResponse:  server -> request -> response -> key -> …
  | CommClientReceiveResponse: client -> server -> request -> response -> key -> …
```

Each API function triggers exactly one event. The event predicates
enforce the security-relevant preconditions at each step.

---

## 6. Setting Up Invariants

To obtain the security guarantees from the communication layer you need to
include the layer's predicates in your protocol-level invariants.
This is done across two modules: the *Total Proof* (crypto invariants) and
the *Stateful Proof* (state + event invariants).

### 6.1 Crypto Invariants (Total Proof)

You must include the communication-layer crypto predicates in the
protocol-level lists and use `default_crypto_usages`:

```fstar
val crypto_usages_protocol: crypto_usages
instance crypto_usages_protocol = default_crypto_usages

val pke_pred_list_protocol: list (string & pke_crypto_predicate)
let pke_pred_list_protocol = [
  pke_crypto_predicate_and_tag_communication_layer_reqres message_t;
  // add protocol-specific PKE predicates here
]

val sign_pred_list_protocol: list (string & sign_crypto_predicate)
let sign_pred_list_protocol = [
  sign_crypto_predicate_and_tag_communication_layer_reqres message_t;
  // add protocol-specific sign predicates here
]

val aead_pred_list_protocol: list (string & aead_crypto_predicate)
let aead_pred_list_protocol = [
  aead_crypto_predicate_and_tag_communication_layer_reqres message_t;
  // add protocol-specific AEAD predicates here
]

let crypto_predicates_protocol = {
  default_crypto_predicates with
  pke_pred  = mk_pke_predicate  pke_pred_list_protocol;
  sign_pred = mk_sign_predicate sign_pred_list_protocol;
  aead_pred = mk_aead_predicate aead_pred_list_protocol;
}

instance crypto_invariants_protocol: crypto_invariants = {
  usages = crypto_usages_protocol;
  preds = crypto_predicates_protocol;
}

// Split-predicate boilerplate
let _ = do_split_boilerplate mk_pke_predicate_correct  pke_pred_list_protocol
let _ = do_split_boilerplate mk_sign_predicate_correct sign_pred_list_protocol
let _ = do_split_boilerplate mk_aead_predicate_correct aead_pred_list_protocol
```

> **Note:** `default_crypto_usages` is required — the communication layer
> internally relies on this, in particular for `get_response_label`.

### 6.2 State Predicates (Stateful Proof)

Include the communication-layer state predicate and its update predicate
alongside your protocol state predicate:

```fstar
let all_sessions = [
  pki_tag_and_invariant;
  private_keys_tag_and_invariant;
  state_predicate_and_tag_communication_layer_reqres message_t;
  mk_local_state_tag_and_pred state_predicates_protocol;  // your protocol state predicate
]

let all_state_update_preds = [
  pki_tag_and_state_update_pred;
  private_keys_tag_and_state_update_pred;
  state_update_predicates_communication_layer_and_tag message_t;
  mk_local_state_tag_and_update_pred state_update_predicate_protocol; // your update predicate
]
```

When your protocol state contains a `comm_meta_data` field, use
`comm_client_state_invariant` and `comm_meta_data_knowable_proof` in
the `pred` and `pred_knowable` fields of your state predicate:

```fstar
let state_predicates_protocol: local_state_predicate protocol_state = {
  pred = (fun tr prin sess_id st ->
    match st with
    | ClientSendRequest {server; cmeta_data; nonce} ->
      let client = prin in
      comm_client_state_invariant tr message_t client cmeta_data /\
      is_secret (comm_label client server) tr nonce
    | …
  );
  pred_later = (fun tr1 tr2 prin sess_id st -> ());
  pred_knowable = (fun tr prin sess_id st ->
    match st with
    | ClientSendRequest {server; cmeta_data; nonce} ->
      comm_meta_data_knowable_proof tr message_t protocol_state sess_id st prin cmeta_data
    | …
  );
}
```

### 6.3 Event Predicates (Stateful Proof)

You need to provide an instance of `comm_reqres_preds` for your message type.
This typeclass lets you specify **additional protocol-specific preconditions**
for sending requests and responses.

```fstar
class comm_reqres_preds (a:Type) {| comm_layer_reqres_config a |} = {
  send_request_pred:
    tr:trace -> client:principal -> server:principal -> request:a -> key_label:label -> prop;
  send_request_pred_later: …  // monotonicity proof
  send_response_pred:
    tr:trace -> server:principal -> request:a -> response:a -> key_label:label -> prop;
  send_response_pred_later: …  // monotonicity proof
}
```

Both predicates take a `key_label` argument, which corresponds to the label of
the AEAD key (`comm_label client server`). You can use this label in your
predicates such as `is_well_formed` or `is_knowable_by` conditions.

#### Example

```fstar
let comm_layer_event_preds: comm_reqres_preds message_t = {
  send_request_pred = (fun tr client server (payload:message_t) key_label ->
    match payload with
    | Request {client; nonce} ->
      is_secret (comm_label client server) tr nonce
    | Response _ -> True
  );
  send_request_pred_later = (fun tr1 tr2 client server payload key_label -> ());
  send_response_pred = (fun tr server request response key_label -> True);
  send_response_pred_later = (fun tr1 tr2 server request response key_label -> ());
}
```

If you do not need any additional preconditions, you can leave the predicates
as `True` (or use a default if available).

Then include all events:

```fstar
let all_events =
  event_predicate_communication_layer_reqres_and_tag message_t
```

`event_predicate_communication_layer_reqres_and_tag` produces a list of
`(string & compiled_event_predicate)` that contains both the core
communication-layer events and the request-response events.

### 6.4 Combining Everything

```fstar
let trace_invariants_protocol: trace_invariants = {
  state_pred = mk_state_pred all_sessions;
  state_update_pred = mk_state_update_pred all_state_update_preds;
  event_pred = mk_event_pred all_events;
}

instance protocol_invariants_protocol: protocol_invariants = {
  crypto_invs = crypto_invariants_protocol;
  trace_invs = trace_invariants_protocol;
}
```

Then prove that the global predicates contain all local ones:

```fstar
let _ = (
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst_dtuple all_sessions));
  do_split_boilerplate mk_state_pred_correct all_sessions
)
let _ = (
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst_dtuple all_state_update_preds));
  do_split_boilerplate mk_state_update_pred_correct all_state_update_preds
)
let _ = (
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst all_events));
  do_split_boilerplate mk_event_pred_correct all_events
)
```

Finally, verify that all communication-layer predicates are included:

```fstar
let _: squash (has_communication_layer_reqres_predicates message_t) = ()
```

---

## 7. Writing Stateful Proofs

For each stateful protocol function you write a lemma showing that it
preserves the trace invariant. The communication-layer lemmas in
`DY.Lib.Communication.RequestResponse.Lemmas` have SMT patterns that fire
automatically when the trace invariant holds, but you need to enable them
and provide the correct preconditions.

### 7.1 Enabling SMT Lemmas

The communication layer uses a guard mechanism to scope its SMT lemmas.
Call `enable_reqres_comm_layer_lemmas` once in your module (or the proof
lemmas have SMT patterns that include `reqres_comm_layer_lemmas_enabled a`):

```fstar
val enable_reqres_comm_layer_lemmas:
  a:Type0 -> {|comm_layer_reqres_config a|} ->
  {|comm_reqres_preds a|} ->
  Lemma (reqres_comm_layer_lemmas_enabled a)
```

The proof lemmas for the API functions are:

| API Function | Proof Lemma | Key Precondition |
|---|---|---|
| `send_request` | `send_request_proof` | `send_request_pred`, `is_well_formed` of request |
| `receive_request` | `receive_request_proof` | `trace_invariant`, `has_communication_layer_reqres_predicates` |
| `send_response` | `send_response_proof` | `CommServerReceiveRequest` event triggered, `send_response_pred`, `is_well_formed` of response |
| `receive_response` | `receive_response_proof` | `CommClientSendRequest` event triggered |
| `initialize_communication_reqres` | `initialize_communication_reqres_proof` | `has_private_keys_invariant`, `has_pki_invariant` |

### 7.2 Proving `send_request`

The main obligation is to show that `send_request_pred` holds and that the
request payload is well-formed at the appropriate label:

```fstar
val client_send_request_proof:
  tr:trace ->
  comm_keys_ids:communication_keys_sess_ids ->
  client:principal -> server:principal ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (_, tr_out) = client_send_request comm_keys_ids client server tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant tr);
   SMTPat (client_send_request comm_keys_ids client server tr)]
```

Inside the proof, `send_request_proof` (from the Lemmas module) fires
automatically via SMT patterns when `reqres_comm_layer_lemmas_enabled` holds
and `trace_invariant tr` is in scope. You only need to establish that
`send_request_pred` holds at the point of the call and that any protocol-level
state you set satisfies your `state_predicates_protocol.pred`.

For the protocol state, if you store `comm_meta_data` in your state, use:

```fstar
derive_comm_client_state_invariant tr_out comm_layer_event_preds client cmeta_data
```

to derive `comm_client_state_invariant`.

### 7.3 Proving `receive_request` and `send_response`

After `receive_request` succeeds, the `CommServerReceiveRequest` event is
triggered. This event gives you access to the following properties
(via `request_message_properties` from the Properties module):

- The request is well-formed and knowable by the server.
- Either a legitimate client sent the request (and `send_request_pred` holds),
  **or** the key is publishable (attacker case).

When proving the `send_response` call, you must show:
1. The `CommServerReceiveRequest` event was triggered.
2. `send_response_pred` holds.
3. The response is well-formed at the `get_response_label` of the metadata.

```fstar
send_response_proof tr server req_meta_data response
```

### 7.4 Proving `receive_response`

The main precondition is that the `CommClientSendRequest` event was previously
triggered by the client (which follows from the client's state invariant).
After `receive_response` succeeds, `CommClientReceiveResponse` is triggered,
giving access to the authentication and response-binding properties.

---

## 8. Security Properties

The Properties module (`DY.Lib.Communication.RequestResponse.Properties`)
provides ready-to-use security lemmas. All require `trace_invariant tr`,
`has_communication_layer_reqres_predicates`, and the relevant events to be
triggered.

### Server Authentication

```fstar
val server_authentication:
  tr:trace -> i:timestamp ->
  client:principal -> server:principal ->
  request:a -> response:a -> key:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    event_triggered_at tr i client
      (CommClientReceiveResponse client server request response key)
  )
  (ensures
    (exists request.
      event_triggered (prefix tr i) server
        (CommServerSendResponse server request response key)) \/
    is_corrupt (prefix tr i) (principal_label client) \/
    is_corrupt (prefix tr i) (principal_label server)
  )
```

### Key Secrecy

```fstar
val key_secrecy_client:
  tr:trace ->
  client:principal -> server:principal ->
  key:bytes -> request:a -> response:a ->
  Lemma
  (requires
    attacker_knows tr key /\
    (exists sid. state_was_set tr client sid
      (ClientSendRequest {server; request; key}))
  )
  (ensures
    is_corrupt tr (principal_label client) \/
    is_corrupt tr (principal_label server)
  )
```

### Request-Response Binding

```fstar
val request_response_property:
  tr:trace ->
  client:principal -> server:principal ->
  request:a -> response:a -> key:bytes ->
  Lemma
  (requires
    event_triggered tr client
      (CommClientSendRequest client server request key) /\
    is_secret (comm_label client server) tr key /\
    (exists request'. event_triggered tr server
      (CommServerSendResponse server request' response key)
      \/ is_corrupt …)
  )
  (ensures
    (event_triggered tr server
      (CommServerSendResponse server request response key) /\
     event_triggered tr server
      (CommServerReceiveRequest server request key))
    \/ is_corrupt …
  )
```

This ensures that the response is bound to the *same* request the client
originally sent (since the AEAD key is generated fresh per request and the
`CommClientSendRequest` event is injective in the key).

### Response Payload Properties

```fstar
val response_message_properties:
  tr:trace -> client:principal -> response:a -> req_meta_data:comm_meta_data a ->
  Lemma
  (requires
    event_triggered tr client (CommClientSendRequest …) /\
    event_triggered tr client (CommClientReceiveResponse …)
  )
  (ensures
    is_well_formed a (is_knowable_by (comm_label client server) tr) response /\
    (event_triggered tr server (CommServerSendResponse …) \/
      is_corrupt … ) /\
    send_request_pred tr client server request (get_response_label tr req_meta_data) /\
    (send_response_pred tr server request response (get_response_label tr req_meta_data) \/
      is_corrupt … )
  )
```

There are also fine-grained variants of this lemma
(`response_message_properties_payload`,
`response_message_properties_send_event`,
`response_message_properties_send_request`,
`response_message_properties_send_response`) that expose individual conjuncts.

---

## 9. Helper Functions

### `mk_comm_layer_response_nonce`

```fstar
val mk_comm_layer_response_nonce:
  #a:Type -> {|comm_layer_reqres_config a|} ->
  comm_meta_data a -> usage ->
  traceful (option bytes)
```

Generates a fresh nonce whose label is the `get_response_label` of the
metadata (i.e., `comm_label client server`). Useful when the server needs
to create fresh secret values in its response that should be readable by both
client and server.

A labeled variant is also available:

```fstar
val mk_comm_layer_response_nonce_labeled:
  #a:Type -> {|comm_layer_reqres_config a|} ->
  comm_meta_data a -> usage -> label ->
  traceful (option bytes)
```

This generates a nonce with label `join lab (get_response_label tr req_meta_data)`.

### `get_response_label`

```fstar
val get_response_label:
  tr:trace -> #a:Type0 -> {|comm_layer_reqres_config a|} ->
  comm_meta_data a -> label
```

Returns the label of the AEAD key inside the metadata. In practice this equals
`comm_label client server` (see `get_response_label_eq_key_label` lemma).
Use this when you need to specify the label for values that should be
knowable by both the client and server involved in a request-response exchange.

### `comm_client_state_invariant` and `comm_meta_data_knowable`

```fstar
val comm_client_state_invariant:
  trace -> a:Type -> {|comm_layer_reqres_config a|} ->
  principal -> comm_meta_data a -> prop

val comm_meta_data_knowable:
  trace -> a:Type -> {|comm_layer_reqres_config a|} ->
  principal -> comm_meta_data a -> prop
```

`comm_client_state_invariant` combines key knowability and the
`CommClientSendRequest` event trigger — use it in your protocol state
predicate for any client state that holds a `comm_meta_data`.

`comm_meta_data_knowable_proof` helps discharge `pred_knowable` obligations
for state predicates that contain `comm_meta_data` fields.

---

## 10. End-to-End Example Walkthrough

This section walks through the complete example in the
`DY.Example.RequestResponse.*` modules.

### Step 1: Define Messages (`Protocol.Total`)

```fstar
[@@with_bytes bytes]
type request = { client: principal; nonce: bytes; }

[@@with_bytes bytes]
type message_t =
  | Request: request -> message_t
  | Response: bytes -> message_t

instance comm_layer_reqres_config_protocol: comm_layer_reqres_config message_t = {
  reqres_tag = "DY.Lib.Communication.Layer.Reqres.Protocol";
  reqres_ps_a = ps_message_t;
}
```

### Step 2: Define Protocol State and Functions (`Protocol.Stateful`)

```fstar
[@@with_bytes bytes]
type client_state = {
  server: principal;
  cmeta_data: comm_meta_data message_t;  // communication-layer metadata
  nonce: bytes;
}

// Protocol functions calling the communication-layer API:
val client_send_request:
  communication_keys_sess_ids -> principal -> principal ->
  traceful (option (state_id & timestamp))

val server_receive_request_send_response:
  communication_keys_sess_ids -> principal -> timestamp ->
  traceful (option timestamp)

val client_receive_response:
  principal -> state_id -> timestamp ->
  traceful (option unit)
```

Key points:
- `client_send_request` generates protocol-level secrets (the nonce),
  then calls `send_request` and stores both the protocol state and the
  `comm_meta_data`.
- `server_receive_request_send_response` calls `receive_request`, stores
  protocol state, then calls `send_response`.
- `client_receive_response` retrieves its state to get the `comm_meta_data`,
  calls `receive_response`, and verifies the response content.

### Step 3: Crypto Invariants (`Protocol.Total.Proof`)

Include the three communication-layer predicate lists (PKE, signature, AEAD)
and use `default_crypto_usages`. See [Section 6.1](#61-crypto-invariants-total-proof).

### Step 4: State and Event Invariants (`Protocol.Stateful.Proof`)

1. Define `state_predicates_protocol` using `comm_client_state_invariant` for
   client states (see [Section 6.2](#62-state-predicates-stateful-proof)).
2. Define `comm_reqres_preds` (see [Section 6.3](#63-event-predicates-stateful-proof)).
3. Combine into `protocol_invariants` and prove inclusion
   (see [Section 6.4](#64-combining-everything)).
4. Write proof lemmas for each protocol function
   (see [Section 7](#7-writing-stateful-proofs)).

### Step 5: Security Properties (`SecurityProperties`)

Prove high-level properties using the lemmas from the Properties module:

```fstar
val nonce_secrecy_client:
  tr:trace -> client:principal -> server:principal ->
  cmeta_data:comm_meta_data message_t -> nonce:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    attacker_knows tr nonce /\
    (exists sid. state_was_set tr client sid (ClientSendRequest {server; cmeta_data; nonce}))
  )
  (ensures
    is_corrupt tr (principal_label client) \/
    is_corrupt tr (principal_label server)
  )

val server_authentication:
  tr:trace -> i:timestamp ->
  client:principal -> server:principal ->
  request:message_t -> response:message_t -> key:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    event_triggered_at tr i client
      (CommClientReceiveResponse client server request response key)
  )
  (ensures
    event_triggered (prefix tr i) server
      (CommServerSendResponse server request response key) \/
    is_corrupt (prefix tr i) (principal_label client) \/
    is_corrupt (prefix tr i) (principal_label server)
  )
```

### Step 6: Debug Trace (`Debug` / `Debug.Proof`)

The `Debug` module runs a concrete protocol trace:

```fstar
let debug () : traceful (option unit) =
  let client = "client" in
  let server = "server" in
  let*? ck, sk = initialize_communication_reqres message_t client server in
  let*? (sid, msg_id) = client_send_request ck client server in
  let*? msg_id = server_receive_request_send_response sk server msg_id in
  client_receive_response client sid msg_id
```

The `Debug.Proof` module proves that this trace preserves the trace invariant.
Because all stateful proofs have SMT patterns, the proof is largely automatic:

```fstar
val debug_proof:
  tr:trace ->
  Lemma
  (requires trace_invariant tr)
  (ensures (let (_, tr_out) = debug () tr in trace_invariant tr_out))
```

---

## Quick Reference

| What you need | Where to find it |
|---|---|
| `comm_layer_reqres_config` | `DY.Lib.Communication.Data` |
| `send_request`, `receive_request`, `send_response`, `receive_response` | `DY.Lib.Communication.RequestResponse` |
| `comm_meta_data`, `communication_states`, events | `DY.Lib.Communication.RequestResponse` |
| `comm_reqres_preds` typeclass | `DY.Lib.Communication.RequestResponse.Invariants` |
| Crypto/state/event predicates to include | `DY.Lib.Communication.RequestResponse.Invariants` |
| `send_request_proof`, `receive_response_proof`, … | `DY.Lib.Communication.RequestResponse.Lemmas` |
| `server_authentication`, `response_message_properties`, … | `DY.Lib.Communication.RequestResponse.Properties` |
| `comm_client_state_invariant`, `comm_meta_data_knowable_proof` | `DY.Lib.Communication.RequestResponse.Lemmas` |
| `get_response_label`, `mk_comm_layer_response_nonce` | `DY.Lib.Communication.RequestResponse` |