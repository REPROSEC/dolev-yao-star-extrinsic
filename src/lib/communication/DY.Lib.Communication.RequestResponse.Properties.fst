module DY.Lib.Communication.RequestResponse.Properties

open Comparse
open DY.Core
open DY.Lib.Crypto.PKE.Split
open DY.Lib.Crypto.Signature.Split
open DY.Lib.Event.Typed
open DY.Lib.State.PKI
open DY.Lib.State.PrivateKeys
open DY.Lib.State.Typed

open DY.Lib.Communication.Data
open DY.Lib.Communication.Core
open DY.Lib.Communication.RequestResponse
open DY.Lib.Communication.RequestResponse.Invariants
open DY.Lib.Communication.RequestResponse.Lemmas

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10 --z3cliopt 'smt.qi.eager_threshold=100'"

/// This module contains security properties that can be proven from the
/// communication layer guarantees.

(*** Authentication Security Properties ***)

val server_authentication:
  {|protocol_invariants|} ->
  #a:eqtype -> {| comm_layer_reqres_config a |} ->
  {|comm_reqres_preds a|} ->
  tr:trace -> i:timestamp ->
  client:principal -> response:a -> req_meta_data:comm_meta_data a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_event_predicates a /\
    event_triggered_at tr i client (CommClientReceiveResponse client response req_meta_data <: communication_reqres_event a)
  )
  (ensures
    (exists request. event_triggered (prefix tr i) req_meta_data.server (CommServerSendResponse req_meta_data.client req_meta_data.server request response req_meta_data.key <: communication_reqres_event a)) \/
    is_corrupt (prefix tr i) (principal_label client) \/
    is_corrupt (prefix tr i) (principal_label req_meta_data.server)
  )
let server_authentication #invs #a #config #crpreds tr i client response req_meta_data = ()


(*** Secrecy Security Property ***)

val key_secrecy_client:
  {|protocol_invariants|} ->
  #a:eqtype -> {|comm_layer_reqres_config a|} ->
  tr:trace ->
  client:principal -> client_opt:option principal -> server:principal ->
  key:bytes -> request:a -> response:a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_state_predicate a /\
    attacker_knows tr key /\
    (
      (exists sid authenticated. state_was_set tr client sid (ClientSendRequest {authenticated; client=client_opt; server; request; key} <: communication_states a)) \/
      (exists sid. state_was_set tr client sid (ClientReceiveResponse {server; response; key} <: communication_states a))
    )
  )
  (ensures
    is_corrupt tr (principal_label client) \/ is_corrupt tr (principal_label server)
  )
let key_secrecy_client #tag #invs tr client client_opt server key request response =
  attacker_only_knows_publishable_values tr key;
  ()

(*** Properties ***)

(**** Client Side Lemmas ****)

val send_request_event_properties:
  {|protocol_invariants|} ->
  #a:eqtype -> {|comm_layer_reqres_config a|} ->
  {|crpreds:comm_reqres_preds a|} ->
  tr:trace ->
  client:principal ->
  req_meta_data:comm_meta_data a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_predicates a /\
    (exists authenticated. event_triggered tr client (CommClientSendRequest authenticated client req_meta_data.server req_meta_data.request req_meta_data.key <: communication_reqres_event a))
  )
  (ensures
    is_well_formed a (is_knowable_by (get_response_label tr req_meta_data) tr) req_meta_data.request /\
    comm_label client req_meta_data.server == get_response_label tr req_meta_data /\
    req_meta_data.key `has_usage tr` (AeadKey (comm_layer_aead_tag a) empty) /\
    crpreds.send_request_pred tr client req_meta_data.server req_meta_data.request (get_label tr req_meta_data.key)
  )
let send_request_event_properties #invs #a #config #crpreds tr client req_meta_data =
  eliminate exists authenticated. event_triggered tr client (CommClientSendRequest authenticated client req_meta_data.server req_meta_data.request req_meta_data.key <: communication_reqres_event a)
  returns is_well_formed a (is_knowable_by (get_response_label tr req_meta_data) tr) req_meta_data.request /\
    comm_label client req_meta_data.server == get_response_label tr req_meta_data /\
    req_meta_data.key `has_usage tr` (AeadKey (comm_layer_aead_tag a) empty) /\
    crpreds.send_request_pred tr client req_meta_data.server req_meta_data.request (get_label tr req_meta_data.key)
  with _. (
    let send_event:communication_reqres_event a = CommClientSendRequest authenticated client req_meta_data.server req_meta_data.request req_meta_data.key in
    let j = find_event_triggered_at_timestamp tr client send_event in
    let key_label = get_label tr req_meta_data.key in
    get_response_label_eq_key_label tr req_meta_data;
    crpreds.send_request_pred_later (prefix tr j) tr client req_meta_data.server req_meta_data.request key_label;
    ()
  )

val derive_comm_meta_data_knowable_client:
  {|protocol_invariants|} ->
  #a:eqtype -> {|comm_layer_reqres_config a|} ->
  {|comm_reqres_preds a|} ->
  tr:trace ->
  req_meta_data:comm_meta_data a -> client:principal ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_predicates a /\
    (exists authenticated. event_triggered tr client (CommClientSendRequest authenticated client req_meta_data.server req_meta_data.request req_meta_data.key <: communication_reqres_event a))
  )
  (ensures
    comm_meta_data_knowable tr a client req_meta_data
  )
let derive_comm_meta_data_knowable_client #invs #a #config #crpreds tr req_meta_data client = ()

(**** Server Side Lemmas ****)

val derive_comm_meta_data_knowable_server:
  {|protocol_invariants|} ->
  #a:eqtype -> {|comm_layer_reqres_config a|} ->
  {|comm_reqres_preds a|} ->
  tr:trace ->
  req_meta_data:comm_meta_data a -> server:principal ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_predicates a /\
    event_triggered tr server (CommServerReceiveRequest req_meta_data.client server req_meta_data.request req_meta_data.key <: communication_reqres_event a)
  )
  (ensures
    comm_meta_data_knowable tr a server req_meta_data
  )
let derive_comm_meta_data_knowable_server #invs #a #config #crpreds tr req_meta_data server = ()

#push-options "--z3rlimit 20"
val request_message_properties:
  {|protocol_invariants|} ->
  #a:eqtype -> {|comm_layer_reqres_config a|} ->
  {|crpreds:comm_reqres_preds a|} ->
  tr:trace ->
  req_meta_data:comm_meta_data a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_predicates a /\
    req_meta_data.client == None /\
    event_triggered tr req_meta_data.server (CommServerReceiveRequest req_meta_data.client req_meta_data.server req_meta_data.request req_meta_data.key <: communication_reqres_event a)
  )
  (ensures
    is_well_formed a (is_knowable_by (principal_label req_meta_data.server) tr) req_meta_data.request /\
    is_well_formed a (is_knowable_by (get_response_label tr req_meta_data) tr) req_meta_data.request /\
    is_knowable_by (principal_label req_meta_data.server) tr req_meta_data.key /\
    ((exists client. 
      crpreds.send_request_pred tr client req_meta_data.server req_meta_data.request (get_response_label tr req_meta_data) /\
      comm_label client req_meta_data.server == get_response_label tr req_meta_data
    ) \/ (is_publishable tr req_meta_data.key /\ is_well_formed a (is_publishable tr) req_meta_data.request))
  )
let request_message_properties #invs #a #config #crpreds tr req_meta_data =
  let send_event client:communication_reqres_event a = CommClientSendRequest Unauthenticated client req_meta_data.server req_meta_data.request req_meta_data.key in
  let i = find_event_triggered_at_timestamp tr req_meta_data.server (CommServerReceiveRequest req_meta_data.client req_meta_data.server req_meta_data.request req_meta_data.key <: communication_reqres_event a) in
  let tr_i = prefix tr i in
  let key_label = get_label tr_i req_meta_data.key in
  get_response_label_eq_key_label tr req_meta_data;
  assert(is_well_formed a (is_knowable_by (principal_label req_meta_data.server) tr_i) req_meta_data.request);
  assert(exists client. event_triggered tr_i client (send_event client) \/
            is_publishable tr_i req_meta_data.key);
  eliminate (exists client. event_triggered tr_i client (send_event client)) \/
            is_publishable tr_i req_meta_data.key
  returns
    is_well_formed a (is_knowable_by (principal_label req_meta_data.server) tr) req_meta_data.request /\
    (exists client. 
      crpreds.send_request_pred tr client req_meta_data.server req_meta_data.request key_label /\
      comm_label client req_meta_data.server == get_response_label tr req_meta_data
    ) \/ (is_publishable tr req_meta_data.key /\ is_well_formed a (is_publishable tr) req_meta_data.request)
  with _. eliminate exists client. event_triggered tr_i client (send_event client)
    returns _
    with _. (
      let j = find_event_triggered_at_timestamp tr client (send_event client) in
      find_event_triggered_at_timestamp_later tr_i tr client (send_event client);

      crpreds.send_request_pred_later (prefix tr j) tr client req_meta_data.server req_meta_data.request key_label;
      ()
    )
  and _. ()
#pop-options

val request_message_properties_request:
  {|protocol_invariants|} ->
  #a:eqtype -> {|comm_layer_reqres_config a|} ->
  {|crpreds:comm_reqres_preds a|} ->
  tr:trace ->
  req_meta_data:comm_meta_data a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_predicates a /\
    req_meta_data.client == None /\
    event_triggered tr req_meta_data.server (CommServerReceiveRequest req_meta_data.client req_meta_data.server req_meta_data.request req_meta_data.key <: communication_reqres_event a)
  )
  (ensures
    is_well_formed a (is_knowable_by (principal_label req_meta_data.server) tr) req_meta_data.request
  )
let request_message_properties_request #invs #a #config #crpreds tr req_meta_data =
  request_message_properties #invs #a #config #crpreds tr req_meta_data

val request_message_properties_request':
  {|protocol_invariants|} ->
  #a:eqtype -> {|comm_layer_reqres_config a|} ->
  {|crpreds:comm_reqres_preds a|} ->
  tr:trace ->
  req_meta_data:comm_meta_data a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_predicates a /\
    req_meta_data.client == None /\
    event_triggered tr req_meta_data.server (CommServerReceiveRequest req_meta_data.client req_meta_data.server req_meta_data.request req_meta_data.key <: communication_reqres_event a)
  )
  (ensures
    is_well_formed a (is_knowable_by (get_response_label tr req_meta_data) tr) req_meta_data.request
  )
let request_message_properties_request' #invs #a #config #crpreds tr req_meta_data =
  request_message_properties #invs #a #config #crpreds tr req_meta_data

val request_message_properties_key:
  {|protocol_invariants|} ->
  #a:eqtype -> {|comm_layer_reqres_config a|} ->
  {|crpreds:comm_reqres_preds a|} ->
  tr:trace ->
  req_meta_data:comm_meta_data a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_predicates a /\
    req_meta_data.client == None /\
    event_triggered tr req_meta_data.server (CommServerReceiveRequest req_meta_data.client req_meta_data.server req_meta_data.request req_meta_data.key <: communication_reqres_event a)
  )
  (ensures
    is_knowable_by (principal_label req_meta_data.server) tr req_meta_data.key
  )
let request_message_properties_key #invs #a #config #crpreds tr req_meta_data =
  request_message_properties #invs #a #config #crpreds tr req_meta_data

val request_message_properties_key_well_formed:
  {|protocol_invariants|} ->
  #a:eqtype -> {|comm_layer_reqres_config a|} ->
  {|crpreds:comm_reqres_preds a|} ->
  tr:trace ->
  req_meta_data:comm_meta_data a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_predicates a /\
    req_meta_data.client == None /\
    event_triggered tr req_meta_data.server (CommServerReceiveRequest req_meta_data.client req_meta_data.server req_meta_data.request req_meta_data.key <: communication_reqres_event a)
  )
  (ensures
    bytes_well_formed tr req_meta_data.key
  )
let request_message_properties_key_well_formed #invs #a #config #crpreds tr req_meta_data =
  request_message_properties #invs #a #config #crpreds tr req_meta_data

val request_message_properties_send_request:
  {|protocol_invariants|} ->
  #a:eqtype -> {|comm_layer_reqres_config a|} ->
  {|crpreds:comm_reqres_preds a|} ->
  tr:trace ->
  req_meta_data:comm_meta_data a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_predicates a /\
    req_meta_data.client == None /\
    event_triggered tr req_meta_data.server (CommServerReceiveRequest req_meta_data.client req_meta_data.server req_meta_data.request req_meta_data.key <: communication_reqres_event a)
  )
  (ensures
    (exists client. crpreds.send_request_pred tr client req_meta_data.server req_meta_data.request (get_response_label tr req_meta_data)) \/
    (is_publishable tr req_meta_data.key /\ is_well_formed a (is_publishable tr) req_meta_data.request)
  )
let request_message_properties_send_request #invs #a #config #crpreds tr req_meta_data =
  request_message_properties #invs #a #config #crpreds tr req_meta_data


#push-options "--z3rlimit 20"
val request_message_authenticated_properties:
  {|protocol_invariants|} ->
  #a:eqtype -> {|comm_layer_reqres_config a|} ->
  {|crpreds:comm_reqres_preds a|} ->
  tr:trace ->
  server:principal ->
  req_meta_data:comm_meta_data a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_predicates a /\
    Some? req_meta_data.client /\
    event_triggered tr server (CommServerReceiveRequest req_meta_data.client server req_meta_data.request req_meta_data.key <: communication_reqres_event a)
  )
  (ensures
    is_well_formed a (is_knowable_by (principal_label server) tr) req_meta_data.request /\
    is_well_formed a (is_knowable_by (get_response_label tr req_meta_data) tr) req_meta_data.request /\
    is_knowable_by (principal_label server) tr req_meta_data.key /\
    ((
      crpreds.send_request_pred tr (Some?.v req_meta_data.client) server req_meta_data.request (get_response_label tr req_meta_data) /\
      comm_label (Some?.v req_meta_data.client) server == get_response_label tr req_meta_data
    ) \/ (is_corrupt tr (long_term_key_label (Some?.v req_meta_data.client)) /\ is_publishable tr req_meta_data.key /\ is_well_formed a (is_publishable tr) req_meta_data.request))
  )
let request_message_authenticated_properties #invs #a #config #crpreds tr server req_meta_data =
  let Some client = req_meta_data.client in
  let send_event:communication_reqres_event a = CommClientSendRequest Authenticated client server req_meta_data.request req_meta_data.key in
  let i = find_event_triggered_at_timestamp #(communication_reqres_event a #config) #(event_communication_reqres_event #a #config) tr server (CommServerReceiveRequest req_meta_data.client server req_meta_data.request req_meta_data.key <: communication_reqres_event a) in
  let tr_i = prefix tr i in
  let key_label:label = DY.Core.Bytes.get_label tr_i req_meta_data.key in
  get_response_label_eq_key_label tr req_meta_data;
  assert(event_triggered tr_i client send_event \/ is_corrupt tr (long_term_key_label client));
  eliminate event_triggered tr_i client send_event \/ is_corrupt tr (long_term_key_label client)
  returns
    is_well_formed a #(parseable_serializeable_bytes_a_reqres #a #config) (is_knowable_by #invs.crypto_invs (principal_label server) tr) req_meta_data.request /\
    (
      crpreds.send_request_pred tr client server req_meta_data.request key_label /\
      comm_label client server == get_response_label tr req_meta_data
    ) \/ (is_corrupt tr (long_term_key_label client) /\ is_publishable tr req_meta_data.key /\ is_well_formed a (is_publishable tr) req_meta_data.request)
  with _.
    let j = find_event_triggered_at_timestamp tr client send_event in
    find_event_triggered_at_timestamp_later tr_i tr client send_event;

    crpreds.send_request_pred_later (prefix tr j) tr client server req_meta_data.request key_label;
    ()
  and _. ()
#pop-options

val send_response_event_properties:
  {|protocol_invariants|} ->
  #a:eqtype -> {|comm_layer_reqres_config a|} ->
  {|crpreds:comm_reqres_preds a|} ->
  tr:trace -> client:principal ->
  req_meta_data:comm_meta_data a ->
  response:a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_predicates a /\
    event_triggered tr req_meta_data.server (CommServerSendResponse req_meta_data.client req_meta_data.server req_meta_data.request response req_meta_data.key <: communication_reqres_event a)
  )
  (ensures
    event_triggered tr req_meta_data.server (CommServerReceiveRequest req_meta_data.client req_meta_data.server req_meta_data.request req_meta_data.key <: communication_reqres_event a) /\
    is_well_formed a (bytes_well_formed tr) req_meta_data.request /\
    is_well_formed a (bytes_well_formed tr) response /\
    bytes_well_formed tr req_meta_data.key /\
    crpreds.send_response_pred tr req_meta_data.client req_meta_data.server req_meta_data.request response (get_response_label tr req_meta_data)
  )
let send_response_event_properties #invs #a #config #crpreds tr client req_meta_data response =
  let send_event:communication_reqres_event a = CommServerSendResponse req_meta_data.client req_meta_data.server req_meta_data.request response req_meta_data.key in
  let j = find_event_triggered_at_timestamp tr req_meta_data.server send_event in
  let key_label = get_label tr req_meta_data.key in
  get_response_label_eq_key_label tr req_meta_data;
  crpreds.send_response_pred_later (prefix tr j) tr req_meta_data.client req_meta_data.server req_meta_data.request response key_label;
  ()


(**** Client Side Lemmas ****)

val response_message_properties:
  {|protocol_invariants|} ->
  #a:eqtype -> {|comm_layer_reqres_config a|} ->
  {|crpreds:comm_reqres_preds a|} ->
  tr:trace ->
  client:principal -> response:a -> req_meta_data:comm_meta_data a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_predicates a /\
    event_triggered tr client (CommClientReceiveResponse client response req_meta_data <: communication_reqres_event a)
  )
  (ensures
    is_well_formed a (is_knowable_by (comm_label client req_meta_data.server) tr) response /\
    (event_triggered tr req_meta_data.server (CommServerSendResponse req_meta_data.client req_meta_data.server req_meta_data.request response req_meta_data.key <: communication_reqres_event a) \/
      is_corrupt tr (principal_label client) \/ is_corrupt tr (principal_label req_meta_data.server)) /\
    crpreds.send_request_pred tr client req_meta_data.server req_meta_data.request (get_response_label tr req_meta_data) /\
    (crpreds.send_response_pred tr req_meta_data.client req_meta_data.server req_meta_data.request response (get_response_label tr req_meta_data) \/ 
      is_corrupt tr (principal_label client) \/ is_corrupt tr (principal_label req_meta_data.server))
  )
let response_message_properties #invs #a #config #crpreds tr client response req_meta_data =
  let send_event:communication_reqres_event a = CommServerSendResponse req_meta_data.client req_meta_data.server req_meta_data.request response req_meta_data.key in
  let i = find_event_triggered_at_timestamp tr client (CommClientReceiveResponse client response req_meta_data <: communication_reqres_event a) in
  let tr_i = prefix tr i in
  get_response_label_eq_key_label tr req_meta_data;
  let key_label = get_label tr req_meta_data.key in

  assert(is_well_formed a (is_knowable_by (comm_label client req_meta_data.server) tr) response);

  let j' = find_event_triggered_at_timestamp tr client (CommClientSendRequest (request_authenticated req_meta_data) client req_meta_data.server req_meta_data.request req_meta_data.key <: communication_reqres_event a) in
  assert(crpreds.send_request_pred (prefix tr j') client req_meta_data.server req_meta_data.request (get_label (prefix tr j') req_meta_data.key));
  crpreds.send_request_pred_later (prefix tr j') tr client req_meta_data.server req_meta_data.request (get_label (prefix tr j') req_meta_data.key);

  eliminate (event_triggered tr_i req_meta_data.server send_event) \/
            (is_corrupt tr (principal_label client) \/ is_corrupt tr (principal_label req_meta_data.server))
  returns
    is_well_formed a (is_knowable_by (principal_label req_meta_data.server) tr_i) response /\
    crpreds.send_request_pred tr client req_meta_data.server req_meta_data.request (get_label tr req_meta_data.key) /\
    (
      crpreds.send_response_pred tr req_meta_data.client req_meta_data.server req_meta_data.request response key_label
    ) \/ (
      is_corrupt tr (principal_label client) \/ is_corrupt tr (principal_label req_meta_data.server)
    ) /\
    (crpreds.send_response_pred tr req_meta_data.client req_meta_data.server req_meta_data.request response (get_response_label tr req_meta_data) \/
      (is_publishable tr req_meta_data.key /\ is_well_formed a (is_publishable tr) response))
  with _. (
    let j = find_event_triggered_at_timestamp tr req_meta_data.server send_event in
    crpreds.send_response_pred_later (prefix tr j) tr req_meta_data.client req_meta_data.server req_meta_data.request response key_label;
    ()
  )
  and _. ()

val response_message_properties_payload:
  {|protocol_invariants|} ->
  #a:eqtype -> {|comm_layer_reqres_config a|} ->
  {|crpreds:comm_reqres_preds a|} ->
  tr:trace ->
  client:principal -> response:a -> req_meta_data:comm_meta_data a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_predicates a /\
    event_triggered tr client (CommClientReceiveResponse client response req_meta_data <: communication_reqres_event a)
  )
  (ensures
    is_well_formed a (is_knowable_by (comm_label client req_meta_data.server) tr) response
  )
let response_message_properties_payload #invs #a #config #crpreds tr client response req_meta_data =
  response_message_properties #invs #a #config #crpreds tr client response req_meta_data

val response_message_properties_send_event:
  {|protocol_invariants|} ->
  #a:eqtype -> {|comm_layer_reqres_config a|} ->
  {|crpreds:comm_reqres_preds a|} ->
  tr:trace ->
  client:principal -> response:a -> req_meta_data:comm_meta_data a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_predicates a /\
    event_triggered tr client (CommClientReceiveResponse client response req_meta_data <: communication_reqres_event a)
  )
  (ensures
    event_triggered tr req_meta_data.server (CommServerSendResponse req_meta_data.client req_meta_data.server req_meta_data.request response req_meta_data.key <: communication_reqres_event a) \/
      is_corrupt tr (principal_label client) \/ is_corrupt tr (principal_label req_meta_data.server)
  )
let response_message_properties_send_event #invs #a #config #crpreds tr client response req_meta_data =
  response_message_properties #invs #a #config #crpreds tr client response req_meta_data

val response_message_properties_send_event':
  {|protocol_invariants|} ->
  #a:eqtype -> {|comm_layer_reqres_config a|} ->
  {|crpreds:comm_reqres_preds a|} ->
  tr:trace ->
  client:principal -> response:a -> req_meta_data:comm_meta_data a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_predicates a /\
    event_triggered tr client (CommClientReceiveResponse client response req_meta_data <: communication_reqres_event a)
  )
  (ensures
    event_triggered tr req_meta_data.server (CommServerSendResponse req_meta_data.client req_meta_data.server req_meta_data.request response req_meta_data.key <: communication_reqres_event a) \/
      (is_publishable tr req_meta_data.key /\ is_well_formed a (is_publishable tr) response)
  )
let response_message_properties_send_event' #invs #a #config #crpreds tr client response req_meta_data =
  response_message_properties #invs #a #config #crpreds tr client response req_meta_data

val response_message_properties_send_request:
  {|protocol_invariants|} ->
  #a:eqtype -> {|comm_layer_reqres_config a|} ->
  {|crpreds:comm_reqres_preds a|} ->
  tr:trace ->
  client:principal -> response:a -> req_meta_data:comm_meta_data a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_predicates a /\
    event_triggered tr client (CommClientReceiveResponse client response req_meta_data <: communication_reqres_event a)
  )
  (ensures
    crpreds.send_request_pred tr client req_meta_data.server req_meta_data.request (get_response_label tr req_meta_data)
  )
let response_message_properties_send_request #invs #a #config #crpreds tr client response req_meta_data =
  response_message_properties #invs #a #config #crpreds tr client response req_meta_data

val response_message_properties_send_response:
  {|protocol_invariants|} ->
  #a:eqtype -> {|comm_layer_reqres_config a|} ->
  {|crpreds:comm_reqres_preds a|} ->
  tr:trace ->
  client:principal -> response:a -> req_meta_data:comm_meta_data a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_predicates a /\
    event_triggered tr client (CommClientReceiveResponse client response req_meta_data <: communication_reqres_event a)
  )
  (ensures
    (crpreds.send_response_pred tr req_meta_data.client req_meta_data.server req_meta_data.request response (get_response_label tr req_meta_data) \/ 
      is_corrupt tr (principal_label client) \/ is_corrupt tr (principal_label req_meta_data.server))
  )
let response_message_properties_send_response #invs #a #config #crpreds tr client response req_meta_data =
  response_message_properties #invs #a #config #crpreds tr client response req_meta_data

val response_message_properties_send_response':
  {|protocol_invariants|} ->
  #a:eqtype -> {|comm_layer_reqres_config a|} ->
  {|crpreds:comm_reqres_preds a|} ->
  tr:trace ->
  client:principal -> response:a -> req_meta_data:comm_meta_data a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_predicates a /\
    event_triggered tr client (CommClientReceiveResponse client response req_meta_data <: communication_reqres_event a)
  )
  (ensures
    (crpreds.send_response_pred tr req_meta_data.client req_meta_data.server req_meta_data.request response (get_response_label tr req_meta_data) \/
      (is_publishable tr req_meta_data.key /\ is_well_formed a (is_publishable tr) response))
  )
let response_message_properties_send_response' #invs #a #config #crpreds tr client response req_meta_data =
  response_message_properties #invs #a #config #crpreds tr client response req_meta_data
