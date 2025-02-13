module DY.Lib.Communication.RequestResponse.Lemmas

open Comparse
open DY.Core
open DY.Lib.Crypto.PKE.Split
open DY.Lib.Crypto.Signature.Split
open DY.Lib.State.PKI
open DY.Lib.State.PrivateKeys
open DY.Lib.Event.Typed
open DY.Lib.State.Typed

open DY.Lib.Communication.Data
open DY.Lib.Communication.Core
open DY.Lib.Communication.Core.Invariants
open DY.Lib.Communication.Core.Lemmas
open DY.Lib.Communication.Core.Properties
open DY.Lib.Communication.RequestResponse
open DY.Lib.Communication.RequestResponse.Invariants

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Lemmas ***)

val get_response_label: tr:trace -> comm_meta_data -> label
let get_response_label tr req_meta_data = get_label #default_crypto_usages tr req_meta_data.key

val is_comm_response_payload:
  {|crypto_invariants|} ->
  #a:Type -> {| parseable_serializeable bytes a |} ->
  trace -> principal -> comm_meta_data -> a -> prop
let is_comm_response_payload #cusg #a tr server req_meta_data payload =
  is_well_formed a (is_knowable_by (get_response_label tr req_meta_data) tr) payload

val comm_meta_data_knowable: {|crypto_invariants|} -> trace -> principal -> comm_meta_data -> prop
let comm_meta_data_knowable #cinvs tr prin req_meta_data =
  is_knowable_by (principal_label prin) tr req_meta_data.key /\
  is_knowable_by (principal_label prin) tr req_meta_data.request

val apply_reqres_comm_layer_lemmas:
  #a:Type -> {| parseable_serializeable bytes a |} ->
  comm_reqres_higher_layer_event_preds a -> prop
let apply_reqres_comm_layer_lemmas _ = True


val send_request_proof:
  {|protocol_invariants|} ->
  #a:Type -> {| parseable_serializeable bytes a |} ->
  tr:trace ->
  comm_keys_ids:communication_keys_sess_ids ->
  higher_layer_preds:comm_reqres_higher_layer_event_preds a ->
  client:principal -> server:principal -> request:a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_pki_invariant /\
    has_communication_layer_crypto_predicates /\
    has_communication_layer_reqres_event_predicates request_response_event_preconditions higher_layer_preds /\
    has_communication_layer_state_predicates /\
    higher_layer_preds.send_request tr client server request (comm_label client server) /\
    is_well_formed a (is_knowable_by (comm_label client server) tr) request
  )
  (ensures (
    let (_, tr_out) = send_request comm_keys_ids client server request tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant tr);
  SMTPat (apply_reqres_comm_layer_lemmas higher_layer_preds);
  SMTPat (send_request comm_keys_ids client server request tr)]
let send_request_proof #invs #a tr comm_keys_ids higher_layer_preds client server request =
  reveal_opaque (`%send_request) (send_request #a);
  assert(apply_core_comm_layer_lemmas request_response_event_preconditions);
  let request_bytes = serialize #bytes a request in
  match send_request comm_keys_ids client server request tr with
  | (None, tr_out) -> (
    let (key, tr') = mk_rand (AeadKey comm_layer_aead_tag empty) (comm_label client server) 32 tr in
    let (sid, tr') = new_session_id client tr' in
    let ((), tr') = set_state client sid (ClientSendRequest {server; request=request_bytes; key} <: communication_states) tr' in
    higher_layer_preds.send_request_later tr tr' client server request (get_label tr' key);
    ()
  )
  | (Some _, tr_out) -> (
    let (key, tr') = mk_rand (AeadKey comm_layer_aead_tag empty) (comm_label client server) 32 tr in
    let (sid, tr') = new_session_id client tr' in
    let ((), tr') = set_state client sid (ClientSendRequest {server; request=request_bytes; key} <: communication_states) tr' in
    higher_layer_preds.send_request_later tr tr' client server request (get_label tr' key);
    let ((), tr') = trigger_event client (CommClientSendRequest client server request_bytes key) tr' in
    assert(trace_invariant tr');
    let req_payload:com_message_t = RequestMessage {request=(serialize a request); key} in
    let req_payload_bytes = serialize #bytes com_message_t req_payload in
    let (Some msg_id, tr') = send_confidential comm_keys_ids client server req_payload tr' in

    assert(tr_out == tr');
    assert(trace_invariant tr_out);
    ()
  )


#push-options "--ifuel 2 --z3rlimit 50"
val receive_request_proof:
  {|protocol_invariants|} ->
  #a:Type -> {| parseable_serializeable bytes a |} ->
  tr:trace ->
  comm_keys_ids:communication_keys_sess_ids ->
  higher_layer_preds:comm_reqres_higher_layer_event_preds a ->
  server:principal -> msg_id:timestamp ->
  Lemma
  (requires
    trace_invariant tr /\
    has_private_keys_invariant /\
    has_pki_invariant /\
    has_communication_layer_reqres_crypto_predicates /\
    has_communication_layer_reqres_event_predicates request_response_event_preconditions higher_layer_preds /\
    has_communication_layer_state_predicates
  )
  (ensures (
    match receive_request #a comm_keys_ids server msg_id tr with
    | (None, tr_out) -> trace_invariant tr_out
    | (Some (payload, req_meta_data), tr_out) -> (
      let payload_bytes = serialize a payload in
      trace_invariant tr_out /\
      event_triggered tr_out server (CommServerReceiveRequest server payload_bytes req_meta_data.key) /\
      is_well_formed a (is_knowable_by (principal_label server) tr_out) payload /\
      is_well_formed a (is_knowable_by (get_response_label tr_out req_meta_data) tr_out) payload
    )
  ))
  [SMTPat (trace_invariant tr);
  SMTPat (apply_reqres_comm_layer_lemmas higher_layer_preds);
  SMTPat (receive_request #a comm_keys_ids server msg_id tr)]
let receive_request_proof #invs #a tr comm_keys_ids higher_layer_preds server msg_id =
  reveal_opaque (`%receive_request) (receive_request #a);
  assert(apply_core_comm_layer_lemmas request_response_event_preconditions);
  match receive_request #a comm_keys_ids server msg_id tr with
  | (None, tr_out) -> ()
  | (Some (payload, req_meta_data), tr_out) -> (
    let (Some req_msg_t, tr') = receive_confidential #com_message_t comm_keys_ids server msg_id tr in
    let RequestMessage req_msg = req_msg_t in

    let req_msg_bytes = serialize com_message_t req_msg_t in
    let req_send_event client = CommClientSendRequest client server req_msg.request req_msg.key in

    let i = find_event_triggered_at_timestamp tr' server (CommConfReceiveMsg server req_msg_bytes) in
    conf_message_secrecy tr' i request_response_event_preconditions server req_msg_bytes;

    // Properties that can be proved uniformly in both the honest and corrupt case
    eliminate (exists client. event_triggered tr' client (req_send_event client)) \/
              (is_publishable tr' req_msg.request /\ is_publishable tr' req_msg.key)
    returns (
      is_knowable_by (get_response_label tr' req_meta_data) tr' req_msg.request /\
      req_msg.key `has_usage tr'` (AeadKey comm_layer_aead_tag empty)
    )
    with _. eliminate exists client. event_triggered tr' client (req_send_event client)
      returns _
      with _. (
        let i = find_event_triggered_at_timestamp tr' client (req_send_event client) in
        // Triggers event_triggered_at_implies_pred
        assert(event_triggered_at tr' i client (req_send_event client))
      )
    and _. has_usage_publishable tr' req_msg.key (AeadKey comm_layer_aead_tag empty);

    // Relating knowledge of the request to knowledge of its fields
    serialize_parse_inv_lemma #bytes a req_msg.request;
    assert(is_comm_response_payload tr' server req_meta_data payload);

    let ((), tr') = trigger_event server (CommServerReceiveRequest server req_msg.request req_msg.key) tr' in
    let (sid', tr') = new_session_id server tr' in
    let ((), tr') = set_state server sid' (ServerReceiveRequest {request=req_msg.request; key=req_msg.key} <: communication_states) tr' in
    assert(tr' == tr_out);
    assert(trace_invariant tr_out);
    ()
  )
#pop-options


val mk_comm_layer_response_nonce_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  req_meta_data:comm_meta_data -> usg:usage ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_state_predicates /\
    has_communication_layer_reqres_crypto_predicates /\
    bytes_well_formed tr req_meta_data.key
  )
  (ensures (
    match mk_comm_layer_response_nonce req_meta_data usg tr with
    | (None, tr_out) -> trace_invariant tr_out
    | (Some nonce, tr_out) -> (
      is_knowable_by (get_response_label tr_out req_meta_data) tr_out nonce
    )
  ))
let mk_comm_layer_response_nonce_proof #invs tr req_meta_data usg =
  reveal_opaque (`%mk_comm_layer_response_nonce) (mk_comm_layer_response_nonce)


val compute_response_message_proof:
  {|crypto_invariants|} ->
  #a:Type -> {| parseable_serializeable bytes a |} ->
  tr:trace ->
  server:principal ->
  key:bytes -> nonce:bytes -> request:bytes -> response:a ->
  Lemma
  (requires
    has_communication_layer_reqres_crypto_predicates /\
    is_knowable_by (principal_label server) tr key /\
    is_well_formed a (is_knowable_by (get_label tr key) tr) response /\
    is_publishable tr nonce /\
    key `has_usage tr` (AeadKey comm_layer_aead_tag empty) /\
    event_triggered tr server (CommServerSendResponse server request (serialize a response))
  )
  (ensures
    is_publishable tr (compute_response_message #a server key nonce response)
  )
let compute_response_message_proof #cinvs #a tr server key nonce request response =
  reveal_opaque (`%compute_response_message) (compute_response_message #a);
  let res_bytes = serialize a response in
  serialize_wf_lemma a (is_knowable_by (get_label tr key) tr) response;
  let ad:authenticated_data = {server} in
  let ad_bytes = serialize authenticated_data ad in
  serialize_wf_lemma authenticated_data (is_publishable tr) ad;
  let ciphertext = aead_enc key nonce res_bytes ad_bytes in
  // Needed for the case that the key is publishable
  FStar.Classical.move_requires (aead_enc_preserves_publishability tr key nonce res_bytes) ad_bytes;
  serialize_wf_lemma com_message_t (is_publishable tr) (ResponseMessage {nonce; ciphertext});
  ()

val send_response_proof:
  {|protocol_invariants|} ->
  #a:Type -> {| parseable_serializeable bytes a |} ->
  tr:trace ->
  higher_layer_preds:comm_reqres_higher_layer_event_preds a ->
  server:principal -> req_meta_data:comm_meta_data -> response:a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_crypto_predicates /\
    has_communication_layer_reqres_event_predicates request_response_event_preconditions higher_layer_preds /\
    (match parse a req_meta_data.request with
    | None -> False
    | Some request -> higher_layer_preds.send_response tr server request response) /\
    has_communication_layer_state_predicates /\
    is_well_formed a (is_knowable_by (get_response_label tr req_meta_data) tr) response
  )
  (ensures (
    let (_, tr_out) = send_response #a server req_meta_data response tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant tr);
  SMTPat (apply_reqres_comm_layer_lemmas higher_layer_preds);
  SMTPat (send_response server req_meta_data response tr)]
let send_response_proof #invs #a tr higher_layer_preds server req_meta_data response =
  reveal_opaque (`%send_response) (send_response #a);
  match send_response server req_meta_data response tr with
  | (None, tr_out) -> ()
  | (Some msg_id, tr_out) -> (
    let (Some state, tr') = get_state server req_meta_data.sid tr in
    let ServerReceiveRequest srr = state in
    let ((), tr') = trigger_event server (CommServerSendResponse server req_meta_data.request (serialize a response)) tr' in
    let (nonce, tr') = mk_rand NoUsage public 32 tr' in
    compute_response_message_proof tr' server req_meta_data.key nonce req_meta_data.request response;
    let resp_msg_bytes = compute_response_message server req_meta_data.key nonce response in
    let (msg_id, tr') = send_msg resp_msg_bytes tr' in
    assert(tr_out == tr');
    assert(trace_invariant tr_out);
    ()
  )


#push-options "--fuel 0 --ifuel 1 --z3rlimit 10"
val decode_response_proof:
  {|crypto_invariants|} ->
  #a:Type -> {| parseable_serializeable bytes a |} ->
  tr:trace ->
  client:principal -> server:principal ->
  key:bytes -> response:bytes ->
  Lemma
  (requires
    has_communication_layer_reqres_crypto_predicates /\
    is_publishable tr response /\
    is_secret (comm_label client server) tr key /\
    key `has_usage tr` (AeadKey comm_layer_aead_tag empty)
  )
  (ensures (
    match decode_response_message #a server key response with
    | None -> True
    | Some payload -> (
      is_well_formed a (is_knowable_by (get_label tr key) tr) payload /\
      is_knowable_by (get_label tr key) tr (serialize a payload) /\
      (exists request. event_triggered tr server (CommServerSendResponse server request (serialize a payload))
        \/ is_corrupt tr (principal_label client) \/ is_corrupt tr (principal_label server))
    )
  ))
let decode_response_proof #cinvs #a #ps tr client server key msg_bytes =
  reveal_opaque (`%decode_response_message) (decode_response_message #a);
  match decode_response_message #a server key msg_bytes with
  | None -> ()
  | Some payload -> (
    parse_wf_lemma com_message_t (is_publishable tr) msg_bytes;
    let Some (ResponseMessage {nonce; ciphertext}) = parse com_message_t msg_bytes in
    serialize_wf_lemma authenticated_data (is_publishable tr) {server};
    let ad_bytes = serialize authenticated_data {server} in
    let Some res_bytes = aead_dec key nonce ciphertext ad_bytes in
    serialize_parse_inv_lemma #bytes a #ps res_bytes;
    ()
  )
#pop-options

val receive_response_proof:
  {|protocol_invariants|} ->
  #a:Type -> {| parseable_serializeable bytes a |} ->
  tr:trace ->
  higher_layer_preds:comm_reqres_higher_layer_event_preds a ->
  client:principal -> req_meta_data:comm_meta_data -> msg_id:timestamp ->
  Lemma
  (requires
    trace_invariant tr /\
    has_private_keys_invariant /\
    has_pki_invariant /\
    has_communication_layer_reqres_crypto_predicates /\
    has_communication_layer_reqres_event_predicates request_response_event_preconditions higher_layer_preds /\
    has_communication_layer_state_predicates
  )
  (ensures (
    match receive_response #a client req_meta_data msg_id tr with
    | (None, tr_out) -> trace_invariant tr_out
    | (Some (payload, _), tr_out) -> (
      trace_invariant tr_out /\
      event_triggered tr_out client (CommClientReceiveResponse client req_meta_data.server (serialize a payload) req_meta_data.key) /\
      is_well_formed a (is_knowable_by (get_label tr req_meta_data.key) tr) payload
    )
  ))
  [SMTPat (trace_invariant tr);
  SMTPat (apply_reqres_comm_layer_lemmas higher_layer_preds);
  SMTPat (receive_response #a client req_meta_data msg_id tr)]
let receive_response_proof #invs #a tr higher_layer_preds client req_meta_data msg_id =
  reveal_opaque (`%receive_response) (receive_response #a);
  match receive_response #a client req_meta_data msg_id tr with
  | (None, tr_out) -> ()
  | (Some (response, _), tr_out) -> (
    let server = req_meta_data.server in
    let key = req_meta_data.key in
    let (Some state, tr') = get_state client req_meta_data.sid tr in
    let ClientSendRequest csr = state in
    let (Some resp_msg_bytes, tr') = recv_msg msg_id tr' in
    decode_response_proof #invs.crypto_invs #a tr' client csr.server csr.key resp_msg_bytes;
    let Some response = decode_response_message #a csr.server csr.key resp_msg_bytes in
    let ((), tr') = set_state client req_meta_data.sid (ClientReceiveResponse {server=csr.server; response=(serialize a response); key=csr.key} <: communication_states) tr' in
    let ((), tr') = trigger_event client (CommClientReceiveResponse client csr.server (serialize a response) csr.key) tr' in
    assert(event_triggered tr' client (CommClientReceiveResponse client csr.server (serialize a response) csr.key));
    assert(tr_out == tr');
    assert(trace_invariant tr_out);
    ()
  )
