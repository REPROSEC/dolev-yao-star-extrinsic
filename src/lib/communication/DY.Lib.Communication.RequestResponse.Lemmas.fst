module DY.Lib.Communication.RequestResponse.Lemmas

open Comparse
open DY.Core
open DY.Lib.Communication.Core.Extension
open DY.Lib.Crypto.PkEncryption.Split
open DY.Lib.Crypto.Signature.Split
open DY.Lib.State.PKI
open DY.Lib.State.PrivateKeys
open DY.Lib.Event.Typed
open DY.Lib.State.Typed

open DY.Lib.Communication.Core
open DY.Lib.Communication.Core.Invariants
open DY.Lib.Communication.Core.Lemmas
open DY.Lib.Communication.RequestResponse
open DY.Lib.Communication.RequestResponse.Invariants

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Lemmas ***)

val is_comm_response_payload: {|crypto_invariants|} -> trace -> principal -> comm_meta_data -> bytes -> prop
let is_comm_response_payload #cusg tr server req_meta_data payload =
  bytes_invariant tr payload /\
  get_label tr payload `can_flow tr` get_label #default_crypto_usages tr req_meta_data.key /\
  bytes_well_formed tr payload

val get_response_label: tr:trace -> comm_meta_data -> label
let get_response_label tr req_meta_data = get_label #default_crypto_usages tr req_meta_data.key

val comm_meta_data_knowable: {|crypto_invariants|} -> trace -> principal -> comm_meta_data -> prop
let comm_meta_data_knowable #cinvs tr prin req_meta_data =
  is_knowable_by (principal_label prin) tr req_meta_data.key


val compute_request_message_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  client:principal -> server:principal ->
  payload:bytes -> key:bytes ->
  Lemma
  (requires
    is_secret (comm_label client server) tr key /\
    is_knowable_by (comm_label client server) tr payload
  )
  (ensures
    is_knowable_by (comm_label client server) tr (compute_request_message payload key)
  )
let compute_request_message_proof #invs tr client server payload key =
  serialize_wf_lemma request_message (is_knowable_by (comm_label client server) tr) {payload; key};
  ()

val send_request_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  comm_keys_ids:communication_keys_sess_ids ->
  higher_layer_preds:comm_reqres_higher_layer_event_preds ->
  client:principal -> server:principal -> payload:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    has_pki_invariant /\
    has_communication_layer_crypto_predicates /\
    has_communication_layer_reqres_event_predicates request_response_event_preconditions higher_layer_preds /\
    has_communication_layer_state_predicates /\
    higher_layer_preds.send_request tr client server payload (comm_label client server) /\
    is_knowable_by (comm_label client server) tr payload
  )
  (ensures (
    let (_, tr_out) = send_request comm_keys_ids client server payload tr in
    trace_invariant tr_out
  ))
let send_request_proof #invs tr comm_keys_ids higher_layer_preds client server payload =
  match send_request comm_keys_ids client server payload tr with
  | (None, tr_out) -> (
    let (key, tr') = mk_rand (AeadKey comm_layer_aead_tag empty) (comm_label client server) 32 tr in
    let (id, tr') = mk_rand NoUsage (comm_label client server) 32 tr' in
    let (sid, tr') = new_session_id client tr' in
    let ((), tr') = set_state client sid (ClientSendRequest {server; payload; key} <: communication_states) tr' in
    higher_layer_preds.send_request_later tr tr' client server payload (get_label tr' key);
    let ((), tr') = trigger_event client (CommClientSendRequest client server payload key) tr' in
    ()
  )
  | (Some _, tr_out) -> (
    let (key, tr') = mk_rand (AeadKey comm_layer_aead_tag empty) (comm_label client server) 32 tr in
    let (id, tr') = mk_rand NoUsage (comm_label client server) 32 tr' in
    let (sid, tr') = new_session_id client tr' in
    let ((), tr') = set_state client sid (ClientSendRequest {server; payload; key} <: communication_states) tr' in
    higher_layer_preds.send_request_later tr tr' client server payload (get_label tr' key);
    let ((), tr') = trigger_event client (CommClientSendRequest client server payload key) tr' in
    compute_request_message_proof tr' client server payload key;
    let req_payload = compute_request_message payload key in
    send_confidential_proof #invs tr' request_response_event_preconditions comm_keys_ids client server req_payload;   
    let (Some msg_id, tr') = send_confidential comm_keys_ids client server req_payload tr' in

    assert(tr_out == tr');
    assert(trace_invariant tr_out);
    ()
  )


val decode_request_message_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  server:principal -> msg_bytes:bytes ->
  Lemma
  (requires
    exists client. is_knowable_by (comm_label client server) tr msg_bytes
  )
  (ensures (
    match decode_request_message msg_bytes with
    | None -> True
    | Some {payload; key} -> (
      exists client.
        is_knowable_by (comm_label client server) tr payload /\
        is_knowable_by (comm_label client server) tr key
    )
  ))
let decode_request_message_proof #cinvs tr server msg_bytes =
  match decode_request_message msg_bytes with
  | None -> ()
  | Some {payload; key} -> (
    eliminate exists client. is_knowable_by (comm_label client server) tr msg_bytes
    returns (exists client.
        is_knowable_by (comm_label client server) tr payload /\
        is_knowable_by (comm_label client server) tr key)
    with _. (
      parse_wf_lemma request_message (is_knowable_by (comm_label client server) tr) msg_bytes;
     ()
    )
  )

#push-options "--z3rlimit 20"
val receive_request_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  comm_keys_ids:communication_keys_sess_ids ->
  higher_layer_preds:comm_reqres_higher_layer_event_preds ->
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
    match receive_request comm_keys_ids server msg_id tr with
    | (None, tr_out) -> trace_invariant tr_out
    | (Some (payload, req_meta_data), tr_out) -> (
      trace_invariant tr_out /\
      event_triggered tr_out server (CommServerReceiveRequest server payload req_meta_data.key) /\    
      is_comm_response_payload tr_out server req_meta_data payload
    )
  ))
let receive_request_proof #invs tr comm_keys_ids higher_layer_preds server msg_id =
  match receive_request comm_keys_ids server msg_id tr with
  | (None, tr_out) -> ()
  | (Some (payload, req_meta_data), tr_out) -> (
    receive_confidential_proof #invs tr request_response_event_preconditions comm_keys_ids server msg_id;
    let (Some req_msg_bytes, tr') = receive_confidential comm_keys_ids server msg_id tr in
    decode_request_message_proof tr' server req_msg_bytes;
    let Some req_msg = decode_request_message req_msg_bytes in    
    FStar.Classical.move_requires (parse_wf_lemma request_message (is_publishable tr')) req_msg_bytes;
    let ((), tr') = trigger_event server (CommServerReceiveRequest server req_msg.payload req_msg.key) tr' in
    let (sid', tr') = new_session_id server tr' in
    let ((), tr') = set_state server sid' (ServerReceiveRequest {payload=req_msg.payload; key=req_msg.key} <: communication_states) tr' in
    
    assert(tr' == tr_out);
    assert(trace_invariant tr_out);   
    ()
  )
#pop-options


val mk_comm_layer_response_nonce_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  server:principal -> req_meta_data:comm_meta_data -> usg:usage ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_state_predicates /\
    has_communication_layer_reqres_crypto_predicates /\
    bytes_well_formed tr req_meta_data.key
  )
  (ensures (
    match mk_comm_layer_response_nonce server req_meta_data usg tr with
    | (None, tr_out) -> trace_invariant tr_out
    | (Some nonce, tr_out) -> (
      is_comm_response_payload tr_out server req_meta_data nonce
    )
  ))
let mk_comm_layer_response_nonce_proof #invs tr server req_meta_data usg = ()


val compute_response_message_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  server:principal ->
  key:bytes -> nonce:bytes -> payload:bytes ->
  Lemma
  (requires
    has_communication_layer_reqres_crypto_predicates /\
    is_knowable_by (principal_label server) tr key /\
    is_knowable_by (get_label tr key) tr payload /\    
    is_publishable tr nonce /\
    (key `has_usage tr` (AeadKey comm_layer_aead_tag empty) \/
      is_publishable tr key    
    ) /\
    event_triggered tr server (CommServerSendResponse server payload)
  )
  (ensures
    is_publishable tr (compute_response_message server key nonce payload)
  )
let compute_response_message_proof #cinvs tr server key nonce payload =
  let res:response_message = {payload} in
  let res_bytes = serialize response_message res in
  serialize_wf_lemma response_message (is_knowable_by (get_label tr key) tr) res;
  let ad:authenticated_data = {server} in
  let ad_bytes = serialize authenticated_data ad in
  serialize_wf_lemma authenticated_data (is_publishable tr) ad;
  let ciphertext = aead_enc key nonce res_bytes ad_bytes in  
  // Needed for the case that the key is publishable
  FStar.Classical.move_requires (aead_enc_preserves_publishability tr key nonce res_bytes) ad_bytes;
  serialize_wf_lemma response_envelope (is_publishable tr) {nonce; ciphertext};
  ()

val send_response_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  comm_keys_ids:communication_keys_sess_ids ->
  higher_layer_preds:comm_reqres_higher_layer_event_preds ->
  server:principal -> req_meta_data:comm_meta_data -> payload:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_crypto_predicates /\
    has_communication_layer_reqres_event_predicates request_response_event_preconditions higher_layer_preds /\
    higher_layer_preds.send_response tr server payload /\
    has_communication_layer_state_predicates /\
    is_comm_response_payload tr server req_meta_data payload
  )
  (ensures (
    let (_, tr_out) = send_response comm_keys_ids server req_meta_data payload tr in
    trace_invariant tr_out
  ))
let send_response_proof #invs tr comm_keys_ids higher_layer_preds server req_meta_data payload =
  match send_response comm_keys_ids server req_meta_data payload tr with
  | (None, tr_out) -> ()
  | (Some msg_id, tr_out) -> (
    let (Some state, tr') = get_state server req_meta_data.sid tr in
    let ServerReceiveRequest srr = state in    
    let ((), tr') = trigger_event server (CommServerSendResponse server payload) tr' in    
    let (nonce, tr') = mk_rand NoUsage public 32 tr' in
    compute_response_message_proof tr' server req_meta_data.key nonce payload;
    let resp_msg_bytes = compute_response_message server req_meta_data.key nonce payload in
    let (msg_id, tr') = send_msg resp_msg_bytes tr' in
    assert(tr_out == tr');
    assert(trace_invariant tr_out);
    ()
  )


#push-options "--fuel 0 --ifuel 1 --z3rlimit 10"
val decode_response_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  client:principal -> server:principal ->
  key:bytes -> msg_bytes:bytes ->
  Lemma
  (requires
    has_communication_layer_reqres_crypto_predicates /\
    is_publishable tr msg_bytes /\
    is_secret (comm_label client server) tr key /\
    key `has_usage tr` (AeadKey comm_layer_aead_tag empty)
  )
  (ensures (
    match decode_response_message server key msg_bytes with
    | None -> True
    | Some payload -> (
      is_knowable_by (get_label tr key) tr payload /\
      (event_triggered tr server (CommServerSendResponse server payload)
        \/ is_corrupt tr (principal_label client) \/ is_corrupt tr (principal_label server))
    )
  ))
let decode_response_proof #cinvs tr client server key msg_bytes =
  match decode_response_message server key msg_bytes with
  | None -> ()
  | Some payload -> (
    parse_wf_lemma response_envelope (is_publishable tr) msg_bytes;
    let Some {nonce; ciphertext} = parse response_envelope msg_bytes in
    serialize_wf_lemma authenticated_data (is_publishable tr) {server};
    let ad_bytes = serialize authenticated_data {server} in
    let Some res_bytes = aead_dec key nonce ciphertext ad_bytes in
    parse_wf_lemma response_message (is_knowable_by (comm_label client server) tr) res_bytes;
    ()
  )
#pop-options

val receive_response_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  comm_keys_ids:communication_keys_sess_ids ->
  higher_layer_preds:comm_reqres_higher_layer_event_preds ->
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
    match receive_response comm_keys_ids client req_meta_data msg_id tr with
    | (None, tr_out) -> trace_invariant tr_out
    | (Some (payload, _), tr_out) -> (
      trace_invariant tr_out /\
      event_triggered tr_out client (CommClientReceiveResponse client req_meta_data.server payload req_meta_data.key)
    )
  ))
let receive_response_proof #invs tr comm_keys_ids higher_layer_preds client req_meta_data msg_id =
  match receive_response comm_keys_ids client req_meta_data msg_id tr with
  | (None, tr_out) -> ()
  | (Some (payload, _), tr_out) -> (
    let server = req_meta_data.server in
    let key = req_meta_data.key in
    let (Some state, tr') = get_state client req_meta_data.sid tr in
    let ClientSendRequest csr = state in
    let (Some resp_msg_bytes, tr') = recv_msg msg_id tr' in
    decode_response_proof tr' client csr.server csr.key resp_msg_bytes;
    let Some payload = decode_response_message csr.server csr.key resp_msg_bytes in
    let ((), tr') = set_state client req_meta_data.sid (ClientReceiveResponse {server=csr.server; payload; key=csr.key} <: communication_states) tr' in
    let ((), tr') = trigger_event client (CommClientReceiveResponse client csr.server payload csr.key) tr' in

    assert(tr_out == tr');
    assert(trace_invariant tr_out);
    ()
  )
