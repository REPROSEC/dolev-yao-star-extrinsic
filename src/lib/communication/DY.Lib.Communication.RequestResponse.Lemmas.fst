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

val compute_request_message_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  client:principal -> server:principal ->
  id:bytes -> payload:bytes -> key:bytes ->
  Lemma
  (requires
    is_secret (comm_label client server) tr id /\
    is_secret (comm_label client server) tr key /\
    is_knowable_by (comm_label client server) tr payload
  )
  (ensures
    is_knowable_by (comm_label client server) tr (compute_request_message client id payload key)
  )
let compute_request_message_proof #invs tr client server id payload key =
  serialize_wf_lemma request_message (is_knowable_by (comm_label client server) tr) {client; id; payload; key};
  ()

//#push-options "--fuel 4 --ifuel 4 --z3rlimit 50"
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
    let ((), tr') = set_state client sid (ClientSendRequest {id; server; payload; key} <: communication_states) tr' in
    higher_layer_preds.send_request_later tr tr' client server payload (get_label tr' key);
    let ((), tr') = trigger_event client (CommClientSendRequest client server id payload key) tr' in
    ()
  )
  | (Some _, tr_out) -> (
    let (key, tr') = mk_rand (AeadKey comm_layer_aead_tag empty) (comm_label client server) 32 tr in
    let (id, tr') = mk_rand NoUsage (comm_label client server) 32 tr' in
    
    let (sid, tr') = new_session_id client tr' in
    let ((), tr') = set_state client sid (ClientSendRequest {id; server; payload; key} <: communication_states) tr' in
    
    higher_layer_preds.send_request_later tr tr' client server payload (get_label tr' key);
    assert(is_knowable_by (comm_label client server) tr' payload);
    assert(higher_layer_preds.send_request tr' client server payload (get_label tr' key));
    let ((), tr') = trigger_event client (CommClientSendRequest client server id payload key) tr' in
    assert(event_triggered tr' client (CommClientSendRequest client server id payload key));
    assert(trace_invariant tr');

    compute_request_message_proof tr' client server id payload key;
    let req_payload = compute_request_message client id payload key in

    assert(request_response_event_preconditions.send_conf tr' client server req_payload);
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
    | Some {id; client=client'; payload; key} -> (
      exists client.
        is_knowable_by (comm_label client server) tr id /\
        is_knowable_by (comm_label client server) tr payload /\
        is_knowable_by (comm_label client server) tr key
    )
  ))
let decode_request_message_proof #cinvs tr server msg_bytes =
  match decode_request_message msg_bytes with
  | None -> ()
  | Some {id; client=client'; payload; key} -> (
    eliminate exists client. is_knowable_by (comm_label client server) tr msg_bytes
    returns (exists client.
        is_knowable_by (comm_label client server) tr id /\
        is_knowable_by (comm_label client server) tr payload /\
        is_knowable_by (comm_label client server) tr key)
    with _. (
      parse_wf_lemma request_message (is_knowable_by (comm_label client server) tr) msg_bytes;
     ()
    )
  )

val is_comm_response_payload: {|crypto_invariants|} -> trace -> principal -> state_id -> bytes -> prop
let is_comm_response_payload #cusg tr server sid payload =
  match get_state server sid tr with
  | (None, _) -> False
  | (Some state, tr) -> (
    match state with
    | ServerReceiveRequest {id; client; payload=payload'; key} -> (
      bytes_invariant tr payload /\
      get_label tr payload `can_flow tr` get_label #default_crypto_usages tr key /\
      bytes_well_formed tr payload
    )
    | _ -> False
  )

//#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
#push-options "--fuel 1 --ifuel 3 --z3rlimit 500"
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
    | (Some (sid, payload, client, id, key), tr_out) -> (
      trace_invariant tr_out /\
      (*exists client. 
        is_knowable_by (comm_label client server) tr_out payload) /\*)
      event_triggered tr_out server (CommServerReceiveRequest client server id payload key) // /\
      //state_was_set tr_out server sid (ServerReceiveRequest {id; client; payload; key} <: communication_states)     
      //is_comm_response_payload tr_out server sid payload
    )
  ))
let receive_request_proof #invs tr comm_keys_ids higher_layer_preds server msg_id =
  match receive_request comm_keys_ids server msg_id tr with
  | (None, tr_out) -> ()
  | (Some (sid, payload, client, id, key), tr_out) -> (
    receive_confidential_proof #invs tr request_response_event_preconditions comm_keys_ids server msg_id;
    let (Some req_msg_bytes, tr') = receive_confidential comm_keys_ids server msg_id tr in
    decode_request_message_proof tr' server req_msg_bytes;
    let Some req_msg = decode_request_message req_msg_bytes in    
    FStar.Classical.move_requires (parse_wf_lemma request_message (is_publishable tr')) req_msg_bytes;        
    (*assert(trace_invariant tr');
    assert(exists client.
      request_response_event_preconditions.send_conf tr' client server req_msg_bytes \/
      is_publishable tr' req_msg_bytes
    );

    assert(exists client.
      event_triggered tr' client (CommClientSendRequest client server id payload req_msg.key) \/
        is_publishable tr' req_msg.key
    );
    assert(is_knowable_by (get_label tr req_msg.key) tr' req_msg.id);*)

    let ((), tr') = trigger_event server (CommServerReceiveRequest req_msg.client server req_msg.id req_msg.payload req_msg.key) tr' in
    assert(event_triggered tr' server (CommServerReceiveRequest req_msg.client server req_msg.id req_msg.payload req_msg.key));

    let (sid', tr') = new_session_id server tr' in
    let ((), tr_state_set) = set_state server sid' (ServerReceiveRequest {id=req_msg.id; client=req_msg.client; payload=req_msg.payload; key=req_msg.key} <: communication_states) tr' in
    assert(state_was_set tr_state_set server sid' (ServerReceiveRequest {id; client; payload; key} <: communication_states));

    normalize_term_spec (DY.Core.Trace.Manipulation.new_session_id);
admit();
    normalize_term_spec (DY.Lib.State.Typed.set_state #communication_states #local_state_communication_layer_session);
    normalize_term_spec (DY.Lib.State.Tagged.set_tagged_state);
    normalize_term_spec (DY.Core.Trace.Manipulation.set_state);

    normalize_term_spec (DY.Lib.State.Typed.get_state #communication_states #local_state_communication_layer_session);
    normalize_term_spec (DY.Lib.State.Tagged.get_tagged_state);
    normalize_term_spec (DY.Core.Trace.Manipulation.get_state);
    assert(
      match get_state #communication_states #local_state_communication_layer_session server sid' tr_state_set with
      | (None, _) -> True
      | (Some state, tr') -> (
        match state with
        | ServerReceiveRequest {id=id'; client=client'; payload=payload'; key=key'} -> (
          req_msg.payload == payload'
        )
        | _ -> True
      )
    );
    
    assert(tr' == tr_out);
    assert(trace_invariant tr_out);

    assert(bytes_invariant tr_out payload);
    assert(bytes_well_formed tr_out payload);
    assert(get_label tr_out payload `can_flow tr_out` get_label #default_crypto_usages tr_out key);
    
    ()
    (*
    //normalize_term_spec (set_state #communication_states #local_state_communication_layer_session);
    //normalize_term_spec (get_state #communication_states #local_state_communication_layer_session);
    get_state_same_trace #communication_states #local_state_communication_layer_session server sid tr_out;

    assert(
      match get_state server sid tr_out with
      | (None, _) -> True
      | (Some state, tr) -> (
        match state with
        | ServerReceiveRequest {id; client; payload=payload'; key=key'} -> (
          bytes_invariant tr payload' /\
          payload' == payload /\
          get_label tr payload `can_flow tr` get_label #default_crypto_usages tr key /\
          bytes_well_formed tr payload'
        )
        | _ -> True
      )
    );
    admit();
    
    //assert(is_comm_response_payload tr_out server sid payload);
    
    match get_state server sid tr_out with
    | (None, tr') -> assert(tr' == tr_out); admit()
    | (Some state, tr_out) -> (
      match state with
      | ServerReceiveRequest {id=id'; client=client'; payload=payload'; key=key'} -> (
        assert(payload == payload');
        assert(FStar.Ghost.reveal id == id');
        assert(FStar.Ghost.reveal client == client');
        assert(FStar.Ghost.reveal key == key');
        
        assert(
          bytes_invariant tr_out payload /\
          get_label tr_out payload `can_flow tr` get_label #default_crypto_usages tr_out key /\
          bytes_well_formed tr_out payload
        );
        assert(is_comm_response_payload tr_out server sid payload);
        ()
      )
      | _ -> ()
    )
    *)
  )
#pop-options


val compute_response_message_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  client:principal -> server:principal ->
  key:bytes -> nonce:bytes -> id:bytes -> payload:bytes ->
  Lemma
  (requires
    has_communication_layer_reqres_crypto_predicates /\
    is_knowable_by (comm_label client server) tr key /\
    is_knowable_by (get_label tr key) tr id /\
    is_knowable_by (get_label tr key) tr payload /\    
    is_publishable tr nonce /\
    (key `has_usage tr` (AeadKey comm_layer_aead_tag empty) \/
      is_publishable tr key    
    ) /\
    event_triggered tr server (CommServerSendResponse client server id payload)
  )
  (ensures
    is_publishable tr (compute_response_message client server key nonce id payload)
  )
let compute_response_message_proof #cinvs tr client server key nonce id payload =
  let res:response_message = {id; payload} in
  let res_bytes = serialize response_message res in
  serialize_wf_lemma response_message (is_knowable_by (get_label tr key) tr) res;
  assert(bytes_invariant tr res_bytes);
  let ad:authenticated_data = {client; server} in
  let ad_bytes = serialize authenticated_data ad in
  serialize_wf_lemma authenticated_data (is_publishable tr) ad;
  let ciphertext = aead_enc key nonce res_bytes ad_bytes in  
  // Needed for the case that the key is publishable
  FStar.Classical.move_requires (aead_enc_preserves_publishability tr key nonce res_bytes) ad_bytes;
  assert(bytes_invariant tr ciphertext);
  serialize_wf_lemma response_envelope (is_publishable tr) {nonce; ciphertext};
  ()

// TODO should this go into the core?
val state_was_set_grows:
  #a:Type -> {|ev:local_state a|} ->
  tr1:trace -> tr2:trace ->
  prin:principal -> sid:state_id -> e:a  ->
  Lemma
  (requires state_was_set tr1 prin sid e /\ tr1 <$ tr2)
  (ensures state_was_set tr2 prin sid e)
  [SMTPat (state_was_set tr1 prin sid e); SMTPat (tr1 <$ tr2)]
let state_was_set_grows #a #ev tr1 tr2 prin sid e =
  reveal_opaque (`%state_was_set) (state_was_set #a);
  reveal_opaque (`%DY.Lib.State.Tagged.tagged_state_was_set) (DY.Lib.State.Tagged.tagged_state_was_set);
  ()



(*
val is_comm_response_payload_later:
  {|crypto_invariants|} ->
  tr1:trace -> tr2:trace ->
  server:principal -> sid:state_id -> payload:bytes ->
  Lemma
  (requires
    is_comm_response_payload tr1 server sid payload /\
    tr1 <$ tr2
  )
  (ensures
    is_comm_response_payload tr2 server sid payload
  )
let is_comm_response_payload_later #cusg tr1 tr2 server sid payload =
  match get_state server sid tr1 with
  | (None, _) -> ()
  | (Some state, tr') -> (
    state_was_set_grows #communication_states #local_state_communication_layer_session tr1 tr2 server sid state;
    assert(state_was_set tr2 server sid state);
    admit()
  )
*)

#push-options "--fuel 1 --ifuel 0"
val mk_comm_layer_response_nonce_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  server:principal -> sid:state_id -> usg:usage ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_state_predicates /\
    has_communication_layer_reqres_crypto_predicates
  )
  (ensures (
    match mk_comm_layer_response_nonce server sid usg tr with
    | (None, tr_out) -> trace_invariant tr_out
    | (Some nonce, tr_out) -> (
      is_comm_response_payload tr_out server sid nonce
    )
  ))
let mk_comm_layer_response_nonce_proof #invs tr server sid usg =
  match mk_comm_layer_response_nonce server sid usg tr with
  | (None, tr_out) -> ()
  | (Some nonce, tr_out) -> (
    let (Some state, tr') = get_state server sid tr in
    assert(trace_invariant tr');
    let ServerReceiveRequest srr = state in
    let (nonce', tr') = mk_rand usg (get_label tr' srr.key) 32 tr' in
    assert(tr_out == tr');
    assert(get_label tr_out nonce' `can_flow tr_out` get_label #default_crypto_usages tr_out srr.key);
    assert(bytes_invariant tr_out nonce');
    assert(bytes_well_formed tr_out nonce');
    normalize_term_spec mk_rand;
    normalize_term_spec (get_state #communication_states #local_state_communication_layer_session);
    assert(is_comm_response_payload tr_out server sid nonce');
    ()
  )
#pop-options

val send_response_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  comm_keys_ids:communication_keys_sess_ids ->
  higher_layer_preds:comm_reqres_higher_layer_event_preds ->
  server:principal -> sid:state_id -> payload:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_crypto_predicates /\
    has_communication_layer_reqres_event_predicates request_response_event_preconditions higher_layer_preds /\
    higher_layer_preds.send_response tr server payload /\
    has_communication_layer_state_predicates /\
    is_comm_response_payload tr server sid payload
    (*
      match get_state server sid tr with
      | (Some (ServerReceiveRequest {id; client; payload=payload'; key}), tr_out) -> (
        is_knowable_by (get_label tr key) tr payload
      )
      | _ -> False
    *)
  )
  (ensures (
    let (_, tr_out) = send_response comm_keys_ids server sid payload tr in
    trace_invariant tr_out
  ))
let send_response_proof #invs tr comm_keys_ids higher_layer_preds server sid payload =
  match send_response comm_keys_ids server sid payload tr with
  | (None, tr_out) -> ()
  | (Some msg_id, tr_out) -> (
    let (Some state, tr') = get_state server sid tr in
    assert(trace_invariant tr');
    let ServerReceiveRequest srr = state in
    
    
    assert(higher_layer_preds.send_response tr server payload);
    higher_layer_preds.send_response_later tr tr' server payload;
    assert(higher_layer_preds.send_response tr' server payload);

    //mk_comm_layer_response_nonce_proof tr' server sid payload_usg;
    assert(tr' == tr);
    assert(is_comm_response_payload tr' server sid payload);
    assert(get_label tr' payload `can_flow tr'` get_label #default_crypto_usages tr' srr.key);
    assert(bytes_invariant tr' payload);
    assert(is_knowable_by (get_label #default_crypto_usages tr' srr.key) tr' payload);

    let ((), tr') = trigger_event server (CommServerSendResponse srr.client server srr.id payload) tr' in
    assert(trace_invariant tr');
    (*assert(
      exists client id key.
      state_was_set tr' server sid (ServerReceiveRequest {id; client; payload; key}) /\
      is_knowable_by (get_label tr' key) tr' payload /\
      is_knowable_by (get_label tr' key) tr' id /\
      srr.client == client
    );*)
    
    let (nonce, tr') = mk_rand NoUsage public 32 tr' in
    compute_response_message_proof tr' srr.client server srr.key nonce srr.id payload;
    let resp_msg_bytes = compute_response_message srr.client server srr.key nonce srr.id payload in
    let (msg_id, tr') = send_msg resp_msg_bytes tr' in
    assert(tr_out == tr');
    assert(trace_invariant tr_out);
    ()
  )


#push-options "--fuel 2 --ifuel 4 --z3rlimit 50"
val decode_response_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  client:principal -> server:principal ->
  key:bytes -> id:bytes -> msg_bytes:bytes ->
  Lemma
  (requires
    has_communication_layer_reqres_crypto_predicates /\
    is_publishable tr msg_bytes /\
    is_secret (comm_label client server) tr key /\
    key `has_usage tr` (AeadKey comm_layer_aead_tag empty)
  )
  (ensures (
    match decode_response_message client server key id msg_bytes with
    | None -> True
    | Some payload -> (
      is_knowable_by (get_label tr key) tr payload /\
      (event_triggered tr server (CommServerSendResponse client server id payload)
        \/ is_publishable tr key)
    )
  ))
let decode_response_proof #cinvs tr client server key id msg_bytes =
  match decode_response_message client server key id msg_bytes with
  | None -> ()
  | Some payload -> (
    parse_wf_lemma response_envelope (is_publishable tr) msg_bytes;
    let Some {nonce; ciphertext} = parse response_envelope msg_bytes in
    assert(is_publishable tr nonce);
    assert(is_publishable tr ciphertext);
    serialize_wf_lemma authenticated_data (is_publishable tr) {client; server};
    let ad_bytes = serialize authenticated_data {client; server} in
    assert(is_publishable tr ad_bytes);
    let Some res_bytes = aead_dec key nonce ciphertext ad_bytes in
    assert(bytes_invariant tr res_bytes);
    assert(is_knowable_by (comm_label client server) tr res_bytes);
    parse_wf_lemma response_message (is_knowable_by (comm_label client server) tr) res_bytes;
    ()
  )
#pop-options
