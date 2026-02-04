module DY.Lib.Communication.RequestResponse.Lemmas

open Comparse
open DY.Core
open DY.Lib.Crypto.PKE.Split
open DY.Lib.Crypto.Signature.Split
open DY.Lib.State.PKI
open DY.Lib.State.PrivateKeys
open DY.Lib.Event.Typed
open DY.Lib.State.Typed
open DY.Lib.Comparse.Parsers

open DY.Lib.Communication.Data
open DY.Lib.Communication.Core
open DY.Lib.Communication.Core.Invariants
open DY.Lib.Communication.Core.Lemmas
open DY.Lib.Communication.Core.Properties
open DY.Lib.Communication.RequestResponse
open DY.Lib.Communication.RequestResponse.Invariants

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Lemmas ***)

val get_response_label_eq_key_label:
  {|cinvs:crypto_invariants|} ->
  #a:Type0 -> {|conf:comm_layer_reqres_config a|} -> tr:trace ->
  req_meta_data:comm_meta_data a ->
  Lemma
  (requires
    cinvs.usages == default_crypto_usages /\
    bytes_well_formed tr req_meta_data.key
  )
  (ensures
    get_response_label tr req_meta_data == get_label tr (req_meta_data.key)
  )
  //[SMTPat (get_response_label tr #a #conf req_meta_data)]
let get_response_label_eq_key_label #cinvs #a #_ tr req_meta_data =
  reveal_opaque (`%get_response_label) (get_response_label)

val get_response_label_later:
  #a:Type0 -> {|comm_layer_reqres_config a|} -> 
  tr1:trace -> tr2:trace ->
  req_meta_data:comm_meta_data a ->
  Lemma
  (requires
    tr1 <$ tr2 /\
    bytes_well_formed tr1 req_meta_data.key
  )
  (ensures
    get_response_label tr1 req_meta_data == get_response_label tr2 req_meta_data
  )
  [SMTPat (get_response_label tr1 req_meta_data); SMTPat (tr1 <$ tr2)]
let get_response_label_later #a tr1 tr2 req_meta_data =
  reveal_opaque (`%get_response_label) get_response_label;
  get_label_later #default_crypto_usages tr1 tr2 req_meta_data.key;
  ()

val is_comm_response_payload:
  {|crypto_invariants|} ->
  #a:Type0 -> {|comm_layer_reqres_config a|} ->
  trace -> principal -> comm_meta_data a -> a -> prop
let is_comm_response_payload #cusg #a #ps tr server req_meta_data payload =
  is_well_formed a (is_knowable_by (get_response_label tr req_meta_data) tr) payload

val comm_meta_data_knowable: 
  {|crypto_invariants|} ->
  trace ->
  a:Type -> {|comm_layer_reqres_config a|} ->
  principal -> comm_meta_data a ->
  prop
let comm_meta_data_knowable #cinvs tr a #ps prin req_meta_data =
  is_knowable_by (principal_label prin) tr req_meta_data.key /\
  is_well_formed a (is_knowable_by (principal_label prin) tr) req_meta_data.request


instance parseable_serializeable_bytes_state_id: parseable_serializeable bytes state_id
  = mk_parseable_serializeable ps_state_id

instance parseable_serializeable_bytes_principal: parseable_serializeable bytes principal
  = mk_parseable_serializeable ps_principal

val comm_meta_data_knowable_proof: 
  {|crypto_invariants|} ->
  tr:trace ->
  a:Type -> {|comm_layer_reqres_config a|} ->
  st_t:Type0 -> {|ps:parseable_serializeable bytes st_t|} ->
  sess_id:state_id -> st:st_t -> {|local_state st_t|} ->
  prin:principal -> req_meta_data:comm_meta_data a ->
  Lemma
  (requires
    comm_meta_data_knowable tr a prin req_meta_data
  )
  (ensures
    is_well_formed (comm_meta_data a) (is_knowable_by (principal_typed_state_content_label prin (DY.Lib.State.Typed.tag #st_t) sess_id st) tr) req_meta_data
  )
let comm_meta_data_knowable_proof #cinvs tr a #ps st_t #ps_st_t sess_id st #local_state_st prin req_meta_data = 
  let lab = principal_typed_state_content_label prin (DY.Lib.State.Typed.tag #st_t) sess_id st in
  assert(
    is_knowable_by lab tr req_meta_data.key /\
    is_well_formed a (is_knowable_by lab tr) req_meta_data.request
  );
  assert(is_well_formed state_id (is_knowable_by lab tr) req_meta_data.sid);
  assert(is_well_formed principal (is_knowable_by lab tr) req_meta_data.server);
  ()

val comm_client_state_invariant: 
  {|crypto_invariants|} ->
  trace ->
  a:Type -> {|comm_layer_reqres_config a|} ->
  principal -> comm_meta_data a ->
  prop
let comm_client_state_invariant #cinvs tr a #ps prin req_meta_data =
  comm_meta_data_knowable tr a prin req_meta_data /\
  event_triggered tr prin (CommClientSendRequest prin req_meta_data.server req_meta_data.request req_meta_data.key <: communication_reqres_event a)

/// The communication layer makes use of many lemmas with SMT patterns.
/// These lemmas depend, however, on the communication layer predicates
/// in use for the current analysis.
/// To enable these lemmas for an analysis, which requires specifying which
/// predicates they shouild be used for, one can use the line
/// `enable_reqres_comm_layer_lemmas preds`, where `preds` is the relevant
/// `comm_reqres_higher_layer_event_preds` for the protocol.
/// See https://github.com/FStarLang/FStar/wiki/Quantifiers-and-patterns
/// for more information on this technique.

[@@"opaque_to_smt"]
val reqres_comm_layer_lemmas_enabled:
  a:Type0 -> {| comm_layer_reqres_config a |} ->
  {|comm_reqres_preds a|} -> prop
let reqres_comm_layer_lemmas_enabled a #config #crpreds = True

val enable_reqres_comm_layer_lemmas:
  a:Type0 -> {|comm_layer_reqres_config a|} ->
  {|comm_reqres_preds a|} ->
  Lemma (reqres_comm_layer_lemmas_enabled a)
let enable_reqres_comm_layer_lemmas a #config #crpreds =
  normalize_term_spec (reqres_comm_layer_lemmas_enabled a)


#push-options "--ifuel 2"
val initialize_communication_reqres_proof:
  {|invs:protocol_invariants|} ->
  tr:trace ->
  a:Type -> {|comm_layer_reqres_config a|} ->
  sender:principal -> receiver:principal ->
  Lemma
  (requires
    trace_invariant tr /\
    has_private_keys_invariant /\
    has_private_keys_state_update_invariant /\
    has_pki_invariant /\
    has_pki_state_update_invariant
  )
  (ensures (
    let (_, tr_out) = initialize_communication_reqres a sender receiver tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant #invs tr);
   SMTPat (initialize_communication_reqres a sender receiver tr);
  ]
let initialize_communication_reqres_proof tr a sender receiver =
  reveal_opaque (`%initialize_communication_reqres) (initialize_communication_reqres a sender receiver)
#pop-options


#push-options "--z3rlimit 250"
val send_request_proof:
  {|protocol_invariants|} ->
  #a:Type0 -> {|comm_layer_reqres_config a|} ->
  {|crpreds:comm_reqres_preds a|} ->
  tr:trace ->
  comm_keys_ids:communication_keys_sess_ids ->
  client:principal -> server:principal -> request:a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_pki_invariant /\
    has_pki_state_update_invariant /\
    has_communication_layer_reqres_predicates a /\
    crpreds.send_request_pred tr client server request (comm_label client server) /\
    is_well_formed a (is_knowable_by (comm_label client server) tr) request
  )
  (ensures (
    match send_request comm_keys_ids client server request tr with
    | (None, tr_out) -> trace_invariant tr_out
    | (Some (_, req_meta_data), tr_out) -> (
      trace_invariant tr_out /\
      event_triggered tr_out client (CommClientSendRequest client server request req_meta_data.key <: communication_reqres_event a) /\
      request == req_meta_data.request /\
      server == req_meta_data.server
    )
  ))
  [SMTPat (trace_invariant tr);
  SMTPat (reqres_comm_layer_lemmas_enabled a);
  SMTPat (send_request comm_keys_ids client server request tr)]
let send_request_proof #invs #a #config #crpreds tr comm_keys_ids  client server request =
  reveal_opaque (`%send_request) (send_request #a);
  enable_core_comm_layer_lemmas (comm_core_higher_layer_event_preds_reqres a);
  let request_bytes = serialize a request in
  match send_request comm_keys_ids client server request tr with
  | (None, tr_out) -> (
    let (key, tr') = mk_rand (AeadKey (comm_layer_aead_tag a) empty) (comm_label client server) 32 tr in
    crpreds.send_request_pred_later tr tr' client server request (get_label tr' key);
    let ((), tr') = trigger_event client (CommClientSendRequest client server request key <: communication_reqres_event a) tr' in
    let (sid, tr') = new_session_id client tr' in
    let ((), tr') = set_state client sid (ClientSendRequest {server; request=request; key} <: communication_states a) tr' in
    assert(trace_invariant tr');
    ()
  )
  | (Some (_, req_meta_data), tr_out) -> (
    let (key, tr') = mk_rand (AeadKey (comm_layer_aead_tag a) empty) (comm_label client server) 32 tr in
    crpreds.send_request_pred_later tr tr' client server request (get_label tr' key);
    let ((), tr') = trigger_event client (CommClientSendRequest client server request key <: communication_reqres_event a) tr' in
    let (sid, tr') = new_session_id client tr' in
    let ((), tr') = set_state client sid (ClientSendRequest {server; request; key} <: communication_states a) tr' in
    assert(trace_invariant tr');
    let req_payload:comm_message_t = RequestMessage {request=request_bytes; key} in
    let (Some msg_id, tr') = send_confidential #comm_message_t #(comm_layer_tag_core_config_reqres a) comm_keys_ids client server req_payload tr' in
    assert(tr_out == tr');
    assert(trace_invariant tr_out); 
    ()
  )
#pop-options

val send_request_parameter_equality:
  #a:eqtype -> {|comm_layer_reqres_config a|} ->
  tr:trace ->
  com_keys_ids:communication_keys_sess_ids ->
  client:principal -> server:principal -> request:a ->
  Lemma
  (ensures (
    match send_request com_keys_ids client server request tr with
    | (None, _) -> True
    | (Some (_, cmeta_data), _) -> (
      server == cmeta_data.server /\
      request == cmeta_data.request
    )
  ))
let send_request_parameter_equality #a #config tr com_keys_ids client server request =
  reveal_opaque (`%send_request) (send_request #a);
  ()


#push-options "--z3rlimit 1000"
val receive_request_proof:
  {|invs:protocol_invariants|} ->
  a:Type -> {|comm_layer_reqres_config a|} ->
  {|crpreds:comm_reqres_preds a|} ->
  tr:trace ->
  comm_keys_ids:communication_keys_sess_ids ->
  server:principal -> msg_id:timestamp ->
  Lemma
  (requires
    invs.crypto_invs.usages == default_crypto_usages /\
    trace_invariant tr /\
    has_private_keys_invariant /\
    has_pki_invariant /\
    has_communication_layer_reqres_predicates a
  )
  (ensures (
    match receive_request #a comm_keys_ids server msg_id tr with
    | (None, tr_out) -> trace_invariant tr_out
    | (Some (payload, req_meta_data), tr_out) -> (
      trace_invariant tr_out /\
      event_triggered tr_out server (CommServerReceiveRequest server payload req_meta_data.key <: communication_reqres_event a) /\
      payload == req_meta_data.request /\
      server == req_meta_data.server
    )
  ))
  [SMTPat (trace_invariant tr);
  SMTPat (reqres_comm_layer_lemmas_enabled a);
  SMTPat (receive_request #a comm_keys_ids server msg_id tr)]
let receive_request_proof #invs a #config #crpreds tr comm_keys_ids server msg_id =
  reveal_opaque (`%receive_request) (receive_request #a);
  enable_core_comm_layer_lemmas (comm_core_higher_layer_event_preds_reqres a);
  match receive_request #a comm_keys_ids server msg_id tr with
  | (None, tr_out) -> ()
  | (Some (payload, req_meta_data), tr_out) -> (
    receive_confidential_proof #invs #comm_message_t #(comm_layer_tag_core_config_reqres a) tr (comm_core_higher_layer_event_preds_reqres a) comm_keys_ids server msg_id;
    let (Some req_msg_t, tr_recv) = receive_confidential #comm_message_t #(comm_layer_tag_core_config_reqres a) comm_keys_ids server msg_id tr in
    let RequestMessage req_msg = req_msg_t in
    let Some request = parse a req_msg.request in

    let req_msg_bytes:bytes = serialize comm_message_t req_msg_t in
    let req_send_event client:communication_reqres_event a = CommClientSendRequest client server request req_msg.key in

    conf_message_properties tr_recv (comm_core_higher_layer_event_preds_reqres a) server req_msg_t;
    
    // Properties that can be proved uniformly in both the honest and corrupt case
    eliminate (exists client. event_triggered tr_recv client (req_send_event client)) \/
              (is_publishable tr_recv req_msg.request /\ is_publishable tr_recv req_msg.key)
    returns (
      is_well_formed a (is_knowable_by (get_response_label tr_recv req_meta_data) tr_recv) request /\
      req_msg.key `has_usage tr_recv` (AeadKey (comm_layer_aead_tag a) empty)
    )
    with _. eliminate exists client. event_triggered tr_recv client (req_send_event client)
      returns _
      with _. (
        get_response_label_eq_key_label tr_recv req_meta_data;

        let i = find_event_triggered_at_timestamp tr_recv client (req_send_event client) in
        assert(event_predicate_communication_layer_reqres a (prefix tr_recv i) client (req_send_event client));
        ()
      )
    and _. (has_usage_publishable tr_recv req_msg.key (AeadKey (comm_layer_aead_tag a) empty);
      parse_wf_lemma a (is_publishable tr_recv) req_msg.request;
      ()
    );

    // Relating knowledge of the request to knowledge of its fields
    serialize_parse_inv_lemma #bytes a req_msg.request;
    assert(is_comm_response_payload tr_recv server req_meta_data payload);

    let ((), tr_ev) = trigger_event server (CommServerReceiveRequest server request req_msg.key <: communication_reqres_event a) tr_recv in
    let (sid', tr_sess) = new_session_id server tr_ev in

    // Needed for the proof to go through
    assert((state_predicate_communication_layer_reqres a).pred tr_sess server sid' (ServerReceiveRequest {request; key=req_msg.key} <: communication_states a));
    let ((), tr_st) = set_state server sid' (ServerReceiveRequest {request; key=req_msg.key} <: communication_states a) tr_sess in

    get_response_label_eq_key_label tr_recv req_meta_data;
    
    assert(tr_out == tr_st);
    assert(trace_invariant tr_out);
    ()
  )
#pop-options


val mk_comm_layer_response_nonce_proof:
  {|protocol_invariants|} ->
  #a:Type -> {|comm_layer_reqres_config a|} ->
  tr:trace ->
  req_meta_data:comm_meta_data a -> usg:usage ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_state_predicate a /\
    has_communication_layer_reqres_crypto_predicates a /\
    bytes_well_formed tr req_meta_data.key // Can be derived from CommServerReceiveRequest event
  )
  (ensures (
    match mk_comm_layer_response_nonce req_meta_data usg tr with
    | (None, tr_out) -> trace_invariant tr_out
    | (Some nonce, tr_out) -> (
      trace_invariant tr_out /\
      is_secret (get_response_label tr_out req_meta_data) tr_out nonce /\
      is_knowable_by (get_response_label tr_out req_meta_data) tr_out nonce
    )
  ))
[SMTPat (trace_invariant tr);
  SMTPat (mk_comm_layer_response_nonce req_meta_data usg tr)]
let mk_comm_layer_response_nonce_proof #invs #a tr req_meta_data usg =
  reveal_opaque (`%mk_comm_layer_response_nonce) (mk_comm_layer_response_nonce #a);
  reveal_opaque (`%get_response_label) (get_response_label);
  ()

val mk_comm_layer_response_nonce_labeled_proof:
  {|protocol_invariants|} ->
  #a:Type -> {|comm_layer_reqres_config a|} ->
  tr:trace ->
  req_meta_data:comm_meta_data a -> usg:usage -> lab:label ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_state_predicate a /\
    has_communication_layer_reqres_crypto_predicates a /\
    bytes_well_formed tr req_meta_data.key // Can be derived from CommServerReceiveRequest event
  )
  (ensures (
    match mk_comm_layer_response_nonce_labeled req_meta_data usg lab tr with
    | (None, tr_out) -> trace_invariant tr_out
    | (Some nonce, tr_out) -> (
      trace_invariant tr_out /\
      is_secret (join (get_response_label tr_out req_meta_data) lab) tr_out nonce /\
      is_knowable_by (join (get_response_label tr_out req_meta_data) lab) tr_out nonce
    )
  ))
  [SMTPat (trace_invariant tr);
  SMTPat (mk_comm_layer_response_nonce_labeled req_meta_data usg lab tr)]
let mk_comm_layer_response_nonce_labeled_proof #invs #a tr req_meta_data usg lab =
  reveal_opaque (`%mk_comm_layer_response_nonce_labeled) (mk_comm_layer_response_nonce_labeled #a);
  reveal_opaque (`%get_response_label) (get_response_label);
  ()


val compute_response_message_proof:
  {|crypto_invariants|} ->
  #a:Type0 -> {|comm_layer_reqres_config a|} ->
  tr:trace ->
  server:principal ->
  req_meta_data:comm_meta_data a -> nonce:bytes -> request:a -> response:a ->
  Lemma
  (requires
    has_communication_layer_reqres_crypto_predicates a /\
    is_knowable_by (principal_label server) tr req_meta_data.key /\
    is_well_formed a (is_knowable_by (get_response_label tr req_meta_data) tr) response /\
    is_publishable tr nonce /\
    req_meta_data.key `has_usage tr` (AeadKey (comm_layer_aead_tag a) empty) /\
    event_triggered tr server (CommServerSendResponse server request response req_meta_data.key <: communication_reqres_event a)
  )
  (ensures
    is_publishable tr (compute_response_message #a server req_meta_data nonce response)
  )
let compute_response_message_proof #cinvs #a tr server req_meta_data nonce request response =
  reveal_opaque (`%compute_response_message) (compute_response_message #a);
  get_response_label_eq_key_label tr req_meta_data;
  let res_bytes = serialize a response in
  serialize_wf_lemma a (is_knowable_by (get_response_label tr req_meta_data) tr) response;
  let ad:authenticated_data = {server} in
  let ad_bytes = serialize authenticated_data ad in
  serialize_wf_lemma authenticated_data (is_publishable tr) ad;
  let ciphertext = aead_enc req_meta_data.key nonce res_bytes ad_bytes in
  // Needed for the case that the key is publishable
  FStar.Classical.move_requires (aead_enc_preserves_publishability tr req_meta_data.key nonce res_bytes) ad_bytes;
  serialize_wf_lemma comm_message_t (is_publishable tr) (ResponseMessage {nonce; ciphertext});
  ()

#push-options "--z3rlimit 10"
val send_response_proof:
  {|protocol_invariants|} ->
  #a:eqtype -> {|comm_layer_reqres_config a|} ->
  {|crpreds:comm_reqres_preds a|} ->
  tr:trace ->
  server:principal -> req_meta_data:comm_meta_data a -> response:a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_predicates a /\
    event_triggered tr server (CommServerReceiveRequest server req_meta_data.request req_meta_data.key <: communication_reqres_event a) /\
    crpreds.send_response_pred tr server req_meta_data.request response (get_response_label tr req_meta_data) /\
    is_well_formed a (is_knowable_by (get_response_label tr req_meta_data) tr) response
  )
  (ensures (
    let (_, tr_out) = send_response server req_meta_data response tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant tr);
  SMTPat (reqres_comm_layer_lemmas_enabled a);
  SMTPat (send_response server req_meta_data response tr)]
let send_response_proof #invs #a #config #crpreds tr server req_meta_data response =
  reveal_opaque (`%send_response) (send_response #a);
  match send_response server req_meta_data response tr with
  | (None, tr_out) -> ()
  | (Some msg_id, tr_out) -> (
    let (Some state, tr_st):(option (communication_states a) & trace) = get_state server req_meta_data.sid tr in
    let ServerReceiveRequest srr = state in
    assert(trace_invariant tr_st);
    let ((), tr_ev) = trigger_event server (CommServerSendResponse server req_meta_data.request response req_meta_data.key <: communication_reqres_event a) tr_st in
    get_response_label_eq_key_label tr_ev req_meta_data;
    assert(trace_invariant tr_ev);
    let (nonce, tr_nonce) = mk_rand NoUsage public 32 tr_ev in
    assert(trace_invariant tr_nonce);
    compute_response_message_proof tr_nonce server req_meta_data nonce req_meta_data.request response;
    let resp_msg_bytes = compute_response_message server req_meta_data nonce response in
    let (msg_id, tr_snd) = send_msg resp_msg_bytes tr_nonce in
    assert(tr_out == tr_snd);
    assert(trace_invariant tr_out); 
    ()
  )
#pop-options


#push-options "--z3rlimit 50"
val decode_response_proof:
  {|crypto_invariants|} ->
  #a:Type -> {|comm_layer_reqres_config a|} ->
  tr:trace ->
  client:principal -> server:principal ->
  response_bytes:bytes -> key:bytes ->
  Lemma
  (requires
    has_communication_layer_reqres_crypto_predicates a /\
    is_publishable tr response_bytes /\
    is_secret (comm_label client server) tr key /\
    key `has_usage tr` (AeadKey (comm_layer_aead_tag a) empty)
  )
  (ensures (
    match decode_response_message server key response_bytes with
    | None -> True
    | Some response -> (
      is_well_formed a (is_knowable_by (get_label tr key) tr) response /\
      is_knowable_by (get_label tr key) tr (serialize a response) /\
      ((exists request. event_triggered tr server (CommServerSendResponse server request response key <: communication_reqres_event a))
        \/ is_corrupt tr (principal_label client) \/ is_corrupt tr (principal_label server))
    )
  ))
let decode_response_proof #invs #a tr client server response_bytes key =
  reveal_opaque (`%decode_response_message) (decode_response_message #a);
  match decode_response_message #a server key response_bytes with
  | None -> ()
  | Some response -> (
    parse_wf_lemma comm_message_t (is_publishable tr) response_bytes;
    let Some (ResponseMessage {nonce; ciphertext}) = parse comm_message_t response_bytes in
    serialize_wf_lemma authenticated_data (is_publishable tr) {server};
    let ad_bytes = serialize authenticated_data {server} in
    let Some res_bytes = aead_dec key nonce ciphertext ad_bytes in
    serialize_parse_inv_lemma a res_bytes;
    ()
  )
#pop-options

#push-options "--z3rlimit 10"
val comm_client_send_request_injective:
  {|protocol_invariants|} ->
  #a:Type -> {| comm_layer_reqres_config a |} ->
  {|crpreds:comm_reqres_preds a|} ->
  tr:trace ->
  client:principal -> client':principal -> server:principal ->
  request:a -> request':a -> key:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_predicates a /\
    event_triggered tr client' (CommClientSendRequest client' server request' key <: communication_reqres_event a) /\
    event_triggered tr client (CommClientSendRequest client server request key <: communication_reqres_event a)
  )
  (ensures
    client == client' /\
    request == request'
  )
let comm_client_send_request_injective #invs #a #config #crpreds tr client client' server request request' key = ()
#pop-options

#push-options "--z3rlimit 100"
val request_response_property:
  {|protocol_invariants|} ->
  #a:Type -> {|comm_layer_reqres_config a|} ->
  {|comm_reqres_preds a|} ->
  tr:trace ->
  client:principal -> server:principal ->
  request:a -> response:a -> key:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_predicates a /\
    event_triggered tr client (CommClientSendRequest client server request key <: communication_reqres_event a) /\
    is_secret (comm_label client server) tr key /\
    key `has_usage tr` (AeadKey (comm_layer_aead_tag a) empty) /\
    (exists request'. event_triggered tr server (CommServerSendResponse server request' response key <: communication_reqres_event a)
        \/ is_corrupt tr (principal_label client) \/ is_corrupt tr (principal_label server))
  )
  (ensures
    (
      event_triggered tr server (CommServerSendResponse server request response key <: communication_reqres_event a) /\
      event_triggered tr server (CommServerReceiveRequest server request key <: communication_reqres_event a)
    ) \/ is_corrupt tr (principal_label client) \/ is_corrupt tr (principal_label server)
  )
let request_response_property #invs #a #config #crpreds tr client server request response key =
  let send_event request:communication_reqres_event a = CommServerSendResponse server request response key in
  introduce (~(is_corrupt tr (principal_label client) \/ is_corrupt tr (principal_label server))) ==> (exists request'. event_triggered #(communication_reqres_event a) #(event_communication_reqres_event #a #config) tr server (CommServerSendResponse server request' response key <: communication_reqres_event a)) 
  with _. (
    eliminate exists request'. event_triggered tr server (CommServerSendResponse server request' response key <: communication_reqres_event a)
    returns event_triggered tr server (CommServerSendResponse server request response key <: communication_reqres_event a) /\
            event_triggered tr server (CommServerReceiveRequest server request key <: communication_reqres_event a)
    with _. (
      let j = find_event_triggered_at_timestamp tr server (send_event request') in
      assert((event_predicate_communication_layer_reqres a) (prefix tr j) server (send_event request'));
      assert((exists client'. 
        event_triggered tr client' (CommClientSendRequest client' server request' key <: communication_reqres_event a)));
      eliminate exists client'. event_triggered tr client' (CommClientSendRequest client' server request' key <: communication_reqres_event a)
      returns event_triggered tr server (CommServerSendResponse server request response key <: communication_reqres_event a) /\
              event_triggered tr server (CommServerReceiveRequest server request key <: communication_reqres_event a)
      with _. (
        comm_client_send_request_injective tr client client' server request request' key;
        ()
      )
    )
  )
#pop-options

#push-options "--z3rlimit 150"
val receive_response_proof:
  {|protocol_invariants|} ->
  #a:Type -> {|comm_layer_reqres_config a|} ->
  {|crpreds:comm_reqres_preds a|} ->
  tr:trace ->
  client:principal -> req_meta_data:comm_meta_data a -> msg_id:timestamp ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_predicates a /\
    event_triggered tr client (CommClientSendRequest client req_meta_data.server req_meta_data.request req_meta_data.key <: communication_reqres_event a)
  )
  (ensures (
    match receive_response client req_meta_data msg_id tr with
    | (None, tr_out) -> trace_invariant tr_out
    | (Some (payload, _), tr_out) -> (
      trace_invariant tr_out /\
      event_triggered tr_out client (CommClientReceiveResponse client req_meta_data.server req_meta_data.request payload req_meta_data.key <: communication_reqres_event a)
    )
  ))
  [SMTPat (trace_invariant tr);
  SMTPat (reqres_comm_layer_lemmas_enabled a);
  SMTPat (receive_response client req_meta_data msg_id tr)]
let receive_response_proof #invs #a #crpreds tr client req_meta_data msg_id =
  reveal_opaque (`%receive_response) (receive_response #a);
  match receive_response #a client req_meta_data msg_id tr with
  | (None, tr_out) -> ()
  | (Some (response, _), tr_out) -> (
    let server = req_meta_data.server in
    let key = req_meta_data.key in
    let (Some state, tr'):(option (communication_states a) & trace) = get_state client req_meta_data.sid tr in
    let ClientSendRequest csr = state in
    let (Some resp_msg_bytes, tr') = recv_msg msg_id tr' in
    decode_response_proof #invs.crypto_invs #a tr' client server resp_msg_bytes key;
    let Some response = decode_response_message server key resp_msg_bytes in
    request_response_property tr' client server req_meta_data.request response key;
    get_response_label_eq_key_label tr' req_meta_data;
    let ((), tr') = set_state client req_meta_data.sid (ClientReceiveResponse {server=csr.server; response; key=csr.key} <: communication_states a) tr' in
    let ((), tr') = trigger_event client (CommClientReceiveResponse client csr.server req_meta_data.request response csr.key <: communication_reqres_event a) tr' in
    assert(event_triggered tr' client (CommClientReceiveResponse client csr.server req_meta_data.request response csr.key <: communication_reqres_event a));
    assert(tr_out == tr');
    assert(trace_invariant tr_out);
    ()
  )
#pop-options
