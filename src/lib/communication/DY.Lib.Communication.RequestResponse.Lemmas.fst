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

instance parseable_serializeable_bytes_option (a:Type0) {|ps_a:parser_serializer bytes a|}: parseable_serializeable bytes (option a)
  = mk_parseable_serializeable (ps_option ps_a)

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
  match req_meta_data.client with
  | None -> ()
  | Some client -> assert(is_well_formed principal (is_knowable_by lab tr) client);
  ()

val comm_client_state_invariant: 
  {|crypto_invariants|} ->
  trace ->
  sender_authentication ->
  a:Type -> {|comm_layer_reqres_config a|} ->
  principal -> comm_meta_data a ->
  prop
let comm_client_state_invariant #cinvs tr authenticated a #ps prin req_meta_data =
  comm_meta_data_knowable tr a prin req_meta_data /\
  event_triggered tr prin (CommClientSendRequest authenticated prin req_meta_data.server req_meta_data.request req_meta_data.key <: communication_reqres_event a)

/// The communication layer makes use of many lemmas with SMT patterns.
/// These lemmas depend, however, on the communication layer predicates
/// in use for the current analysis.
/// To enable these lemmas for an analysis, which requires specifying which
/// predicates they shouild be used for, one can use the line
/// `enable_reqres_comm_layer_lemmas preds`, where `preds` is the relevant
/// `comm_reqres_preds` for the protocol.
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


(**** Proof for Request ****)

val helper_lemma_request_knowable:
  {|protocol_invariants|} ->
  #a:Type0 -> {|comm_layer_reqres_config a|} ->
  tr:trace ->
  client:principal -> server:principal ->
  request:a -> key:bytes ->
  Lemma
  (requires
    is_well_formed a (is_knowable_by (comm_label client server) tr) request /\
    is_secret (comm_label client server) tr key
  )
  (ensures
    is_well_formed comm_message_t (is_knowable_by (comm_label client server) tr) (RequestMessage {request=(serialize a request); key})
  )
let helper_lemma_request_knowable #invs #a #config tr client server request key = ()

#push-options "--z3rlimit 50"
val send_request_unauthenticated_proof:
  {|protocol_invariants|} ->
  #a:Type0 -> {|comm_layer_reqres_config a|} ->
  {|crpreds:comm_reqres_preds a|} ->
  tr:trace ->
  comm_keys_ids:communication_keys_sess_ids ->
  client:principal -> server:principal -> request:a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_private_keys_invariant /\
    has_pki_invariant /\
    has_pki_state_update_invariant /\
    has_communication_layer_reqres_predicates a /\
    crpreds.send_request_pred tr client server request (comm_label client server) /\
    is_well_formed a (is_knowable_by (comm_label client server) tr) request
  )
  (ensures (
    match send_request Unauthenticated comm_keys_ids client server request tr with
    | (None, tr_out) -> trace_invariant tr_out
    | (Some (_, req_meta_data), tr_out) -> (
      trace_invariant tr_out /\
      event_triggered tr_out client (CommClientSendRequest Unauthenticated client server request req_meta_data.key <: communication_reqres_event a) /\
      request == req_meta_data.request /\
      server == req_meta_data.server
    )
  ))
let send_request_unauthenticated_proof #invs #a #config #crpreds tr comm_keys_ids  client server request =
  reveal_opaque (`%send_request) (send_request #a);
  let (_, tr_out) = send_request Unauthenticated comm_keys_ids client server request tr in

  let (key, tr_nc) = mk_rand (AeadKey (comm_layer_aead_tag a) empty) (comm_label client server) 32 tr in
  assert(trace_invariant tr_nc);
  crpreds.send_request_pred_later tr tr_nc client server request (get_label tr_nc key);
  let ((), tr_ev) = trigger_event client (CommClientSendRequest Unauthenticated client server request key <: communication_reqres_event a) tr_nc in
  assert(trace_invariant tr_ev);

  let (sid, tr_sess) = new_session_id client tr_ev in
  assert((state_predicate_communication_layer_reqres a).pred tr_sess client sid (ClientSendRequest {server; request; key} <: communication_states a));
  let ((), tr_st) = set_state client sid (ClientSendRequest {server; request; key} <: communication_states a) tr_sess in
  assert(trace_invariant tr_st);

  let request_bytes = serialize a request in
  let req_payload:comm_message_t = RequestMessage {request=request_bytes; key} in
  assert((comm_core_higher_layer_event_preds_reqres a).send_conf tr_st client server req_payload);
  helper_lemma_request_knowable tr_st client server request key;
  send_confidential_proof tr_st (comm_core_higher_layer_event_preds_reqres a) comm_keys_ids client server req_payload;
  let (x_snd, tr_snd) = send_confidential #comm_message_t #(comm_layer_tag_core_config_reqres a) comm_keys_ids client server req_payload tr_st in
  assert(trace_invariant tr_snd);
  
  assert(tr_out == tr_snd);
  ()
#pop-options

#push-options "--z3rlimit 75"
val send_request_authenticated_proof:
  {|protocol_invariants|} ->
  #a:Type0 -> {|comm_layer_reqres_config a|} ->
  {|crpreds:comm_reqres_preds a|} ->
  tr:trace ->
  comm_keys_ids:communication_keys_sess_ids ->
  client:principal -> server:principal -> request:a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_private_keys_invariant /\
    has_pki_invariant /\
    has_pki_state_update_invariant /\
    has_communication_layer_reqres_predicates a /\
    crpreds.send_request_pred tr client server request (comm_label client server) /\
    is_well_formed a (is_knowable_by (comm_label client server) tr) request
  )
  (ensures (
    match send_request Authenticated comm_keys_ids client server request tr with
    | (None, tr_out) -> trace_invariant tr_out
    | (Some (_, req_meta_data), tr_out) -> (
      trace_invariant tr_out /\
      event_triggered tr_out client (CommClientSendRequest Authenticated client server request req_meta_data.key <: communication_reqres_event a) /\
      request == req_meta_data.request /\
      server == req_meta_data.server
    )
  ))
let send_request_authenticated_proof #invs #a #config #crpreds tr comm_keys_ids  client server request =
  reveal_opaque (`%send_request) (send_request #a);
  let (_, tr_out) = send_request Authenticated comm_keys_ids client server request tr in

  let (key, tr_nc) = mk_rand (AeadKey (comm_layer_aead_tag a) empty) (comm_label client server) 32 tr in
  assert(trace_invariant tr_nc);
  crpreds.send_request_pred_later tr tr_nc client server request (get_label tr_nc key);
  let ((), tr_ev) = trigger_event client (CommClientSendRequest Authenticated client server request key <: communication_reqres_event a) tr_nc in
  assert(trace_invariant tr_ev);

  let request_bytes = serialize a request in
  let (sid, tr_sess) = new_session_id client tr_ev in
  let ((), tr_st) = set_state client sid (ClientSendRequest {server; request; key} <: communication_states a) tr_sess in
  assert(trace_invariant tr_st);
  
  let req_payload:comm_message_t = RequestMessage {request=request_bytes; key} in
  assert((comm_core_higher_layer_event_preds_reqres a).send_conf_auth tr_st client server req_payload);
  helper_lemma_request_knowable tr_st client server request key;
  send_confidential_authenticated_proof tr_st (comm_core_higher_layer_event_preds_reqres a) comm_keys_ids client server req_payload;
  let (x_snd, tr_snd) = send_confidential_authenticated #comm_message_t #(comm_layer_tag_core_config_reqres a) comm_keys_ids client server req_payload tr_st in
  assert(trace_invariant tr_snd);
  
  assert(tr_out == tr_snd);
  ()
#pop-options

#push-options "--ifuel 1"
val send_request_proof:
  {|protocol_invariants|} ->
  #a:Type0 -> {|comm_layer_reqres_config a|} ->
  {|crpreds:comm_reqres_preds a|} ->
  tr:trace ->
  authenticated:sender_authentication ->
  comm_keys_ids:communication_keys_sess_ids ->
  client:principal -> server:principal -> request:a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_private_keys_invariant /\
    has_pki_invariant /\
    has_pki_state_update_invariant /\
    has_communication_layer_reqres_predicates a /\
    crpreds.send_request_pred tr client server request (comm_label client server) /\
    is_well_formed a (is_knowable_by (comm_label client server) tr) request
  )
  (ensures (
    match send_request authenticated comm_keys_ids client server request tr with
    | (None, tr_out) -> trace_invariant tr_out
    | (Some (_, req_meta_data), tr_out) -> (
      trace_invariant tr_out /\
      event_triggered tr_out client (CommClientSendRequest authenticated client server request req_meta_data.key <: communication_reqres_event a) /\
      request == req_meta_data.request /\
      server == req_meta_data.server
    )
  ))
  [SMTPat (trace_invariant tr);
  SMTPat (reqres_comm_layer_lemmas_enabled a);
  SMTPat (send_request authenticated comm_keys_ids client server request tr)]
let send_request_proof #invs #a #config #crpreds tr authenticated comm_keys_ids  client server request =
  match authenticated with
  | Authenticated -> send_request_authenticated_proof tr comm_keys_ids client server request
  | Unauthenticated -> send_request_unauthenticated_proof tr comm_keys_ids client server request
#pop-options

#push-options "--z3rlimit 20"
val send_request_properties:
  #a:eqtype -> {|comm_layer_reqres_config a|} ->
  tr:trace ->
  authenticated:sender_authentication ->
  com_keys_ids:communication_keys_sess_ids ->
  client:principal -> server:principal -> request:a ->
  Lemma
  (ensures (
    match send_request authenticated com_keys_ids client server request tr with
    | (None, _) -> True
    | (Some (_, req_meta_data), tr_out) -> (
      event_triggered tr_out client (CommClientSendRequest authenticated client server request req_meta_data.key <: communication_reqres_event a) /\
      server == req_meta_data.server /\
      request == req_meta_data.request
    )
  ))
let send_request_properties #a #config tr authenticated com_keys_ids client server request =
  reveal_opaque (`%send_request) (send_request #a);
  ()
#pop-options

#restart-solver
#push-options "--z3rlimit 75"
val receive_request_authenticated_proof:
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
    match receive_request #a Authenticated comm_keys_ids server msg_id tr with
    | (None, tr_out) -> trace_invariant tr_out
    | (Some (payload, req_meta_data), tr_out) -> (
      trace_invariant tr_out /\
      event_triggered tr_out server (CommServerReceiveRequest req_meta_data.client server payload req_meta_data.key <: communication_reqres_event a) /\
      payload == req_meta_data.request /\
      server == req_meta_data.server
    )
  ))
let receive_request_authenticated_proof #invs a #config #crpreds tr comm_keys_ids server msg_id =
  reveal_opaque (`%receive_request) (receive_request #a);
  let (_, tr_out) = receive_request #a Authenticated comm_keys_ids server msg_id tr in

  receive_confidential_authenticated_proof tr (comm_core_higher_layer_event_preds_reqres a) comm_keys_ids server msg_id;
  let (x_recv, tr_recv) = receive_confidential_authenticated #comm_message_t #(comm_layer_tag_core_config_reqres a) comm_keys_ids server msg_id tr in
  assert(trace_invariant tr_recv);
  match x_recv with
  | None -> assert(tr_recv == tr_out)
  | Some cm ->
    let (x_gd, tr_gd) = guard_tr (RequestMessage? cm.payload) tr_recv in
    assert(trace_invariant tr_gd);
    match x_gd with
    | None -> assert(tr_gd == tr_out)
    | Some () ->
      let RequestMessage req_msg = cm.payload in
      let (x_pr, tr_pr) = return (parse a req_msg.request) tr_gd in
      assert(trace_invariant tr_pr);
      match x_pr with
      | None -> assert(tr_pr == tr_out)
      | Some request ->
        let req_send_event:communication_reqres_event a = CommClientSendRequest Authenticated cm.sender server request req_msg.key in

        confauth_message_properties' tr_pr (comm_core_higher_layer_event_preds_reqres a) cm.sender server cm.payload;
        
        // Properties that can be proved uniformly in both the honest and corrupt case
        eliminate event_triggered tr_pr cm.sender req_send_event \/ is_well_formed (comm_message_t) (is_publishable tr_pr) cm.payload
        returns (
          is_well_formed a (is_knowable_by (get_label tr_pr req_msg.key) tr_pr) request /\
          req_msg.key `has_usage tr_pr` (AeadKey (comm_layer_aead_tag a) empty)
        )
        with _. (
          let i = find_event_triggered_at_timestamp tr_pr cm.sender req_send_event in
          assert(event_predicate_communication_layer_reqres a (prefix tr_pr i) cm.sender req_send_event);
          ()
        )
        and _. (has_usage_publishable tr_pr req_msg.key (AeadKey (comm_layer_aead_tag a) empty);
          parse_wf_lemma a (is_publishable tr_pr) req_msg.request;
          ()
        );
        
        confauth_message_properties tr_pr (comm_core_higher_layer_event_preds_reqres a) cm.sender server cm.payload;
        assert((event_predicate_communication_layer_reqres a) tr_pr server (CommServerReceiveRequest (Some cm.sender) server request req_msg.key <: communication_reqres_event a)) by (
          let open FStar.Tactics in
          norm [delta_only [`%event_predicate_communication_layer_reqres]; iota];
          dump "";
          ()
        );
        let ((), tr_ev) = trigger_event server (CommServerReceiveRequest (Some cm.sender) server request req_msg.key <: communication_reqres_event a) tr_pr in
        assert(trace_invariant tr_ev);

        let (sid', tr_sess) = new_session_id server tr_ev in

        assert((state_predicate_communication_layer_reqres a).pred tr_sess server sid' (ServerReceiveRequest {client=Some cm.sender; request; key=req_msg.key} <: communication_states a));
        let ((), tr_st) = set_state server sid' (ServerReceiveRequest {client=Some cm.sender; request; key=req_msg.key} <: communication_states a) tr_sess in
        assert(trace_invariant tr_st);
        
        assert(tr_out == tr_st);
        ()
#pop-options

#push-options "--z3rlimit 20"
val helper_lemma_request_properties:
  {|protocol_invariants|} ->
  a:Type -> {|comm_layer_reqres_config a|} ->
  {|crpreds:comm_reqres_preds a|} ->
  tr:trace -> server:principal ->
  req_msg_t:comm_message_t ->
  request:a -> req_msg:request_message ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_predicates a /\
    RequestMessage req_msg == req_msg_t /\
    Some request == parse a req_msg.request /\
    event_triggered tr server (CommConfReceiveMsg server req_msg_t <: communication_core_event comm_message_t #(comm_layer_tag_core_config_reqres a))
  )
  (ensures
    is_knowable_by (principal_label server) tr req_msg.key /\
    is_well_formed a (is_knowable_by (get_label tr req_msg.key) tr) request /\
    req_msg.key `has_usage tr` (AeadKey (comm_layer_aead_tag a) empty) /\ (
      (exists client. event_triggered #(communication_reqres_event a) #(event_communication_reqres_event #a) tr client (CommClientSendRequest Unauthenticated client server request req_msg.key)) \/
        (is_publishable tr req_msg.request /\ is_publishable tr req_msg.key)
    )
  )
let helper_lemma_request_properties #invs a #config #crpreds tr server req_msg_t request req_msg =
  let req_send_event client:communication_reqres_event a = CommClientSendRequest Unauthenticated client server request req_msg.key in

  conf_message_properties tr (comm_core_higher_layer_event_preds_reqres a) server req_msg_t;

  // Properties that can be proved uniformly in both the honest and corrupt case
  eliminate (exists client. event_triggered tr client (req_send_event client)) \/
            (is_publishable tr req_msg.request /\ is_publishable tr req_msg.key)
  returns (
    is_knowable_by (principal_label server) tr req_msg.key /\
    is_well_formed a (is_knowable_by (get_label tr req_msg.key) tr) request /\
    req_msg.key `has_usage tr` (AeadKey (comm_layer_aead_tag a) empty)
  )
  with _. (eliminate exists client. event_triggered tr client (req_send_event client)
    returns _
    with _. (
      let i = find_event_triggered_at_timestamp tr client (req_send_event client) in
      assert(event_predicate_communication_layer_reqres a (prefix tr i) client (req_send_event client));
      ()
    )
  )
  and _. (has_usage_publishable tr req_msg.key (AeadKey (comm_layer_aead_tag a) empty);
    parse_wf_lemma a (is_publishable tr) req_msg.request;
    ()
  )
#pop-options

#push-options "--z3rlimit 150"
val receive_request_unauthenticated_proof:
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
    match receive_request #a Unauthenticated comm_keys_ids server msg_id tr with
    | (None, tr_out) -> trace_invariant tr_out
    | (Some (payload, req_meta_data), tr_out) -> (
      trace_invariant tr_out /\
      event_triggered tr_out server (CommServerReceiveRequest req_meta_data.client server payload req_meta_data.key <: communication_reqres_event a) /\
      payload == req_meta_data.request /\
      server == req_meta_data.server
    )
  ))
let receive_request_unauthenticated_proof #invs a #config #crpreds tr comm_keys_ids server msg_id =
  reveal_opaque (`%receive_request) (receive_request #a);
  let (_, tr_out) = receive_request #a Unauthenticated comm_keys_ids server msg_id tr in

  receive_confidential_proof tr (comm_core_higher_layer_event_preds_reqres a) comm_keys_ids server msg_id;
  let (x_recv, tr_recv) = receive_confidential #comm_message_t #(comm_layer_tag_core_config_reqres a) comm_keys_ids server msg_id tr in
  assert(trace_invariant tr_recv);
  match x_recv with
  | None -> assert(tr_recv == tr_out)
  | Some req_msg_t ->
    let (x_gd, tr_gd) = guard_tr (RequestMessage? req_msg_t) tr_recv in
    assert(trace_invariant tr_gd);
    match x_gd with
    | None -> assert(tr_gd == tr_out)
    | Some () ->
      let RequestMessage req_msg = req_msg_t in
      let (x_pr, tr_pr) = return (parse a req_msg.request) tr_gd in
      assert(trace_invariant tr_pr);
      match x_pr with
      | None -> assert(tr_pr == tr_out)
      | Some request ->
        helper_lemma_request_properties a tr_pr server req_msg_t request req_msg;
        
        assert((event_predicate_communication_layer_reqres a) tr_pr server (CommServerReceiveRequest None server request req_msg.key <: communication_reqres_event a)) by (
          let open FStar.Tactics in
          norm [delta_only [`%event_predicate_communication_layer_reqres]; iota];
          dump "";
          ()
        );
        let ((), tr_ev) = trigger_event server (CommServerReceiveRequest None server request req_msg.key <: communication_reqres_event a) tr_pr in
        assert(trace_invariant tr_ev);
        let (sid', tr_sess) = new_session_id server tr_ev in

        assert((state_predicate_communication_layer_reqres a).pred tr_sess server sid' (ServerReceiveRequest {client=None; request; key=req_msg.key} <: communication_states a));
        let ((), tr_st) = set_state server sid' (ServerReceiveRequest {client=None; request; key=req_msg.key} <: communication_states a) tr_sess in
        assert(trace_invariant tr_st);

        assert(tr_out == tr_st);
        ()
#pop-options

#push-options "--ifuel 1"
val receive_request_proof:
  {|invs:protocol_invariants|} ->
  a:Type -> {|comm_layer_reqres_config a|} ->
  {|crpreds:comm_reqres_preds a|} ->
  tr:trace ->
  authenticated:sender_authentication ->
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
    match receive_request #a authenticated comm_keys_ids server msg_id tr with
    | (None, tr_out) -> trace_invariant tr_out
    | (Some (payload, req_meta_data), tr_out) -> (
      trace_invariant tr_out /\
      event_triggered tr_out server (CommServerReceiveRequest req_meta_data.client server payload req_meta_data.key <: communication_reqres_event a) /\
      payload == req_meta_data.request /\
      server == req_meta_data.server
    )
  ))
  [SMTPat (trace_invariant tr);
  SMTPat (reqres_comm_layer_lemmas_enabled a);
  SMTPat (receive_request #a authenticated comm_keys_ids server msg_id tr)]
let receive_request_proof #invs a #config #crpreds tr authenticated comm_keys_ids server msg_id =
  match authenticated with
  | Authenticated -> receive_request_authenticated_proof a tr comm_keys_ids server msg_id
  | Unauthenticated -> receive_request_unauthenticated_proof a tr comm_keys_ids server msg_id
#pop-options


(**** Proof for Response ****)

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

#push-options "--ifuel 1 --z3rlimit 20"
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
    event_triggered tr server (CommServerSendResponse req_meta_data.client server request response req_meta_data.key <: communication_reqres_event a)
  )
  (ensures
    is_publishable tr (compute_response_message #a server req_meta_data nonce response)
  )
let compute_response_message_proof #cinvs #a tr server req_meta_data nonce request response =
  reveal_opaque (`%compute_response_message) (compute_response_message #a);
  get_response_label_eq_key_label tr req_meta_data;
  let res_bytes = serialize a response in
  serialize_wf_lemma a (is_knowable_by (get_response_label tr req_meta_data) tr) response;
  let ad:authenticated_data = {client=req_meta_data.client; server} in
  let ad_bytes = serialize authenticated_data ad in
  serialize_wf_lemma authenticated_data (is_publishable tr) ad;
  let ciphertext = aead_enc req_meta_data.key nonce res_bytes ad_bytes in
  // Needed for the case that the key is publishable
  FStar.Classical.move_requires (aead_enc_preserves_publishability tr req_meta_data.key nonce res_bytes) ad_bytes;
  serialize_wf_lemma comm_message_t (is_publishable tr) (ResponseMessage {nonce; ciphertext});
  ()
#pop-options

#restart-solver
#push-options "--z3rlimit 20"
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
    event_triggered tr server (CommServerReceiveRequest req_meta_data.client server req_meta_data.request req_meta_data.key <: communication_reqres_event a) /\
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
    let ((), tr_ev) = trigger_event server (CommServerSendResponse req_meta_data.client server req_meta_data.request response req_meta_data.key <: communication_reqres_event a) tr_st in
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


#push-options "--ifuel 1 --z3rlimit 50"
val decode_response_proof:
  {|crypto_invariants|} ->
  #a:Type -> {|comm_layer_reqres_config a|} ->
  tr:trace ->
  client:principal ->
  response_bytes:bytes -> req_meta_data:comm_meta_data a ->
  Lemma
  (requires
    has_communication_layer_reqres_crypto_predicates a /\
    is_publishable tr response_bytes /\
    is_secret (comm_label client req_meta_data.server) tr req_meta_data.key /\
    req_meta_data.key `has_usage tr` (AeadKey (comm_layer_aead_tag a) empty)
  )
  (ensures (
    match decode_response_message req_meta_data.server req_meta_data.key response_bytes req_meta_data with
    | None -> True
    | Some response -> (
      is_well_formed a (is_knowable_by (comm_label client req_meta_data.server) tr) response /\
      is_knowable_by (get_label tr req_meta_data.key) tr (serialize a response) /\
      ((exists request. event_triggered tr req_meta_data.server (CommServerSendResponse req_meta_data.client req_meta_data.server request response req_meta_data.key <: communication_reqres_event a))
        \/ is_corrupt tr (principal_label client) \/ is_corrupt tr (principal_label req_meta_data.server))
    )
  ))
let decode_response_proof #invs #a tr client response_bytes req_meta_data =
  reveal_opaque (`%decode_response_message) (decode_response_message #a);
  match decode_response_message #a req_meta_data.server req_meta_data.key response_bytes req_meta_data with
  | None -> ()
  | Some response -> (
    parse_wf_lemma comm_message_t (is_publishable tr) response_bytes;
    let Some (ResponseMessage {nonce; ciphertext}) = parse comm_message_t response_bytes in
    serialize_wf_lemma authenticated_data (is_publishable tr) {client=req_meta_data.client; server=req_meta_data.server};
    let ad_bytes = serialize authenticated_data {client=req_meta_data.client; server=req_meta_data.server} in
    let Some res_bytes = aead_dec req_meta_data.key nonce ciphertext ad_bytes in
    serialize_parse_inv_lemma a res_bytes;
    ()
  )
#pop-options

#push-options "--z3rlimit 10"
val comm_client_send_request_injective:
  {|protocol_invariants|} ->
  #a:Type -> {| comm_layer_reqres_config a |} ->
  {|crpreds:comm_reqres_preds a|} ->
  tr:trace -> authenticated:sender_authentication ->
  client:principal -> client':principal -> server:principal ->
  request:a -> request':a -> key:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_predicates a /\
    event_triggered tr client' (CommClientSendRequest authenticated client' server request' key <: communication_reqres_event a) /\
    event_triggered tr client (CommClientSendRequest authenticated client server request key <: communication_reqres_event a)
  )
  (ensures
    client == client' /\
    request == request'
  )
let comm_client_send_request_injective #invs #a #config #crpreds tr authenticated client client' server request request' key = ()
#pop-options

#push-options "--z3rlimit 100"
val request_response_property:
  {|protocol_invariants|} ->
  #a:Type -> {|comm_layer_reqres_config a|} ->
  {|comm_reqres_preds a|} ->
  tr:trace ->
  client:principal -> response:a ->
  req_meta_data:comm_meta_data a ->
  Lemma
  (requires
    trace_invariant tr /\
    has_communication_layer_reqres_predicates a /\
    event_triggered tr client (CommClientSendRequest (request_authenticated req_meta_data) client req_meta_data.server req_meta_data.request req_meta_data.key <: communication_reqres_event a) /\
    is_secret (comm_label client req_meta_data.server) tr req_meta_data.key /\
    req_meta_data.key `has_usage tr` (AeadKey (comm_layer_aead_tag a) empty) /\
    (match req_meta_data.client with
    | None -> true
    | Some client' ->  client = client') /\
    (exists request'. event_triggered tr req_meta_data.server (CommServerSendResponse req_meta_data.client req_meta_data.server request' response req_meta_data.key <: communication_reqres_event a)
        \/ is_corrupt tr (principal_label client) \/ is_corrupt tr (principal_label req_meta_data.server))
  )
  (ensures
    (
      event_triggered tr req_meta_data.server (CommServerSendResponse req_meta_data.client req_meta_data.server req_meta_data.request response req_meta_data.key <: communication_reqres_event a) (*/\
      event_triggered tr server (CommServerReceiveRequest (match (request_authenticated req_meta_data) with | Authenticated -> Some client | Unauthenticated -> None) server request req_meta_data.key <: communication_reqres_event a)*)
    ) \/ is_corrupt tr (principal_label client) \/ is_corrupt tr (principal_label req_meta_data.server)
  )
let request_response_property #invs #a #config #crpreds tr client response req_meta_data =
  let send_event request:communication_reqres_event a = CommServerSendResponse req_meta_data.client req_meta_data.server request response req_meta_data.key in
  introduce (~(is_corrupt tr (principal_label client) \/ is_corrupt tr (principal_label req_meta_data.server))) ==> 
    (exists request'. event_triggered #(communication_reqres_event a) #(event_communication_reqres_event #a #config) tr req_meta_data.server (CommServerSendResponse req_meta_data.client req_meta_data.server request' response req_meta_data.key <: communication_reqres_event a)) 
  with _. (
    eliminate exists request'. event_triggered tr req_meta_data.server (CommServerSendResponse req_meta_data.client req_meta_data.server request' response req_meta_data.key <: communication_reqres_event a)
    returns event_triggered tr req_meta_data.server (CommServerSendResponse req_meta_data.client req_meta_data.server req_meta_data.request response req_meta_data.key <: communication_reqres_event a) /\
            event_triggered tr req_meta_data.server (CommServerReceiveRequest req_meta_data.client req_meta_data.server req_meta_data.request req_meta_data.key <: communication_reqres_event a)
    with _. (
      let j = find_event_triggered_at_timestamp tr req_meta_data.server (send_event request') in
      assert((event_predicate_communication_layer_reqres a) (prefix tr j) req_meta_data.server (send_event request'));
      assert(event_triggered tr req_meta_data.server (CommServerReceiveRequest req_meta_data.client req_meta_data.server request' req_meta_data.key <: communication_reqres_event a));
      match req_meta_data.client with
      | None -> (
        assert(exists client'. 
          event_triggered tr client' (CommClientSendRequest (request_authenticated req_meta_data) client' req_meta_data.server request' req_meta_data.key <: communication_reqres_event a));
        eliminate exists client'. event_triggered tr client' (CommClientSendRequest (request_authenticated req_meta_data) client' req_meta_data.server request' req_meta_data.key <: communication_reqres_event a)
        returns event_triggered tr req_meta_data.server (CommServerSendResponse req_meta_data.client req_meta_data.server req_meta_data.request response req_meta_data.key <: communication_reqres_event a) /\
                event_triggered tr req_meta_data.server (CommServerReceiveRequest req_meta_data.client req_meta_data.server req_meta_data.request req_meta_data.key <: communication_reqres_event a)
        with _. (
          comm_client_send_request_injective tr (request_authenticated req_meta_data) client client' req_meta_data.server req_meta_data.request request' req_meta_data.key;
          ()
        )
      )
      | Some client'' -> (
        assert(client'' == client);
        assert(
          event_triggered tr client (CommClientSendRequest (request_authenticated req_meta_data) client req_meta_data.server request' req_meta_data.key <: communication_reqres_event a) \/
          is_corrupt tr (long_term_key_label client)
        );
        eliminate event_triggered tr client (CommClientSendRequest (request_authenticated req_meta_data) client req_meta_data.server request' req_meta_data.key <: communication_reqres_event a) \/ 
          is_corrupt tr (long_term_key_label client)
        returns _
        with _. (
          comm_client_send_request_injective tr (request_authenticated req_meta_data) client client req_meta_data.server req_meta_data.request request' req_meta_data.key;
          ()
        )
        and _. (
          assert((principal_label client) `can_flow tr` (long_term_key_label client));
          assert(is_corrupt tr (principal_label client));
          ()
        )
      )
    )
  )
#pop-options

#push-options "--z3rlimit 200"
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
    // TODO shouldn't this be put into the state invariant?
    event_triggered tr client (CommClientSendRequest (request_authenticated req_meta_data) client req_meta_data.server req_meta_data.request req_meta_data.key <: communication_reqres_event a)
  )
  (ensures (
    match receive_response client req_meta_data msg_id tr with
    | (None, tr_out) -> trace_invariant tr_out
    | (Some (payload, _), tr_out) -> (
      trace_invariant tr_out /\
      event_triggered tr_out client (CommClientReceiveResponse client payload req_meta_data <: communication_reqres_event a)
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
    let (Some state, tr'):(option (communication_states a) & trace) = get_state client req_meta_data.sid tr in
    let ClientSendRequest csr = state in
    let server = csr.server in
    let key = csr.key in
    let (Some resp_msg_bytes, tr') = recv_msg msg_id tr' in
    decode_response_proof #invs.crypto_invs #a tr' client resp_msg_bytes req_meta_data;
    let Some response = decode_response_message server key resp_msg_bytes req_meta_data in

    assert((state_predicate_communication_layer_reqres a).pred tr' client req_meta_data.sid (ClientReceiveResponse {server; response; key} <: communication_states a));
    let ((), tr_st) = set_state client req_meta_data.sid (ClientReceiveResponse {server; response; key} <: communication_states a) tr' in
    assert(trace_invariant tr_st) by (
      let open FStar.Tactics in
      let _ = tcut (quote (squash (
        let (_, tr_st) = set_state #(communication_states a) #(local_state_communication_layer_session a) client req_meta_data.sid (ClientReceiveResponse {server; response; key} <: communication_states a) tr' in
        trace_invariant tr_st
      ))) in

      smt ();
      apply_lemma (`set_state_invariant);
      exact (quote state_predicate_communication_layer_reqres a);
      exact (quote default_local_state_update_pred (communication_states a));
      let _ = repeatn 4 split in
      assumption ();
      smt ();
      smt ();
      smt ();
      smt ();

      dump "";
      ()
    );

    request_response_property tr_st client response req_meta_data;
    assert(
      is_well_formed a (is_knowable_by (comm_label client req_meta_data.server) tr_st) response /\
      is_secret (comm_label client req_meta_data.server) tr_st req_meta_data.key
    );
    assert(event_triggered tr_st client (CommClientSendRequest (request_authenticated req_meta_data) client req_meta_data.server req_meta_data.request req_meta_data.key <: communication_reqres_event a));
    let ((), tr_ev) = trigger_event client (CommClientReceiveResponse client response req_meta_data <: communication_reqres_event a) tr_st in
    assert(trace_invariant tr_ev) by (
      let open FStar.Tactics in
      let _ = tcut (quote (squash (
        let ((), tr_ev) = trigger_event #(communication_reqres_event a) #(event_communication_reqres_event #a) client (CommClientReceiveResponse client response req_meta_data <: communication_reqres_event a) tr_st in
        trace_invariant tr_ev
      ))) in

      smt ();

      apply_lemma (`trigger_event_trace_invariant);
      exact (quote event_predicate_communication_layer_reqres a);
      let _ = repeatn 2 split in
      
      // (event_predicate_communication_layer_reqres a) tr_st client (CommClientReceiveResponse client response req_meta_data <: communication_reqres_event a)
      norm [delta_only [`%event_predicate_communication_layer_reqres]; iota];
      let _ = repeatn 2 split in
      smt ();
      assumption ();
      assumption ();

      smt ();
      assumption ();

      dump "";
      ()
    );
    
    assert(tr_out == tr_ev);
    ()
  )
#pop-options
