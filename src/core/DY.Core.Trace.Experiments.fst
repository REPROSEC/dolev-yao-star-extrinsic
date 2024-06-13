module DY.Core.Trace.Experiments

open DY.Core.Trace.Type
open DY.Core.Trace.Invariant
open DY.Core.Trace.State.Aux
open DY.Core.Trace.Manipulation
module BT = DY.Core.Bytes.Type
module B = DY.Core.Bytes
open DY.Core.Label.Type

#set-options "--fuel 1 --ifuel 1"

let rec trace_concat tr1 tr2 =
  match tr2 with
  | Nil -> tr1
  | Snoc init2 ev2 ->
      Snoc (trace_concat tr1 init2) ev2
      

val trace_concat_grows:
  tr1:trace -> tr2:trace ->
  Lemma (tr1 <$ trace_concat tr1 tr2)
  [SMTPat (trace_concat tr1 tr2)]
let rec trace_concat_grows tr1 tr2 =
    reveal_opaque (`%grows) (grows);
    norm_spec [zeta; delta_only [`%prefix]] (prefix);
    match tr2 with
    | Nil -> ()
    | Snoc init ev -> 
           trace_concat_grows tr1 init

val no_set_state_entry_for:
  principal -> state_id -> trace -> prop
let no_set_state_entry_for p sid tr = 
  forall (ts:timestamp{ts < DY.Core.Trace.Type.length tr}).
    match get_event_at tr ts with
    | SetState p' sid' _ -> p' <> p \/ sid' <> sid
    | _ -> True


#push-options "--fuel 2"
let _ = 
  let p = "p" in
  let sid = {the_id = 1} in
  let b = BT.Literal (FStar.Seq.Base.empty) in
  let tr = Nil in
  assert(no_set_state_entry_for p sid tr);
  let tr' = Snoc Nil (SetState p sid b) in
  assert(get_event_at tr' 0 = SetState p sid b);
  assert(~(no_set_state_entry_for p sid tr'));
  assert(no_set_state_entry_for "b" sid tr')
#pop-options

val no_set_state_entry_for_prefix:
  p:principal -> sid:state_id -> tr1:trace -> tr2:trace ->
  Lemma 
    (requires no_set_state_entry_for p sid tr2 /\ tr1 <$ tr2)
    (ensures no_set_state_entry_for p sid tr1)
    [SMTPat (no_set_state_entry_for p sid tr2); SMTPat (tr1 <$ tr2)]
let no_set_state_entry_for_prefix p sid tr1 tr2 = 
  introduce forall (ts:timestamp{ts < DY.Core.Trace.Type.length tr1}). get_event_at tr1 ts = get_event_at tr2 ts
  with begin
    let ev1 = get_event_at tr1 ts in
    event_at_grows tr1 tr2 ts ev1
    end

val suffix_after_event:
  ev:trace_event -> tr:trace{event_exists tr ev} -> trace
let rec suffix_after_event the_ev tr =
  match tr with
  | Snoc init ev ->
      if ev <> the_ev 
        then Snoc (suffix_after_event the_ev init) ev
        else Nil

#push-options "--fuel 2"
let _ =
  let ev1 = MsgSent (BT.Literal FStar.Seq.Base.empty) in
  let ev2 = Corrupt "p" {the_id = 1} in
  let tr = Snoc (Snoc Nil ev1) ev2 in
  assert(suffix_after_event ev2 tr = Nil);
  assert(suffix_after_event ev1 tr = Snoc Nil ev2);
  let tr' = Snoc (Snoc (Snoc Nil ev1) ev1) ev2 in  
  assert(suffix_after_event ev1 tr' = Snoc Nil ev2)
#pop-options


#push-options "--fuel 2"
val get_state_aux_returns_last_set_state : 
  p:principal -> sid:state_id -> tr:trace ->
  Lemma
   (requires True)
   (ensures (
     match (get_state_aux p sid tr) with
     | None -> True
     | Some v -> no_set_state_entry_for p sid 
         (suffix_after_event (SetState p sid v) tr)
     )
   )
   [SMTPat (get_state_aux p sid tr)]
let rec get_state_aux_returns_last_set_state p sid tr =
  match get_state_aux p sid tr with
  | None -> ()
  | Some v -> begin
      match tr with
      | Nil -> ()
      | Snoc init (SetState p' sid' v') ->
            get_state_aux_returns_last_set_state p sid init
      | Snoc init ev ->
             assert(event_exists init (SetState p sid v));
             get_state_aux_returns_last_set_state p sid init
    end
#pop-options

val get_state_returns_last_set_state : 
  p:principal -> sid:state_id -> tr:trace ->
  Lemma
   (requires True)
   (ensures (
     match (get_state p sid tr) with
     | (None,_) -> True
     | (Some v,_) -> no_set_state_entry_for p sid 
         (suffix_after_event (SetState p sid v) tr)
     )
   )
   [SMTPat (get_state p sid tr)]
let get_state_returns_last_set_state p sid tr =
  reveal_opaque (`%get_state) (get_state)


val get_state_aux_is_last_of_get_session_aux:
  p:principal -> sid:state_id -> tr:trace ->
  Lemma 
    (requires True
    )
    (ensures (
      let session = get_session_aux p sid tr in
      match get_state_aux p sid tr with
      | None -> Nil? session
      | Some st -> Snoc? session /\ (let Snoc _ last = session in st = last)
    )
    )
let rec get_state_aux_is_last_of_get_session_aux p sid tr = 
  match tr with
  | Nil -> ()
  | Snoc init _ -> get_state_aux_is_last_of_get_session_aux p sid init



val get_state_is_last_of_get_session:
  p:principal -> sid:state_id -> tr:trace ->
  Lemma 
    (requires True
    )
    (ensures (
      let opt_session = get_session p sid tr in
      let (opt_state, _) = get_state p sid tr in
      match opt_state with
      | None -> None? opt_session
      | Some st -> Some? opt_session /\ Snoc? (Some?.v opt_session) /\ (let Some (Snoc _ last) = opt_session in st = last)
    )
    )
    [SMTPat (get_session p sid tr); SMTPat (get_state p sid tr)]
let get_state_is_last_of_get_session p sid tr =
    reveal_opaque (`%get_state) (get_state);
    get_state_aux_is_last_of_get_session_aux p sid tr


val suffix_after: tr2:trace -> tr1:trace{tr1 <$ tr2} -> trace
let rec suffix_after tr2 tr1 = 
  match tr2 with
  | Nil -> Nil
  | Snoc init ev -> 
      if length tr2 = length tr1
        then Nil
        else begin 
             reveal_opaque (`%grows) grows; 
             norm_spec [zeta; delta_only [`%prefix]] (prefix);
             Snoc (suffix_after init tr1) ev
         end

#push-options "--fuel 3"
let _ = 
  let ev1 = Corrupt "p" {the_id = 1} in
  let ev2 = Corrupt "q" {the_id = 1} in
  let ev3 = Corrupt "r" {the_id = 1} in
  let tr1 = Snoc Nil ev1 in
  let tr2 = Snoc (Snoc (Snoc Nil ev1) ev2) ev3 in
  reveal_opaque (`%grows) grows; 
  norm_spec [zeta; delta_only [`%prefix]] (prefix);
  assert(tr2 `suffix_after` tr2 = Nil);
  assert(tr1 <$ tr2);
  assert(tr2 `suffix_after` tr1 = Snoc (Snoc Nil ev2) ev3)
#pop-options



val suffix_after_for_prefix: 
  tr3:trace -> tr2:trace {tr2 <$ tr3} -> tr1:trace {tr1 <$ tr2} ->
  Lemma 
    (tr2 `suffix_after` tr1 <$ tr3 `suffix_after` tr1
    )
let rec suffix_after_for_prefix tr3 tr2 tr1 = 
  reveal_opaque (`%grows) grows; 
  norm_spec [zeta; delta_only [`%prefix]] (prefix);
  if length tr3 = length tr2 || length tr2 = length tr1
    then ()
    else begin
      match tr3 with
      | Nil -> ()
      | Snoc init ev -> suffix_after_for_prefix init tr2 tr1
    end

val get_state_aux_same:
  p:principal -> sid:state_id -> tr1:trace -> tr2:trace ->
  Lemma
    (requires
      tr1 <$ tr2 /\ no_set_state_entry_for p sid (tr2 `suffix_after` tr1)
    )
    (ensures get_state_aux p sid tr1 = get_state_aux p sid tr2)
 //   [SMTPat (tr1 <$ tr2 /\ no_set_state_entry_for p sid (tr2 `suffix_after` tr1))]
let rec get_state_aux_same p sid tr1 tr2 =
  reveal_opaque (`%grows) grows; 
  norm_spec [zeta; delta_only [`%prefix]] (prefix);

  if tr1 = tr2 
    then ()
    else begin
       match tr2 with
       | Nil -> ()
       | Snoc init ev -> 
              assert(event_exists (tr2 `suffix_after` tr1) ev);
              suffix_after_for_prefix tr2 init tr1;
              get_state_aux_same p sid tr1 init
    end

val get_state_same:
  p:principal -> sid:state_id -> tr1:trace -> tr2:trace ->
  Lemma
    (requires
      tr1 <$ tr2 /\ no_set_state_entry_for p sid (tr2 `suffix_after` tr1)
    )
    (ensures (
      let (s1,_) = get_state p sid tr1 in
      let (s2,_) = get_state p sid tr2 in
      s1 = s2
      )
    )
    [SMTPat (get_state p sid tr1); SMTPat (get_state p sid tr2) ]
let get_state_same p sid tr1 tr2 = 
  reveal_opaque (`%get_state) get_state;
  get_state_aux_same p sid tr1 tr2


val get_session_aux_same:
  p:principal -> sid:state_id -> tr1:trace -> tr2:trace ->
  Lemma
    (requires
      tr1 <$ tr2 /\ no_set_state_entry_for p sid (tr2 `suffix_after` tr1)
    )
    (ensures get_session_aux p sid tr1 = get_session_aux p sid tr2)
 //   [SMTPat (tr1 <$ tr2 /\ no_set_state_entry_for p sid (tr2 `suffix_after` tr1))]
let rec get_session_aux_same p sid tr1 tr2 =
  reveal_opaque (`%grows) grows; 
  norm_spec [zeta; delta_only [`%prefix]] (prefix);

  if tr1 = tr2 
    then ()
    else begin
       match tr2 with
       | Nil -> ()
       | Snoc init ev -> 
              assert(event_exists (tr2 `suffix_after` tr1) ev);
              suffix_after_for_prefix tr2 init tr1;
              get_session_aux_same p sid tr1 init
    end
