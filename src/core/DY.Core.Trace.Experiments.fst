module DY.Core.Trace.Experiments

open DY.Core.Trace.Type
open DY.Core.Trace.Invariant
open DY.Core.Trace.Manipulation
open DY.Core.Bytes.Type
open DY.Core.Bytes
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
  let b = Literal (FStar.Seq.Base.empty) in
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



val get_state_aux_state_was_set :
  p:principal -> sid:state_id -> tr:trace ->
  Lemma
    (requires True)
    (ensures (
       match (get_state_aux p sid tr) with
       | None -> True
       | Some v -> state_was_set tr p sid v
      )
    )
    [SMTPat (get_state_aux p sid tr)]
let rec get_state_aux_state_was_set p sid tr =
  match tr with
  | Nil -> ()
  | Snoc init (SetState p' sid' v) ->
     if p' = p && sid' = sid 
       then begin
         let ev = (SetState p' sid' v) in
         assert(event_at tr (DY.Core.Trace.Type.length tr - 1) ev)
       end
       else get_state_aux_state_was_set p sid init
  | Snoc init _ -> get_state_aux_state_was_set p sid init


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
  let ev1 = MsgSent (Literal FStar.Seq.Base.empty) in
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
