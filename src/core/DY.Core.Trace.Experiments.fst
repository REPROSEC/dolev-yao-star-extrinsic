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
      
#push-options "--fuel 2"
let trace_concat_singleton_lemma tr1 ev :
  Lemma (trace_concat tr1 (Snoc Nil ev) = Snoc tr1 ev)
  [SMTPat (trace_concat tr1 (Snoc Nil ev))]
= ()
#pop-options

let rec trace_concat_event_exists_lemma tr1 tr2 :
  Lemma (forall ev. event_exists tr1 ev \/ event_exists tr2 ev ==> event_exists (trace_concat tr1 tr2) ev) =
  match tr2 with
  | Nil -> ()
  | Snoc init _ -> trace_concat_event_exists_lemma tr1 init

val exists_set_state_entry_for:
  principal -> state_id -> trace -> prop
let exists_set_state_entry_for p sid tr = 
  exists (ts:nat{ts < DY.Core.Trace.Type.length tr}). 
      match get_event_at tr ts with
      | SetState p' sid' _ -> p' = p && sid' = sid
      | _ -> False
  
val no_set_state_entry_for:
  principal -> state_id -> trace -> prop
let no_set_state_entry_for p sid tr = 
//   ~ ( exists_set_state_entry_for p sid tr)
  forall (ts:timestamp{ts < DY.Core.Trace.Type.length tr}).
    match get_event_at tr ts with
    | SetState p' sid' _ -> p' <> p \/ sid' <> sid
    | _ -> True

#push-options "--fuel 2"
val no_set_state_entry_for_snoc :
  p:principal -> sid:state_id -> tr:trace -> ev:trace_event ->
  Lemma
    (requires 
       no_set_state_entry_for p sid tr /\
       (match ev with
        | SetState p' sid' _ -> p' <> p \/ sid' <> sid
        | _ -> True
       )
    )
    (ensures no_set_state_entry_for p sid (Snoc tr ev))
let no_set_state_entry_for_snoc p sid tr ev = ()
#pop-options

// TODO: hier weiter machen
#push-options "--fuel 2"
val no_set_state_entry_for_concat:
 p:principal -> sid:state_id -> tr1:trace -> tr2:trace -> 
 Lemma 
   (requires no_set_state_entry_for p sid tr1 /\ no_set_state_entry_for p sid tr2)
   (ensures no_set_state_entry_for p sid (trace_concat tr1 tr2))
let rec no_set_state_entry_for_concat p sid tr1 tr2 = 
  match tr2 with
  | Nil -> admit()
  | Snoc init (SetState p' sid' v) ->  
         assert(event_at tr2 (DY.Core.Trace.Type.length tr2 -1) (SetState p' sid' v));
         assume(no_set_state_entry_for p sid init);
         no_set_state_entry_for_concat p sid tr1 init
  | Snoc init _ -> admit()

#push-options "--fuel 2"
let _ = 
  let p = "p" in
  let sid = {the_id = 1} in
  let b = Literal (FStar.Seq.Base.empty) in
  let tr = Nil in
  assert(no_set_state_entry_for p sid tr);
  let tr' = Snoc Nil (SetState p sid b) in
//  assert(DY.Core.Trace.Type.length tr' = 1);
  assert(get_event_at tr' 0 = SetState p sid b);
  assert(exists_set_state_entry_for p sid tr');
  assert(no_set_state_entry_for "b" sid tr')
#pop-options

val suffix_after_event_aux:
  ev:trace_event -> tr:trace{event_exists tr ev} -> trace -> trace
let rec suffix_after_event_aux the_ev tr accum =
  match tr with
  | Snoc init ev ->
      if ev <> the_ev 
        then suffix_after_event_aux the_ev init (Snoc accum ev)
        else accum

val suffix_after_event:
  ev:trace_event -> tr:trace{event_exists tr ev} -> trace
let suffix_after_event ev tr = suffix_after_event_aux ev tr Nil

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
//         assert(event_exists tr (SetState p' sid' v))
       end
       else get_state_aux_state_was_set p sid init
  | Snoc init _ -> get_state_aux_state_was_set p sid init

#push-options "--fuel 4"
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
let rec get_state_aux_returns_last_set_state p sid tr =
  match get_state_aux p sid tr with
  | None -> ()
  | Some v -> begin
      match tr with
      | Nil -> ()
      | Snoc init (SetState p' sid' v') ->
          if p' = p && sid' = sid
            then ()
            else begin 
              get_state_aux_returns_last_set_state p sid init
              ; assert(no_set_state_entry_for p sid 
                  (suffix_after_event (SetState p sid v) init)
                  )
              ; assert(forall tr1 tr2. no_set_state_entry_for p sid tr1 /\ no_set_state_entry_for p sid tr2 ==> no_set_state_entry_for p sid (trace_concat tr1 tr2))
              ; assume(suffix_after_event (SetState p sid v) tr 
                  = Snoc (suffix_after_event (SetState p sid v) init)
                      (SetState p' sid' v')
                  )
              ; trace_concat_singleton_lemma (suffix_after_event (SetState p sid v) init) (SetState p' sid' v')      
              ; assert(no_set_state_entry_for p sid (Snoc Nil (SetState p' sid' v')))
//              ; admit()
            end
      | Snoc init _ -> admit()
  end
