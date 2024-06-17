module DY.Core.Trace.Experiments

open DY.Core.Trace.Invariant
open DY.Core.Trace.State.Aux
open DY.Core.Trace.Manipulation
module BT = DY.Core.Bytes.Type
module B = DY.Core.Bytes
open DY.Core.Label.Type
open DY.Core.Trace.Type

#set-options "--fuel 2 --ifuel 1"

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

val suffix_after_event:
  ev:trace_event -> tr:trace{event_exists tr ev} -> trace
let rec suffix_after_event the_ev tr =
  match tr with
  | Snoc init ev ->
      if ev <> the_ev 
        then Snoc (suffix_after_event the_ev init) ev
        else Nil

let _ =
  let ev1 = MsgSent (BT.Literal FStar.Seq.Base.empty) in
  let ev2 = Corrupt "p" {the_id = 1} in
  let tr = Snoc (Snoc Nil ev1) ev2 in
  assert(suffix_after_event ev2 tr = Nil);
  assert(suffix_after_event ev1 tr = Snoc Nil ev2);
  let tr' = Snoc (Snoc (Snoc Nil ev1) ev1) ev2 in  
  assert(suffix_after_event ev1 tr' = Snoc Nil ev2)


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
   // [SMTPat (get_state_aux p sid tr)]
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
   // [SMTPat (get_state p sid tr)]
let get_state_returns_last_set_state p sid tr =
  reveal_opaque (`%get_state) (get_state);
  get_state_aux_returns_last_set_state p sid tr




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
