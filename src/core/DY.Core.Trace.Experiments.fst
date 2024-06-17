module DY.Core.Trace.Experiments

open DY.Core.Trace.Invariant
open DY.Core.Trace.State.Aux
open DY.Core.Trace.Manipulation
module BT = DY.Core.Bytes.Type
module B = DY.Core.Bytes
open DY.Core.Label.Type
open DY.Core.Trace.Type

#set-options "--fuel 1 --ifuel 1"

val init_is_prefix:
  tr:trace{Snoc? tr} ->
  Lemma 
  (let Snoc init _ = tr in
    init <$ tr
  )
let init_is_prefix tr =
    reveal_opaque (`%grows) (grows);
    norm_spec [zeta; delta_only [`%prefix]] (prefix)
    
let rec trace_concat tr1 tr2 =
  match tr2 with
  | Nil -> tr1
  | Snoc init2 ev2 ->
      Snoc (trace_concat tr1 init2) ev2
      

val trace_concat_grows:
  tr1:trace -> tr2:trace ->
  Lemma (tr1 <$ trace_concat tr1 tr2)
//  [SMTPat (trace_concat tr1 tr2)]
let rec trace_concat_grows tr1 tr2 =
    reveal_opaque (`%grows) (grows);
    norm_spec [zeta; delta_only [`%prefix]] (prefix);
    match tr2 with
    | Nil -> ()
    | Snoc init ev -> 
           trace_concat_grows tr1 init

#push-options "--fuel 2"
val no_set_state_entry_for_concat:
  p:principal -> sid:state_id ->
  tr1: trace -> tr2:trace ->
  Lemma
    (requires 
        no_set_state_entry_for p sid tr1
      /\ no_set_state_entry_for p sid tr2
    )
    (ensures
      no_set_state_entry_for p sid (tr1 `trace_concat` tr2)
    )
    // [SMTPat (no_set_state_entry_for p sid tr1)
    // ; SMTPat (no_set_state_entry_for p sid tr2)]
let rec no_set_state_entry_for_concat p sid tr1 tr2 =
  match tr2 with
  | Nil -> ()
  | Snoc init2 ev2 -> 
    init_is_prefix tr2;
    assert(event_exists tr2 ev2);
    no_set_state_entry_for_prefix p sid init2 tr2;
    no_set_state_entry_for_concat p sid tr1 init2
#pop-options

#push-options "--fuel 2"
val suffix_after_concat:
  tr1:trace -> tr2:trace {tr1 <$ tr2} -> tr3:trace{tr2 <$ tr3} ->
  Lemma
  ( tr3 `suffix_after` tr1 == (tr2 `suffix_after` tr1) `trace_concat` (tr3 `suffix_after` tr2)
  )
let rec suffix_after_concat tr1 tr2 tr3 =     
  reveal_opaque (`%grows) (grows);
  norm_spec [zeta; delta_only [`%prefix]] (prefix);
  match tr3 with
  | Nil -> ()
  | Snoc init ev -> 
      if length tr2 = length tr3
        then ()
        else suffix_after_concat tr1 tr2 init
#pop-options

val no_set_state_entry_for_suffixes_transitive:
  p:principal -> sid:state_id ->
  tr1:trace -> tr2:trace{tr1 <$ tr2} -> tr3:trace{tr2 <$ tr3} ->
  Lemma
  (requires
      no_set_state_entry_for p sid (tr2 `suffix_after` tr1)
    /\ no_set_state_entry_for p sid (tr3 `suffix_after` tr2)
  )
  (ensures
    no_set_state_entry_for p sid (tr3 `suffix_after` tr1)
  )
let no_set_state_entry_for_suffixes_transitive p sid tr1 tr2 tr3 =
  suffix_after_concat tr1 tr2 tr3;
  no_set_state_entry_for_concat p sid (tr2 `suffix_after` tr1) (tr3 `suffix_after` tr2)

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
