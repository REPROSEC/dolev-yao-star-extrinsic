module DY.Core.Trace.State.NoSetStateEntry

open DY.Core.Label.Type
open DY.Core.Trace.Type
open DY.Core.Trace.PrefixSuffix
open DY.Core.List

/// The main property we want to show is
/// that a particular session of a principal stays the same
/// if there are no more `SetState` entries for this principal and this session on the trace.




/// if there are no state entries on a trace,
/// this is true for any prefix of the trace.

val no_set_state_entry_for_prefix:
  p:principal -> sid:state_id -> tr1:trace -> tr2:trace ->
  Lemma 
    (requires no_set_state_entry_for p sid tr2 /\ tr1 <$ tr2)
    (ensures no_set_state_entry_for p sid tr1)
    [SMTPat (no_set_state_entry_for p sid tr2); SMTPat (tr1 <$ tr2)]
let no_set_state_entry_for_prefix p sid tr1 tr2 = 
  introduce forall (ts:timestamp{ts < length tr1}). get_event_at tr1 ts = get_event_at tr2 ts
  with begin
    let ev1 = get_event_at tr1 ts in
    event_at_grows tr1 tr2 ts ev1
    end


/// concatenating traces without state entries
/// results in no state entries
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

/// transitivity of `no_set_state_entry_for` on suffixes of growing traces
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



let no_set_state_entry_for_p (p:principal) (tr:trace) =
  forall sid. no_set_state_entry_for p sid tr



let rec no_set_state_entry_for_on_suffix (tr:trace) (suff:trace) (p:principal) (sid:state_id):
  Lemma
  (requires 
    tr `has_suffix` suff /\ no_set_state_entry_for p sid tr
  )
  (ensures
    no_set_state_entry_for p sid suff
  )
  = match suff with
  | Nil -> ()
  | Snoc suff_init suff_ev ->
         match tr with
         | Nil -> ()
         | Snoc tr_init tr_ev -> 
                init_is_prefix tr;
                no_set_state_entry_for_on_suffix tr_init suff_init p sid;
                assert(event_exists tr tr_ev)
