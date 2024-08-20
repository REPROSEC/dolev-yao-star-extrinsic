module DY.Core.Trace.State.NoSetStateEntry

open DY.Core.Label.Type
open DY.Core.Trace.Type
open DY.Core.Trace.PrefixSuffix
open DY.Core.List




/// alternative definition of [no_set_state_entry_for] using timestamps
val no_set_state_entry_for_:
  principal -> state_id -> trace -> prop
let no_set_state_entry_for_ p sid tr = 
  forall (ts:timestamp{ts < length tr}).
    not_a_set_state_entry_for p sid tr (get_event_at tr ts)

let no_set_state_entry_for_equi
  (p:principal) (sid:state_id) (tr:trace):
  Lemma
  ( no_set_state_entry_for p sid tr <==> 
    no_set_state_entry_for_ p sid tr
  )
  [SMTPat (no_set_state_entry_for p sid tr)]
= ()

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
let no_set_state_entry_for_prefix p sid tr1 tr2 = ()

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
