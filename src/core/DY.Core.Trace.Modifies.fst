module DY.Core.Trace.Modifies

open DY.Core.Trace.Type
open DY.Core.Trace.Base
open DY.Core.Trace.Manipulation
open DY.Core.Trace.SplitUtils
open DY.Core.Bytes.Type
open DY.Core.Label.Type

open FStar.Set

type address = principal & state_id

type modifies_set = set address

/// Set lemmas

let union_empty (#a:eqtype) (s:set a)
  : Lemma (ensures union s empty == s /\ union empty s == s)
    [SMTPatOr [
      [SMTPat (union s empty)];
      [SMTPat (union empty s)]
    ]]
  = assert(equal (union s empty) s); assert(equal (union empty s) s)

let union_add (#a:eqtype) (x:a) (s1 s2:set a)
  : Lemma (ensures add x (union s1 s2) == union (add x s1) s2)
  = assert(equal (add x (union s1 s2)) (union (add x s1) s2))

let union_assoc (#a:eqtype) (s1 s2 s3:set a)
  : Lemma (ensures (union (union s1 s2) s3) == (union s1 (union s2 s3)))
  = assert(equal (union (union s1 s2) s3) (union s1 (union s2 s3)))

/// Modifies functions

let rec trace_modifies (#label_t:Type) (tr:trace_ label_t) : modifies_set
  = match tr with
    | Nil -> Set.empty
    | Snoc hd (SetState p sid _) -> Set.add (p, sid) (trace_modifies hd)
    | Snoc hd _ -> trace_modifies hd

let rec trace_modifies_spec (#label_t:Type) (tr:trace_ label_t) (prin:principal) (sid:state_id)
  : Lemma
    (ensures (
      let mod_set = trace_modifies tr in
      if Set.mem (prin, sid) mod_set
      then exists b. state_was_set tr prin sid b
      else forall b. ~(state_was_set tr prin sid b)
    ))
  = match tr with
    | Nil -> ()
    | Snoc hd (SetState prin' sid' b) -> begin
      if prin' = prin && sid' = sid then ()
      else trace_modifies_spec hd prin sid
    end
    | Snoc hd _ -> trace_modifies_spec hd prin sid

let rec trace_modifies_concat (#label_t:Type) (tr1 tr2:trace_ label_t)
  : Lemma
    (ensures
      trace_modifies (tr1 <++> tr2) == union (trace_modifies tr1) (trace_modifies tr2)
    )
    [SMTPat (trace_modifies (tr1 <++> tr2))]
  = match tr2 with
    | Nil -> ()
    | Snoc hd (SetState prin sid _) -> begin
      trace_modifies_concat tr1 hd;
      assert(equal (trace_modifies (tr1 <++> tr2)) (union (trace_modifies tr1) (trace_modifies tr2)))
    end
    | Snoc hd _ -> trace_modifies_concat tr1 hd

let traceful_modifies (#a:Type) (f:traceful a) (tr_in:trace) : modifies_set
  = let (_, tr_out) = f tr_in in
    trace_modifies (tr_out <--> tr_in)

/// Lemmas to automate modifies analysis

let traceful_modifies_bind
  (#a #b:Type)
  (x:traceful a) (f:(a -> traceful b))
  (tr_in:trace)
  : Lemma
    (requires True)
    (ensures (
      let bind_mod = traceful_modifies (let* x in f x) tr_in in
      let x_mod = traceful_modifies x tr_in in
      let (y, tr_mid) = x tr_in in
      let f_mod = traceful_modifies (f y) tr_mid in
      bind_mod == union x_mod f_mod
    ))
  = let (y, tr_mid) = x tr_in in
    let (_, tr_out) = f y tr_mid in
//    assert(tr_in <$ tr_mid /\ tr_mid <$ tr_out);
    // Triggers trace_subtract_concat_slices
    assert(((tr_mid <--> tr_in) <++> (tr_out <--> tr_mid)) == (tr_out <--> tr_in));
//    assert(traceful_modifies x tr_in == trace_modifies (tr_mid <--> tr_in));
//    assert(traceful_modifies (f y) tr_mid == trace_modifies (tr_out <--> tr_mid));
//    assert(traceful_modifies (let* x in f x) tr_in == trace_modifies (tr_out <--> tr_in));
    ()

let traceful_modifies_return
  (#a:Type) (x:a)
  (tr:trace)
  : Lemma
    (ensures (
      traceful_modifies (return x) tr == empty
    ))
    [SMTPat (traceful_modifies (return x) tr)]
  = ()

let traceful_modifies_get_trace (tr:trace)
  : Lemma (ensures traceful_modifies get_trace tr == empty)
    [SMTPat (traceful_modifies get_trace tr)]
  = ()

let traceful_modifies_guard_tr (b:bool) (tr:trace)
  : Lemma (ensures (traceful_modifies (guard_tr b) tr) == empty)
    [SMTPat (traceful_modifies (guard_tr b) tr)]
  = ()

let traceful_modifies_add_event
  (e:trace_event)
  (tr:trace)
  : Lemma
    (ensures (
      match e with
      | SetState prin sid _ -> traceful_modifies (add_event e) tr == singleton (prin, sid)
      | _ -> traceful_modifies (add_event e) tr == empty
    ))
    [SMTPat (traceful_modifies (add_event e) tr)]
  = match e with
    | SetState prin sid _ -> begin
      assert(equal (add (prin, sid) empty) (singleton (prin, sid)))
    end
    | _ -> ()

let traceful_modifies_send_msg (b:bytes) (tr:trace)
  : Lemma (ensures traceful_modifies (send_msg b) tr == empty)
    [SMTPat (traceful_modifies (send_msg b) tr)]
  = reveal_opaque (`%send_msg) (send_msg)

let traceful_modifies_recv_msg (ts:timestamp) (tr:trace)
  : Lemma (ensures traceful_modifies (recv_msg ts) tr == empty)
    [SMTPat (traceful_modifies (recv_msg ts) tr)]
  = ()

let traceful_modifies_mk_rand (usg:usage) (lab:label) (len:nat{len <> 0}) (tr:trace)
  : Lemma (ensures (traceful_modifies (mk_rand usg lab len) tr == empty))
    [SMTPat (traceful_modifies (mk_rand usg lab len) tr)]
  = reveal_opaque (`%mk_rand) (mk_rand)

let traceful_modifies_set_state (prin:principal) (sid:state_id) (b:bytes) (tr:trace)
  : Lemma (ensures (traceful_modifies (set_state prin sid b) tr == singleton (prin, sid)))
    [SMTPat (traceful_modifies (set_state prin sid b) tr)]
   = reveal_opaque (`%set_state) (set_state)

let traceful_modifies_new_session_id (prin:principal) (tr:trace)
  : Lemma (ensures (traceful_modifies (new_session_id prin) tr) == empty)
   [SMTPat (traceful_modifies (new_session_id prin) tr)]
  = ()

let traceful_modifies_get_state (prin:principal) (sid:state_id) (tr:trace)
  : Lemma (ensures (traceful_modifies (get_state prin sid) tr) == empty)
    [SMTPat (traceful_modifies (get_state prin sid) tr)]
  = ()

let traceful_modifies_trigger_event (prin:principal) (tag:string) (b:bytes) (tr:trace)
  : Lemma (ensures (traceful_modifies (trigger_event prin tag b) tr) == empty)
    [SMTPat (traceful_modifies (trigger_event prin tag b) tr)]
  = reveal_opaque (`%trigger_event) (trigger_event)

/// The core property --- if a trace (or traceful function) does not modify a given address,
/// the result of looking up the state at the start and end of that trace (traceful) is the same.


let rec tmp (#label_t:Type) (prin:principal) (sid:state_id) (tr:trace_ label_t)
  : Lemma
    (ensures mem (prin, sid) (trace_modifies tr) <==> (exists b. state_was_set tr prin sid b))
  = match tr with
    | Nil -> ()
    | Snoc hd e -> begin
      tmp prin sid hd;
      if SetState? e && SetState?.prin e = prin && SetState?.sess_id e = sid
      then begin
        assert(state_was_set tr prin sid (SetState?.content e))
      end
      else ()
    end

let rec tmp2 (prin:principal) (sid:state_id) (tr1 tr2:trace)
  : Lemma
    (requires ~((prin, sid) `mem` (trace_modifies tr2)))
    (ensures (get_state_aux prin sid tr1) == (get_state_aux prin sid (tr1 <++> tr2)))
  = match tr2 with
    | Nil -> ()
    | Snoc hd e -> tmp2 prin sid tr1 hd

let tmp3 (prin:principal) (sid:state_id) (tr1 tr2:trace)
  : Lemma
    (requires tr1 <$ tr2 /\ ~((prin, sid) `mem` (trace_modifies (tr2 <--> tr1))))
    (ensures (get_state_aux prin sid tr1) == (get_state_aux prin sid tr2))
  = tmp2 prin sid tr1 (tr2 <--> tr1)

let tmp4 (prin:principal) (sid:state_id) (tr1 tr2:trace)
  : Lemma
    (requires ~((prin, sid) `mem` (trace_modifies tr2)))
    (ensures (
      let (st_opt1, _) = get_state prin sid tr1 in
      let (st_opt2, _) = get_state prin sid (tr1 <++> tr2) in
      st_opt1 == st_opt2
    ))
  = reveal_opaque (`%get_state) (get_state);
    tmp2 prin sid tr1 tr2

let tmp5 (prin:principal) (sid:state_id) (tr1 tr2:trace)
  : Lemma
    (requires tr1 <$ tr2 /\ ~((prin, sid) `mem` (trace_modifies (tr2 <--> tr1))))
    (ensures (
      let (st_opt1, _) = get_state prin sid tr1 in
      let (st_opt2, _) = get_state prin sid tr2 in
      st_opt1 == st_opt2
    ))
    [SMTPat (get_state prin sid tr1);
     SMTPat (get_state prin sid tr2);
     SMTPat (~((prin, sid) `mem` (trace_modifies (tr2 <--> tr1))));
    ]
  = tmp4 prin sid tr1 (tr2 <--> tr1)

let tmp6 (#a:Type) (prin:principal) (sid:state_id) (f:traceful a) (tr:trace)
  : Lemma
    (requires ~((prin, sid) `mem` (traceful_modifies f tr)))
    (ensures (
      let (st_opt1, _) = get_state prin sid tr in
      let (_, tr_out) = f tr in
      let (st_opt2, _) = get_state prin sid tr_out in
      st_opt1 == st_opt2
    ))
  = let (_, tr_out) = f tr in
    assert(~((prin, sid) `mem` (trace_modifies (tr_out <--> tr))));
    ()

val get_trace_same_trace (tr:trace)
  : Lemma
    (ensures (
      let (res, tr_out) = get_trace tr in
      tr_out == tr /\
      tr == res
    ))
    [SMTPat (get_trace tr);]
let get_trace_same_trace tr = ()

val get_state_same_trace (prin:principal) (sid:state_id) (tr:trace)
  : Lemma
    (ensures (
      let (_, tr_out) = get_state prin sid tr in
      tr_out == tr
    ))
    [SMTPat (get_state prin sid tr);]
let get_state_same_trace prin sid tr = ()

(*
let tmp7 (#a:Type) (prin:principal) (sid:state_id) (f:traceful a)
  : Pure (traceful unit)
    (requires (forall tr. ~((prin, sid) `mem` (traceful_modifies f tr))))
    (ensures fun _ -> True)
  = let* tr1 = get_trace in
    let* tr11 = get_trace in
    assert(tr1 == tr11); // This should work
    let* st_opt1 = get_state prin sid in
    let* tr2 = get_trace in
    //assert(tr11 == tr2);
    let* x = f in
    let* tr3 = get_trace in
    let* st_opt2 = get_state prin sid in
    let* tr4 = get_trace in
    assume(tr1 == tr2 /\ tr3 == tr4);
    tmp6 prin sid f tr1;
    let (st_opt1', _) = get_state prin sid tr1 in
//    assert(st_opt1 == st_opt1');
//    assert(st_opt1 == st_opt2);
    return ()
*)
