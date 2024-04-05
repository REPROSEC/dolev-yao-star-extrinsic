module DY.Example.DH.Debug

(*
  Extract code by running:
  1. make extract_lib
  2. In the obj/ directory: OCAMLPATH=$FSTAR_HOME/lib ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib DY_Example_DH_Debug.native
  3. ./DY_Example_DH_Debug.native 
*)

open DY.Core
open DY.Lib
open DY.Example.DH.Protocol.Stateful

val discard: bool -> crypto (option unit)
let discard _ = return (Some ())

let debug () : crypto (option unit)  =
  (*** Initialize protocol run ***)
  let alice = "alice" in
  let bob = "bob" in

  let* alice_global_session_id = new_session_id alice in 
  generate_private_key alice alice_global_session_id (Sign "DH.SigningKey");*
  
  let* bob_global_session_id = new_session_id bob in
  generate_private_key bob bob_global_session_id (Sign "DH.SigningKey");*

  //install_public_key alice alice_global_session_id (Verify "DH.SigningKey") bob 

  let alice_global_session_ids: dh_global_sess_ids = {pki=alice_global_session_id; private_keys=alice_global_session_id} in
  let bob_global_session_ids: dh_global_sess_ids = {pki=bob_global_session_id; private_keys=bob_global_session_id} in

  (*** Run the protocol ***)
  // Alice
  let* alice_session_id = prepare_msg1 alice bob in
  let*? msg1_id = send_msg1 alice alice_session_id in

  // Bob
  let*? bob_session_id = prepare_msg2 alice bob msg1_id in
  let*? msg2_id = send_msg2 bob_global_session_ids bob bob_session_id in

  // Alice
  prepare_msg3 alice_global_session_ids alice bob msg2_id alice_session_id;*
  let*? msg3_id = send_msg3 alice_global_session_ids alice bob alice_session_id in

  // Bob
  verify_msg3 bob_global_session_ids alice bob msg3_id bob_session_id;*

  return (Some ())

//Run ``main ()`` when the module loads
#push-options "--warn_error -272"
let _ = debug ()
#pop-options