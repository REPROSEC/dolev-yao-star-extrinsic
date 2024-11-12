module DY.Lib.Communication.Core.Extension

open DY.Core

val pk_enc_extract_msg: enc_msg:bytes -> GTot (option bytes)
let pk_enc_extract_msg enc_msg =
  match enc_msg with
  | PkEnc pk nonce msg -> Some msg
  | _ -> None

val pk_enc_extract_msg_enc_lemma:
  pk_prin:bytes -> nonce:bytes ->
  msg:bytes -> enc:bytes ->
  Lemma
  (requires
    enc == pk_enc pk_prin nonce msg
  )
  (ensures
    pk_enc_extract_msg enc == Some msg
  )
let pk_enc_extract_msg_enc_lemma pk_prin nonce msg enc =
  normalize_term_spec pk_enc;
  ()

val pk_enc_extract_msg_dec_lemma:
  sk_prin:bytes ->
  enc:bytes -> msg:bytes ->
  Lemma
  (requires
    pk_dec sk_prin enc == Some msg
  )
  (ensures 
    pk_enc_extract_msg enc == Some msg
  )
let pk_enc_extract_msg_dec_lemma sk_prin enc msg = 
  normalize_term_spec pk_dec;
  ()
