open Str
open Printf
open BoolServRaft
open BoolServ
open Util

let serializeOutput out =
  let (cid, outStr) =
    match (Obj.magic out) with
    | NotLeader (client_id, request_id) ->
       (client_id, sprintf "NotLeader %s" (string_of_int request_id))
    | ClientResponse (client_id, request_id, o) ->
       let Response (k, value, old) = (Obj.magic o) in
       (client_id,
        match (value, old) with
        | Some v, Some o -> sprintf "Response %s %s %s %s"
                                    (string_of_int request_id)
                                    (string_of_char_list k)
                                    (string_of_char_list v)
                                    (string_of_char_list o)
        | Some v, None -> sprintf "Response %s %s %s -"
                                  (string_of_int request_id)
                                  (string_of_char_list k)
                                  (string_of_char_list v)
        | None, Some o -> sprintf "Response %s %s - %s"
                                  (string_of_int request_id)
                                  (string_of_char_list k)
                                  (string_of_char_list o)
        | None, None -> sprintf "Response %s %s - -"
                                (string_of_int request_id)
                                (string_of_char_list k))
  in (cid, Bytes.of_string outStr)

let deserializeInp i =
  let inp = String.trim (Bytes.to_string i) in
  let r = regexp "\\([0-9]+\\) \\([A-Z]+\\) +\\([/A-za-z0-9]+\\|-\\)[^/A-za-z0-9]*" in
  if string_match r inp 0 then
    (match (matched_group 1 inp, matched_group 2 inp,
            matched_group 3 inp) with
     | (i, "GET", _) -> Some (int_of_string i, Get)
     | (i, "PUT", b) -> Some (int_of_string i, Put (bool_of_string b))
     | _ -> None)
  else
    (print_endline "No match" ; None)

let deserializeInput inp client_id =
  match deserializeInp inp with
  | Some (request_id, input) ->
    Some (ClientRequest (client_id, request_id, Obj.magic input))
  | None -> None

let deserializeMsg (b : bytes) : BoolServRaft.msg = Marshal.from_bytes b 0

let serializeMsg (msg : BoolServRaft.msg) : bytes = Marshal.to_bytes msg []
