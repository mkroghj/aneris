From distris Require Export lang network notation tactics.
From distris.examples.library Require Export code.

Definition tpc_participant_setup : ground_lang.val :=
  λ: "socket" "req_handler" "fin_handler",
  (rec: "loop" <> :=
        let: "msg" := listen_wait "socket" in
        let: "sender" := Snd "msg" in
        let: "_" := SendTo "socket" ("req_handler" (Fst "msg") "sender") "sender" in
        let: "result" := listen_wait "socket" in
        let: "res_sender" := Snd "result" in
        "fin_handler" (Fst "result") "res_sender";;
        SendTo "socket" #"ACK" "res_sender";;
        "loop" #()
  ) #().

Definition tpc_coordinate : ground_lang.val :=
  λ: "msg" "socket" "nodes" "dec_handler",
  let: "count" := list_length "nodes" in
  let: "msgs" := ref (list_make #()) in
  let: "ack" := ref #0 in
  list_iter (λ: "n", SendTo "socket" "msg" "n") "nodes";;
  listen "socket" (
    rec: "handler" "msg" "sender" :=
      let: "msgs'" := !"msgs" in
      "msgs" <- list_cons "msg" "msgs'";;
      if: list_length !"msgs" = "count"
      then #() else listen "socket" "handler");;
  let: "result" := "dec_handler" ! "msgs" in
  list_iter (λ: "n", SendTo "socket" "result" "n") "nodes";;
  listen "socket" (
    rec: "handler" "msg" "sender" :=
      "ack" <- !"ack" + #1;;
      if: !"ack" = "count"
      then "result" else listen "socket" "handler").