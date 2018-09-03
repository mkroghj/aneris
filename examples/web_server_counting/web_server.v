From distris Require Export lang network notation tactics.
From distris.examples.library Require Export code.
From distris.examples.counter_with_contributions Require Export counter.

Definition serve : ground_lang.val :=
  λ: "ip" "port" "socket" "ccounter_server",
  let: "ps" := NewSocket #Network.PF_INET
                         #Network.SOCK_DGRAM
                         #Network.IPPROTO_UDP in
  let: "addr" := MakeAddress "ip" "port" in
  let: "_" := SocketBind "ps" "addr" in
  let: "handler" := rec: "handler" "msg" "sender" :=
                       (if: "msg" = #"GET"
                        then SendTo "ps" #"INC" "ccounter_server";;
                             let: "result" := Fst (listen_wait "ps") in
                             let: "out" := #"HELLO NR: " ^^ "result" in
                             SendTo "socket" "out" "sender"
                        else #0);;
                       listen "socket" "handler" in
   listen "socket" "handler".

Definition web_server : ground_lang.val :=
  λ: "ip" "ccounter_ip" "ccounter_port" "threads",
  let: "socket" := NewSocket #Network.PF_INET
                             #Network.SOCK_DGRAM
                             #Network.IPPROTO_UDP in
  let: "port" := ref #1100 in
  let: "ccaddr" := MakeAddress "ccounter_ip" "ccounter_port" in
  let: "addr" := MakeAddress "ip" #80 in
  SocketBind "socket" "addr";;
  (rec: "loop" "ts" :=
    if: #0 < "ts"
    then let: "tport" := !"port" in
         "port" <- "tport" + #1;;
         Fork (serve "ip" "tport" "socket" "ccaddr");;
         "loop" ("ts" - #1)
    else #()) "threads".

Definition web_client : ground_lang.val :=
   (
     λ: "ip" "port" "server",
        let: "socket" := NewSocket #Network.PF_INET
                                   #Network.SOCK_DGRAM
                                   #Network.IPPROTO_UDP in
        let: "address" := MakeAddress "ip" "port" in
        let: "dest" := MakeAddress "server" #80 in
        SocketBind "socket" "address";;
        SendTo "socket" #"GET" "dest";;
        Fst (listen_wait "socket")
   )%V.

Definition web_server_runner :=
  ⟨"system";
   Start "ccounter_server" "127.0.0.1" ccounter_server;;
   Start "web_server" "localhost"
         ("web_server" #"localhost" #"127.0.0.1" #1337 #10);;
   Start "client1" "0.0.0.1" (web_client #"0.0.0.1" #1338 #"localhost");;
   Start "client2" "0.0.0.0" (web_client #"0.0.0.0" #1339 #"localhost")
  ⟩.