From distris Require Export lang network notation tactics.
From distris.examples.library Require Export code.

Definition ccounter_server : ground_lang.val :=
  (
    λ: "ip" "port",
    let: "counter" := ref #0 in
    let: "socket" := NewSocket #Network.PF_INET
                               #Network.SOCK_DGRAM
                               #Network.IPPROTO_UDP in
    let: "handler" := rec: "handler" "msg" "sender" :=
                        (if: "msg" = #"INC"
                         then let: "cv" := !"counter" + #1 in
                              "counter" <- "cv";;
                              SendTo "socket" (i2s "cv") "sender"
                         else #0);;
                         listen "socket" "handler" in
    let: "address" := MakeAddress "ip" "port" in
    SocketBind "socket" "address";;
    listen "socket" "handler"
  )%V.

Definition ccounter_client : ground_lang.val :=
   (
     λ: "ip" "port" "server",
        let: "socket" := NewSocket #Network.PF_INET
                                   #Network.SOCK_DGRAM
                                   #Network.IPPROTO_UDP in
        let: "address" := MakeAddress "ip" "port" in
        SocketBind "socket" "address";;
        SendTo "socket" #"INC" "server";;
        listen "socket" (λ: "msg" "addr", "msg")
   )%V.

Definition ccounter_runner :=
  ⟨"system";
   let: "saddress" := MakeAddress #"127.0.0.1" #1337 in
   Start "server" "127.0.0.1" (ccounter_server #"127.0.0.1" #1337);;
   Start "client1" "localhost" (ccounter_client #"localhost" #1338 "saddress");;
   Start "client2" "0.0.0.0" (ccounter_client #"0.0.0.0" #1339 "saddress")
  ⟩.