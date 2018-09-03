From distris Require Export lang network notation tactics.
From distris.examples.library Require Export code.

Definition serve : ground_lang.val :=
  λ: "main" "ip" "port" "server",
  let: "socket" := NewSocket #Network.PF_INET
                        #Network.SOCK_DGRAM
                        #Network.IPPROTO_UDP in
  let: "addr" := MakeAddress "ip" "port" in
  SocketBind "socket" "addr";;
  (rec: "loop" <> :=
      match: ReceiveFrom "main" with
        SOME "m" => let: "msg" := Fst "m" in
                   let: "sender" := Snd "m" in
                   let: "_" := SendTo "socket" "msg" "server" in
                   let: "res" := Fst (listen_wait "socket") in
                   SendTo "main" "res" "sender";;
                   "loop" #()
      | NONE => "loop" #()
      end) #().

Definition load_balancer : ground_lang.val :=
  λ: "ip" "port" "server1" "server2",
  let: "socket" := NewSocket #Network.PF_INET
                             #Network.SOCK_DGRAM
                             #Network.IPPROTO_UDP in
  let: "addr" := MakeAddress "ip" "port" in
  SocketBind "socket" "addr";;
  Fork (serve "socket" "ip" #1100 "server1");;
  Fork (serve "socket" "ip" #1101 "server2").


Definition load_balancer' : ground_lang.val :=
  λ: "ip" "servers",
  let: "socket" := NewSocket #Network.PF_INET
                             #Network.SOCK_DGRAM
                             #Network.IPPROTO_UDP in
  let: "addr" := MakeAddress "ip" #80 in
  SocketBind "socket" "addr";;
  list_fold (λ: "acc" "server",
             Fork (serve "socket" "ip" "acc" "server");;
             "acc" + #1) #1100 "servers".
