From distris Require Export lang network notation tactics.
From distris.examples.library Require Export code.
From distris.examples.load_balancer Require Export lb.

Definition calculator : ground_lang.val :=
  λ: "addr",
  let: "socket" := NewSocket #Network.PF_INET
                        #Network.SOCK_DGRAM
                        #Network.IPPROTO_UDP in
  SocketBind "socket" "addr";;
  listen "socket" (rec: "loop" "msg" "sender" :=
                     let: "arg1" := unSOME (s2i (tag_of_message "msg")) in
                     let: "arg2" := unSOME (s2i (value_of_message "msg")) in
                     let: "res" := "arg1" + "arg2" in
                     SendTo "socket" (i2s "res") "sender";;
                     listen "socket" "loop").

Definition client : ground_lang.val :=
  λ: "arg1" "arg2" "ip" "server",
  let: "socket" := NewSocket #Network.PF_INET
                        #Network.SOCK_DGRAM
                        #Network.IPPROTO_UDP in
  let: "addr" := MakeAddress "ip" #80 in
  SocketBind "socket" "addr";;
  let: "msg" := (i2s "arg1") ^^ #"_" ^^ (i2s "arg2") in
  SendTo "socket" "msg" "server";;
  Fst (listen_wait "socket").

Definition calc_runner :=
  ⟨"system";
   let: "saddr" := MakeAddress #"0.0.0.0" #80 in
   Start "server" "0.0.0.0" (calculator "saddr");;
   Start "client1" "127.0.0.1" (client #10 #20 #"127.0.0.1" "saddr");;
   Start "client2" "127.0.0.2" (client #42 #4 #"127.0.0.2" "saddr")
  ⟩.

Definition calc_lb_runner :=
  ⟨"system";
   let: "server1" := MakeAddress #"0.0.0.1" #80 in
   let: "server2" := MakeAddress #"0.0.0.2" #80 in
   let: "server3" := MakeAddress #"0.0.0.3" #80 in
   let: "servers":= list_make #() in
   let: "servers" := list_cons "server3" "servers" in
   let: "servers" := list_cons "server2" "servers" in
   let: "servers" := list_cons "server1" "servers" in
   Start "lb" "0.0.0.0" (load_balancer' #"0.0.0.0" "servers");;
   Start "server1" "0.0.0.1" (calculator "server1");;
   Start "server2" "0.0.0.2" (calculator "server2");;
   Start "server3" "0.0.0.3" (calculator "server3");;
   let: "lb" := MakeAddress #"0.0.0.0" #80 in
   Start "client1" "127.0.0.1" (client #10 #20 #"127.0.0.1" "lb");;
   Start "client2" "127.0.0.2" (client #42 #4 #"127.0.0.2" "lb")
  ⟩.