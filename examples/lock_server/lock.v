From distris Require Export lang network notation tactics.
From distris.examples.library Require Import code.

Definition lock_server : ground_lang.val :=
  (
    λ: "ip" "port",
    let: "owner" := ref NONE in 
    let: "socket" := NewSocket #Network.PF_INET
                               #Network.SOCK_DGRAM
                               #Network.IPPROTO_UDP in
    let: "handler" := rec: "handler" "msg" "sender" :=
                        (if: "msg" = #"LOCK"
                         then match: !"owner" with
                                NONE => "owner" <- SOME "sender";;
                                       SendTo "socket" #"YES" "sender"
                              | SOME "_" => SendTo "socket" #"NO" "sender"
                              end
                         else "owner" <- NONE;;
                               SendTo "socket" #"RELEASED" "sender");;
                         listen "socket" "handler" in
      let: "address" := MakeAddress "ip" "port" in
      SocketBind "socket" "address";;
      listen "socket" "handler"
  )%V.