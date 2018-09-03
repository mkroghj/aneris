From distris Require Export lang network notation tactics.
From distris.examples.library Require Export proof code.
From distris.examples.lock_server Require Export lock.

Definition mono_server : ground_lang.val :=
  (
    λ: <>,
    let: "val" := ref #0 in 
    let: "socket" := NewSocket #Network.PF_INET
                               #Network.SOCK_DGRAM
                               #Network.IPPROTO_UDP in
    let: "handler" := rec: "handler" "msg" "sender" :=
                        let: "v" := !"val" in
                        (if: "msg" = #"READ"
                         then SendTo "socket" (i2s "v") "sender"
                         else let: "arg" := unSOME (s2i (value_of_message "msg")) in
                              assert: "v" < "arg";;
                              "val" <- "arg";;
                              SendTo "socket" (i2s "arg")%E "sender");;
                          listen "socket" "handler" in
      let: "address" := #(Network.SocketAddressInet "localhost" 1338) in
      SocketBind "socket" "address";;
      listen "socket" "handler"
  )%V.

Definition client : ground_lang.val :=
   (
     λ: "ip" "port" "lock_server" "mono_server",
        let: "socket" := NewSocket #Network.PF_INET
                                   #Network.SOCK_DGRAM
                                   #Network.IPPROTO_UDP in
        SocketBind "socket" (MakeAddress "ip" "port");;
        SendTo "socket" #"LOCK" "lock_server";;
        listen "socket" (rec: "loop" "msg" "addr" :=
           if: "msg" ≠ #"YES"
           then SendTo "socket" #"LOCK" "lock_server";;
                listen "socket" "loop"
           else SendTo "socket" #"READ" "mono_server";;
                let: "message" := (listen_wait "socket") in 
                let: "m" := unSOME (s2i (Fst "message")) in
                SendTo "socket" (#"WRITE" ^^ #"_" ^^
                                  (i2s ("m" + #1))) "mono_server";;
                let: "confirm" := listen_wait "socket" in
                SendTo "socket" #"RELEASE" "lock_server")
   )%V.
