From iris.algebra Require Import auth agree gmap list.
From iris.base_logic Require Export gen_heap.
From iris.base_logic.lib Require Export own.
From stdpp Require Export strings decidable coPset gmap mapset pmap set.

Module Network.

  (** Basic Network *)
  Definition ip_address := string.

  (** Nodes *)
  Definition node := string.

  Definition port := positive.

  (** Socket definitions, subset of POSIX standard. *)
  Inductive address_family :=
  | PF_INET.

  (* Supported socket types. *)
  Inductive socket_type :=
  | SOCK_DGRAM.

  (* Supported protocols. *)
  Inductive protocol :=
  | IPPROTO_UDP.

  Inductive message_state :=
  | MS_FAILED | MS_SENT | MS_RECEIVED | MS_LOST.

  Inductive socket_address :=
  | SocketAddressInet (address : ip_address) (port : positive).

  Fixpoint ip_of_address (sa : socket_address) : ip_address :=
    match sa with
    | SocketAddressInet ip _ => ip
    end.
  Fixpoint port_of_address (sa : socket_address) : positive :=
    match sa with
    | SocketAddressInet _ p => p
    end.

  Record socket := Socket {
                       sfamily : address_family;
                       stype : socket_type;
                       sprotocol : protocol;
                       saddress : option socket_address
                     }.

  Definition socket_handle := positive.

  Global Instance address_family_eq_dec : EqDecision address_family.
  Proof. solve_decision. Defined.

  Global Instance socket_type_eq_dec : EqDecision socket_type.
  Proof. solve_decision. Defined.

  Global Instance protocol_eq_dec : EqDecision protocol.
  Proof. solve_decision. Defined.

  Global Instance message_state_eq_dec : EqDecision message_state.
  Proof. solve_decision. Defined.

  Global Instance socket_address_eq_dec : EqDecision socket_address.
  Proof. solve_decision. Defined.

  Global Instance socket_eq_dec : EqDecision socket.
  Proof.
    intros [[] [] [] o] [[] [] [] o'];
      destruct (decide (o = o'));
      subst; first (by left);
        by (right; intros Heq; inversion Heq; auto).
  Qed.

  Global Instance socket_address_countable : Countable socket_address.
  Proof.
    refine {| encode := λ x,
                        match x with
                          SocketAddressInet a p => encode (a, p)
                        end;
           decode := λ x, match @decode (ip_address * positive) _ _ x with
                          | None => None
                          | Some y => Some (SocketAddressInet (fst y) (snd y))
                          end
           |}.
    { intros []. by rewrite decode_encode. }
  Qed.

  Global Instance address_family_countable : Countable address_family.
  Proof.
    refine {| encode := λ x, 1%positive;
              decode := λ x, Some PF_INET
           |}.
    { by intros []. }
  Qed.

  Global Instance socket_type_countable : Countable socket_type.
  Proof.
    refine {| encode := λ x,
                        match x with
                        | SOCK_DGRAM => 1%positive
                        end;
              decode := λ x,
                        match x with
                        | _ => Some SOCK_DGRAM
                        end
           |}.
    { by intros []. }
  Qed.

  Global Instance protocol_countable : Countable protocol.
  Proof.
    refine {| encode := λ x, 1%positive;
              decode := λ x, Some IPPROTO_UDP
           |}.
    { by intros []. }
  Qed.

  (** IP/Destination Table Lookup *)
  Definition lookup_table := gmap socket_address node.

  (** Ports in use on the client **)
  Definition node_ports := gmap node coPset.

  Fixpoint node_port_not_in_use (n : node) (sa : socket_address) (ports : coPset) :=
    match sa with
    | SocketAddressInet _ p => p ∈ ports
    end.

  (** Messages *)
  Definition message_id := positive.
  Definition message_body := string.

  Record message := Message { m_from_node : node;
                              m_sender : socket_address;
                              m_destination : socket_address;
                              m_protocol : protocol;
                              m_body : message_body;
                              m_state : message_state;
                              m_sent : nat;
                              m_received : nat;
                            }.

  Definition message_soup := gmap message_id message.

  Definition messages_to_receive_at (sa : socket_address) (M : message_soup) :=
    filter (λ (elem : message_id * message), m_destination (elem.2) = sa ∧
           m_state (elem.2) = MS_SENT) M.

  Definition messages_received_at (sa : socket_address) (M : message_soup) :=
    filter (λ elem, m_destination elem.2 = sa ∧ m_state elem.2 = MS_RECEIVED) M.

  Definition messages_delivered (M : message_soup) :=
    filter (λ elem, m_state elem.2 = MS_RECEIVED) M.

  Definition max_sent (M : message_soup) := size M.

  Lemma max_sent_insert (M : message_soup) mId m :
    M !! mId = None →
    max_sent (<[mId:=m]>M) = max_sent M + 1.
  Proof.
    intros. rewrite /max_sent.
    rewrite map_size_insert; last done.
    by rewrite Nat.add_1_r.
  Qed.

  Definition max_received (M : message_soup) := size (messages_delivered M).

  (* We define an additional structure around messages that is stable over network
     traffic (IE, it does not describe it being received or lost.) This will act
     as a certificate of a message being sent. *)
  Record message_stable := MessageStable {
                               ms_from_node : node;
                               ms_sender : socket_address;
                               ms_destination : socket_address;
                               ms_protocol : protocol;
                               ms_failed : bool;
                               ms_body : message_body;
                               ms_sent : nat;
                             }.

  Definition messages_stable := gmap message_id message_stable.

  Definition message_stable_from_message (m : message) :=
    {|
      ms_from_node := m_from_node m;
      ms_sender := m_sender m;
      ms_destination := m_destination m;
      ms_protocol := m_protocol m;
      ms_failed := match m_state m with
                   | MS_FAILED => true
                   | _ => false
                   end;
      ms_body := m_body m;
      ms_sent := m_sent m;
    |}.

  Definition messages_stable_from_ms (M : message_soup) :=
    message_stable_from_message <$> M.

  Definition response_message_stable (msg : message_stable)
             from_node destination body sent :=
    {| ms_from_node := from_node;
       ms_sender := ms_destination msg;
       ms_destination := destination;
       ms_protocol := ms_protocol msg;
       ms_body := body;
       ms_failed := false;
       ms_sent := sent|}.

End Network.

