From iris.base_logic Require Export gen_heap fancy_updates.
From iris.base_logic.lib Require Export own saved_prop viewshifts.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import coq_tactics.
From iris.proofmode Require Export tactics.
From iris.base_logic Require Import derived. 
From distris Require Import tactics proofmode notation adequacy network.
From distris.examples.load_balancer Require Import definitions lb.
From distris.examples.library Require Import proof frac_auth.

Import Network.

Section monoids.
  Context `{X, dG : distG Σ}.
          
  Class lbG  := LbG {
    lb_relayG :> gen_heapG socket_address X Σ;
  }.                 

  Class lbPreG := LbPreG {
    lb_relayPreG :> gen_heapPreG socket_address X Σ;
  }.                 

  Definition lbΣ : gFunctors := #[gen_heapΣ socket_address X].
  
End monoids.

Global Instance subG_inG_repLogΣ {Σ} X :
  subG (lbΣ (X:=X)) Σ → lbPreG (X:=X) (Σ:=Σ).
Proof. constructor; solve_inG. Qed.

Section load_balancer.
  Context `{lG : lbG X Σ}
          `{dG : distG Σ}
          `{N : namespace}.
  
  Definition lb_inv_socket_n := N .@ "lb_socket".
  Definition lb_inv_socket n h a := (∃ s g, ⌜saddress s = Some a⌝ ∗
                                       h s↦[n] s ∗
                                       a r↦{½} g)%I.
  Definition lb_socket_I n h a := inv lb_inv_socket_n (lb_inv_socket n h a).

  Definition lb_inv_w_n := N .@ "lb_w".
  Definition lb_w_I :=
    inv lb_inv_w_n (∃ w, gen_heap_ctx (L:=socket_address) (V:=X) w)%I.
                 
  Notation "a ↦lb{ q } s" := (mapsto (L:=socket_address)
                                    (V:=X) a q s)
    (at level 20, q at level 50, format "a  ↦lb{ q }  s") : uPred_scope.
  Notation "a ↦lb s" := (mapsto (L:=socket_address)
                                    (V:=X) a 1%Qp s)
    (at level 20, format "a  ↦lb  s") : uPred_scope.

  Definition relay_resp_si P Pin Pout : socket_interp Σ :=
    (λ msg, ∃ φ (v : X), ms_sender msg ⤇ φ ∗
           Pin (ms_body msg) v ∗
           P v ∗
           (∀ m', P v ∗ Pout (ms_body m') v -∗ φ m'))%I.

  Definition lb_server_P (a : socket_address) := λ (v : X), (a ↦lb{½} v)%I.
  Definition lb_si a (Pout : message_body -> X -> iProp Σ) : socket_interp Σ :=
    (λ msg, ∃ v, a ↦lb{½} v ∗ Pout (ms_body msg) v)%I.
  
  Lemma serve_spec n e1 e2 e3 e4
        (main : socket_handle)
        (ip : ip_address)
        (port : positive)
        (server : socket_address)
        a A ma φm φs γs Pin Pout v :
    IntoVal ⟨n;e1⟩ 〈n;#(LitSocket main)〉 →
    IntoVal ⟨n;e2⟩ 〈n;#ip〉 →
    IntoVal ⟨n;e3⟩ 〈n;#(Z.pos port)〉 →
    IntoVal ⟨n;e4⟩ 〈n;#server〉 →
    a = SocketAddressInet ip port ->
    a ∉ A ->
    φm = relay_resp_si (λ v, True%I) Pin Pout ->
    φs = relay_resp_si (lb_server_P server) Pin Pout ->
    {{{ lb_w_I ∗ lb_socket_I n main ma ∗ ma ⤇ φm ∗ server ⤇ φs ∗ f↦ A ∗ n n↦ γs ∗
        server ↦lb v ∗
        FreePorts ip {[port]}}}}
      ⟨n;serve e1 e2 e3 e4⟩
    {{{ v, RET 〈n;v〉; True }}}.
  Proof.
    iIntros (<-%to_base_val'%ground_lang.of_to_val
                <-%to_base_val'%ground_lang.of_to_val
                <-%to_base_val'%ground_lang.of_to_val
                <-%to_base_val'%ground_lang.of_to_val
                Ha Hnotin Hφm Hφs Φ)
            "(#HwI & #Hinv & #Hmsi & #Hserversi & Hfixed & Hn & Hlb & Hip) HΦ".
    do 4 wp_let.
    wp_socket h as "Hs"; wp_let.
    wp_makeaddress. wp_let.
    wp_apply (wp_bind_socket_dyn_suc _ _ _ _ _ {|
                            sfamily := PF_INET;
                            stype := SOCK_DGRAM;
                            sprotocol := IPPROTO_UDP;
                            saddress := None |} _ _ (lb_si server Pout)
                with "[$Hfixed Hip Hs]"); simpl; eauto; try iFrame.
    { by rewrite Ha in Hnotin. }
    iIntros "H". iDestruct "H" as (g) "(Hsocket & Hip & Hrecs & #Hsi)".
    wp_seq. iLöb as "IH" forall (g v). wp_rec.
    wp_bind (ReceiveFrom _).
    iInv lb_inv_socket_n as ">H'" "Hclose".
    iDestruct "H'" as (s g0 ?) "[Hms Hmr]".  
    wp_apply (wp_receive_from _ _ ma _ main with "[$Hms $Hmr]"); eauto.
    iIntros (r) "HQ"; iDestruct "HQ" as (rm') "(Hs & Hrec & Hmsg)".
    iMod ("Hclose" with "[Hs Hrec]") as "_".
    { iExists _,_. iFrame. eauto. }
    iModIntro. iDestruct "Hmsg" as "[HQ | [-> ->]]"; simpl.
    - iDestruct "HQ" as (mId message φ' Hri Hm Hrecs) "(Hm & #Hmsi' & Hφmessage)".
      iDestruct (si_pred_agree _ _ _ (message_stable_from_message message)
                   with "Hmsi Hmsi'") as "#Heqv".
      iSimplifyEq. wp_match. iRewrite -"Heqv" in "Hφmessage".
      rewrite /relay_resp_si.
      iDestruct "Hφmessage" as (φ v') "(#Hsender & HPin & _ & Hwand)".
      wp_proj. wp_let. wp_proj. wp_let.
      iApply fupd_wp.
      iInv lb_inv_w_n as ">H'" "Hclose".
      iDestruct "H'" as (?) "Hw".
      iDestruct (gen_heap_update (L:=socket_address)_ _ _ v'
                   with "Hw Hlb") as ">[Hw [Hlb Hlb']]".
      iMod ("Hclose" with "[Hw]") as "_".
      { iExists _. iFrame. }
      iModIntro. wp_apply (wp_send_to_bound True%I True%I
                                 _
                                 (m_body message) h
                  with "[$Hsocket $Hserversi HPin Hlb']"); eauto. 
      { iSplitR; first done.
        iIntros (M sent mId') "(Hms & HmId' & _)". iFrame; iFrame "#".
        iSplitL; last done.
        iModIntro. iNext. simpl. 
        iExists (lb_si server Pout), v'.
        rewrite /lb_server_P. iFrame; iFrame "#".
        iIntros (m') "[Hlb' HPout]". iExists v'. iFrame. }
      iIntros "(Hs' & _)". simpl.
      wp_let. wp_bind (listen_wait _).
      wp_apply (listen_wait_spec _ h _ (SocketAddressInet ip port)
                  with "[$Hrecs $Hsi $Hs']"); eauto.
      iIntros (msg mId') "(#Hri' & Hs' & Hrecs' & HmId & Hφ2)".
      simpl. wp_proj. wp_let.
      wp_bind (SendTo _ _ _).
      iDestruct "Hφ2" as (v'') "(Hlb' & HPout)".
      iDestruct (mapsto_agree (L:=socket_address)
                              (V:=X) with "Hlb Hlb'") as %->.
      iCombine "Hlb" "Hlb'" as "Hlb".
      iInv lb_inv_socket_n as ">H'" "Hclose".
      iDestruct "H'" as (? ? ?) "[Hms Hmr]".  
      wp_apply (wp_send_to_bound ⌜True⌝%I ⌜True⌝%I
                                 φ
                                  (m_body msg)
                  with "[HPout Hwand $Hms]"); eauto.
      + iSplitR; first done. iFrame "#".
        iIntros (M sent' mId'') "(Hinfo & Ho & _)".
        iModIntro. iFrame. iSplitL; last done. iNext.
        iApply "Hwand". iFrame. 
      + iIntros "(Hs & _)". iMod ("Hclose" with "[Hs Hmr]") as "_".
        { iExists _,_. iFrame;  eauto. }
        iModIntro. wp_seq.
        iApply ("IH" with "Hn Hlb HΦ Hs' Hip Hrecs'").
    - wp_match. by iApply ("IH" with "Hn Hlb HΦ Hsocket Hip Hrecs").
  Qed.

  Definition list_sa_val (l : list socket_address) :=
  map (λ (a : socket_address), #a) l.
  
  Fixpoint makePorts (n : nat) (l : nat) : list positive :=
    match l with
      0 => []
    | S n' => (Z.to_pos n) :: makePorts (n + 1) n'
    end.

  Definition dec_handler_fold_acc (init : nat) (ip : ip_address)
             (orgList : list socket_address) (A : gset socket_address) :
    list socket_address → ground_lang.val → option socket_address → list socket_address → uPred (iResUR Σ) :=
    λ (l : list socket_address) (v : ground_lang.val)
       (sa : option socket_address) (rem : list socket_address),
    match sa with
      None =>
      (∃ p : nat, ⌜orgList = l ++ rem⌝ ∗
      ⌜p = (init + List.length l)%nat⌝ ∗
      ⌜v = #p⌝ ∗
      ([∗ list] s∈rem, ∃ v, s ↦lb v) ∗
      [∗ list] p∈(makePorts p (List.length (rem))),
         ⌜SocketAddressInet ip p ∉ A⌝ ∗ FreePorts ip {[p]}
      )%I
    | Some a =>
      (∃ p : nat, ⌜orgList = l ++ a::rem⌝ ∗
      ⌜p = (init + List.length l)%nat⌝ ∗
      ⌜v = #p⌝ ∗
      ([∗ list] s∈(a::rem), ∃ v, s ↦lb v) ∗
      [∗ list] p∈(makePorts p (List.length (a::rem))),
         ⌜SocketAddressInet ip p ∉ A⌝ ∗ FreePorts ip {[p]}
      )%I
     end.
  
  Lemma lb_spec A (a : socket_address) n e1 e2
        (ip : ip_address) servers serversV
        γs Pin Pout:
    a ∈ A ->
    a = SocketAddressInet ip 80 ->
    list_coh (list_sa_val servers) serversV ->
    IntoVal ⟨n;e1⟩ 〈n;#ip〉 →
    IntoVal ⟨n;e2⟩ 〈n;serversV〉 ->
    {{{ lb_w_I ∗ a ⤇ relay_resp_si (λ v : X, True%I) Pin Pout ∗
        ([∗ list] p∈(makePorts 1100 (List.length servers)),
           ⌜SocketAddressInet ip p ∉ A⌝) ∗
        ([∗ list] p∈(makePorts 1100 (List.length servers)), FreePorts ip {[p]}) ∗
        ([∗ list] s∈servers, ∃ v, s ↦lb v) ∗
        ([∗ list] s∈servers, s ⤇ relay_resp_si (lb_server_P s) Pin Pout) ∗ f↦ A ∗
        FreePorts ip {[(Z.to_pos 80)]} ∗
        n n↦ γs }}}
      ⟨n;load_balancer' e1 e2 ⟩
      {{{v, RET 〈n;v〉; ⌜True⌝}}}.
  Proof.
    iIntros (Hain Ha Hlist
                  <-%to_base_val'%ground_lang.of_to_val
                  <-%to_base_val'%ground_lang.of_to_val Φ) "H HΦ".
    iDestruct "H" as
        "(#HwI & #Hasi & #Hfree & Hports & Hws & #Hssi & #Hfixed & Hfp & Hn)".
    wp_rec. wp_let. 
    wp_socket h as "Hs"; wp_let.
    iDestruct "Hn" as "#Hn".
    wp_makeaddress. wp_let.
    wp_apply (wp_bind_socket_fix_suc _ _ _ _ _ {|
                            sfamily := PF_INET;
                            stype := SOCK_DGRAM;
                            sprotocol := IPPROTO_UDP;
                            saddress := None |} _ _ 
                with "[$Hfixed Hs Hfp]"); simplify_eq; simpl; eauto; try iFrame.
    iDestruct 1  as (g) "(Hsocket & Hbind & Hrecs & #Hsi)".
    (* Establish invariant with Hsocket and Hrecs *)
    iApply fupd_wp.
    iMod (inv_alloc lb_inv_socket_n _ (lb_inv_socket n h (SocketAddressInet ip 80))
            with "[Hsocket Hrecs]") as "#Hinv".
    { iNext. iExists _, g. by iFrame. }
    iModIntro. wp_seq.
    wp_apply (list_fold_spec' n _ servers 
                             #1100 serversV #1100 serversV
                             (dec_handler_fold_acc 1100 ip servers A)
                             (λ s, True)%I (λ _, True)%I
                             (λ a, #a)%I
                with "[][][Hports Hws]").
    - iIntros (a acc lacc lrem) "!# H". rewrite /dec_handler_fold_acc.
      iDestruct "H" as (p Hservers Hp Hacc) "[H1 H2]".
      iExists p. iFrame; eauto.
    - iIntros (a acc lacc lrem φ) "!# (#Hlacc & Hhandler & _) HΦ".
      iDestruct "Hlacc" as %Hlacc.
      rewrite /dec_handler_fold_acc.
      iDestruct "Hhandler" as (p Hservers Hp Hacc) "[[Hw Hws] [[% Hp] Hports]]".
      do 2 wp_let. wp_apply (wp_fork).
      iSplitL "HΦ Hports Hws". 
      + wp_seq. rewrite Hacc. wp_op. 
        iApply "HΦ". iSplitL; last done. iExists (p + 1). iFrame.
        repeat iSplitR. by rewrite -app_assoc. by rewrite app_length Hp.
        by rewrite Nat.add_1_r Z.add_1_r Nat2Z.inj_succ.
      + assert (Helemof: a ∈ servers).
        { rewrite Hservers elem_of_app. right. apply elem_of_list_here. }
        iDestruct "Hw" as (v) "Hw".        
        wp_apply (serve_spec with "[Hn $Hp $Hw]"); eauto; try iFrame "#".
        rewrite Z2Pos.id; last omega. by rewrite Hacc.
        apply elem_of_list_lookup in Helemof. destruct Helemof.
        iApply (big_sepL_lookup _ _ x with "Hssi"); eauto.
    - iSplitR; first by rewrite /list_sa_val in Hlist; last done.
      iSplitL. iExists 1100.
      rewrite big_sepL_sepL. by iFrame; iFrame "#".
      by rewrite (big_sepL_forall (λ _ _, True%I)). 
    - iIntros (v) "(Hhandler & Hports')".
        by iApply "HΦ".
  Qed.
 
End load_balancer.

