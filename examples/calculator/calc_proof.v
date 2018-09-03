From iris.base_logic.lib Require Export own saved_prop.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics.
From stdpp Require Import base pretty strings.
From distris Require Import tactics proofmode notation adequacy.
From distris.examples.library Require Import proof frac_auth.
From distris.examples.calculator Require Import calc.
From distris.examples.load_balancer Require Import definitions lb lb_proof.

(* Set Default Proof Using "Type". *)

Import Network.
Import String.
  
Lemma valid_tag_stringOfZ a :
  valid_tag a.
Proof.
Admitted.

Section calculator_server.
  Context `{dG : distG Σ}
          `{node : Network.node}
          `{P : (Z * Z) -> iProp Σ}.

  Definition Pin (msg : string) (v : Z * Z) : iProp Σ :=
    (⌜msg = StringOfZ(v.1) +:+ "_" +:+ StringOfZ(v.2)⌝)%I.

  Definition Pout (msg : string) (v : Z * Z) : iProp Σ :=
    (⌜msg = StringOfZ(v.1 + v.2)⌝)%I.
  
  Definition calculator_si := relay_resp_si P Pin Pout.

  Lemma calculator_spec (addr : socket_address) e1 A γs :
    IntoVal ⟨node;e1⟩ 〈node;#addr〉 ->
    addr ∈ A ->
    {{{ addr ⤇ calculator_si ∗ f↦ A ∗ node n↦ γs ∗
        FreePorts (ip_of_address addr) {[port_of_address addr]} }}}
      ⟨node; calculator e1⟩
    {{{ v, RET 〈node;v〉; True }}}.
  Proof.
    iIntros (<-%to_base_val'%ground_lang.of_to_val
                Haddr Φ) "(#Hsi & #Hfixed & Hn & Hip) HΦ".
    wp_lam. wp_socket h as "Hsocket". wp_let.
    wp_apply (wp_bind_socket_fix_suc with "[$Hfixed Hip $Hsocket]"); eauto.
    iDestruct 1 as (g) "(Haddr & ? & Harecs & _)". wp_seq.
    wp_apply (listen_spec (True)
                          (λ v, ⌜True⌝)%I
                          _ _ _ addr
                with "[] [-HΦ]"); last auto; last iFrame; auto.
    iLöb as "IH" forall (g). 
    iIntros (mId m φ Φ') "!# H HΦ'".
    iDestruct "H" as (Hrecmsg) "(_ & Hs & Hrec & HmId & #Hsi' & HP)".
    iDestruct (si_pred_agree _ _ _ (message_stable_from_message m)
                 with "Hsi Hsi'") as "#Heq". simpl. 
    wp_rec. iRewrite -"Heq" in "HP". wp_let.
    rewrite /calculator_si /relay_resp_si /Pin.
    iDestruct "HP" as (φ' [v1 v2]) "(#Hcsi & Hbody & HP & Hws)".
    iDestruct "Hbody" as %Hbody.
    rewrite /message_stable_from_message /= in Hbody; rewrite Hbody.
    wp_apply (tag_of_message_spec); eauto. apply valid_tag_stringOfZ.
    iIntros (v' Hv') "". subst.
    wp_op. simpl. rewrite ZOfString_inv. eauto.
    wp_apply (unSOME_spec); eauto. iIntros "_". wp_let.
    wp_apply (value_of_message_spec); eauto. apply valid_tag_stringOfZ.
    iIntros (v'' Hv'') "". subst.
    wp_op. simpl. rewrite ZOfString_inv. eauto.
    wp_apply (unSOME_spec); eauto. iIntros "_". wp_let.
    wp_op. wp_let. wp_op.
    rewrite /message_stable_from_message /=.
    wp_apply (wp_send_to_bound ⌜True⌝%I ⌜True⌝%I
                with "[$Hs HP Hws]"); eauto; iFrame; iFrame "#". iSplitR; first done.
    iIntros (M s mId') "(Hm & Hmsg & Hinfo)". iFrame. simpl.
    iApply "Hws". iFrame. done.
    iIntros "[Hsh _]". wp_seq.
    wp_apply (listen_spec (True)
                          (λ v, ⌜True⌝)%I
                          _ _ _ addr
                with "[] [-HΦ']"); last auto; last iFrame; auto.
  Qed.

End calculator_server.

Section calculator_client.
  Context `{dG : distG Σ}.

  Definition client_si a b : socket_interp Σ :=
    (λ msg, ⌜ms_body msg = StringOfZ(a + b)⌝)%I.
  
  Lemma client_spec n (a b : Z) (ip : ip_address) (server : socket_address)
        e1 e2 e3 e4 A γs :
    IntoVal ⟨n;e1⟩ 〈n;#a〉 ->
    IntoVal ⟨n;e2⟩ 〈n;#b〉 ->
    IntoVal ⟨n;e3⟩ 〈n;#ip〉 ->
    IntoVal ⟨n;e4⟩ 〈n;#server〉 ->
    server ∈ A ->
    SocketAddressInet ip 80 ∉ A ->
    {{{ server ⤇ calculator_si (P:=(λ v, True%I)) ∗ f↦ A ∗ n n↦ γs ∗ 
        FreePorts ip {[80%positive]} }}}
      ⟨n; client e1 e2 e3 e4⟩
    {{{ v, RET 〈n;#v〉; ⌜v = StringOfZ(a + b)⌝ }}}.
  Proof.
    iIntros (<-%to_base_val'%ground_lang.of_to_val
                <-%to_base_val'%ground_lang.of_to_val
                <-%to_base_val'%ground_lang.of_to_val
                <-%to_base_val'%ground_lang.of_to_val
                Haddr Hnotin Φ) "(#Hsi & #Hfixed & Hn & Hip) HΦ".
    do 4 wp_let.
    wp_socket h as "Hs". wp_let. wp_makeaddress. wp_let.
    wp_apply (wp_bind_socket_dyn_suc _ _ _ _ _ _ _ _
                (client_si a b) with "[$Hfixed Hip $Hs]"); eauto.
    iDestruct 1 as (g) "(Hs & ? & Hrecs & #Hcsi)". wp_seq.
    wp_op. wp_op. wp_op. wp_op. wp_let.
    wp_apply (wp_send_to_bound ⌜True⌝%I ⌜True⌝%I
                with "[$Hs]"); eauto; iFrame; iFrame "#". iSplitR; first done.
    iIntros (M s mId) "(Hms & _)". iFrame; iFrame "#".
    rewrite /calculator_si /relay_resp_si /message_stable_from_message /=.
    iSplitR; last done.
    iModIntro. iNext. iExists (client_si a b),(a,b). iFrame "#".
    iSplitR. by rewrite -append_assoc. iSplitR. done.
    rewrite /Pout /client_si. iIntros (m) "[% %]". done.
    iIntros "[Hs _]". wp_seq.
    wp_apply (listen_wait_spec with "[$Hs Hrecs]"); eauto.
    iIntros (m mId) "(Hrecm & Hs & Hrec & _ & HP)". simpl.
    wp_proj.
    iApply "HΦ".
    rewrite /client_si /message_stable_from_message /= //.
  Qed.
  
End calculator_client.

Section calculator_runner.
  Context `{dG : distG Σ}.

  Definition ips : gset string := {[ "0.0.0.0" ; "127.0.0.1" ; "127.0.0.2" ]}.
  Definition server := SocketAddressInet "0.0.0.0" 80.

  Lemma calculator_runner_spec A :
    server ∈ A ->
    SocketAddressInet "127.0.0.1" 80 ∉ A →
    SocketAddressInet "127.0.0.2" 80 ∉ A →
    {{{ f↦ A ∗ server ⤇ calculator_si (P:=(λ v, True%I)) ∗
        [∗ set] ip ∈ ips, FreeIP ip }}}
        calc_runner
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (? ? ? Φ) "(#Hfix & #Hsi & Hips) HΦ".
    rewrite /calc_runner.
    iDestruct (big_sepS_delete _ _ "0.0.0.0" with "Hips") as "(Hserver & Hips)";
      first set_solver.
    iDestruct (big_sepS_delete _ _ "127.0.0.1" with "Hips") as "(Hc1 & Hips)";
      first set_solver.
    iDestruct (big_sepS_delete _ _ "127.0.0.2" with "Hips") as "(Hc2 & _)";
      first set_solver.
    wp_makeaddress. wp_let. rewrite /server.
    wp_apply (wp_start with "[-]"); first auto; iFrame. simpl.
    iSplitL "Hc1 Hc2 HΦ"; last first.
    { iNext. iIntros "Hn Hip".
      iDestruct "Hn" as (γs) "Hn".
      iApply (calculator_spec with "[Hn Hip] []");
        try iFrame "#"; simpl;
          eauto; try done.  }
    iNext. wp_seq.
    wp_apply (wp_start _ "127.0.0.1" with "[-]"); first auto. iFrame.
    iSplitL "Hc2 HΦ"; last first.
    { iNext. iIntros "Hn Hip".
      iDestruct "Hn" as (γ) "Hn".
      iApply (client_spec with "[Hn Hip] []"); eauto. }
    iNext. wp_seq.
    wp_apply (wp_start with "[-]"); eauto; iFrame.
    iSplitL "HΦ". by iApply "HΦ".
    { iNext. iIntros "Hn Hip".
      iDestruct "Hn" as (γ) "Hn".
      iApply (client_spec with "[-] []"); eauto. }
  Qed.

End calculator_runner.

Definition calculator_is :=
  {|
    state_heaps := ∅;
    state_sockets := ∅;
    state_lookup := ∅;
    state_ports_in_use :=
      <["0.0.0.0" := ∅ ]> $ <["127.0.0.1" := ∅ ]> $ <["127.0.0.2" := ∅ ]> $ ∅;
    state_ms := ∅;
  |}.

Definition calc_socket_interp `{distG Σ} sa : socket_interp Σ :=
  (match sa with
  | SocketAddressInet "0.0.0.0" 80 => calculator_si (P:=(λ v, True%I))
  | _ => λ msg, ⌜True⌝
   end)%I.

Definition fixed_dom : gset socket_address := {[ server ]}.

Theorem calculator_safe : adequate NotStuck calc_runner calculator_is (λ v, True).
Proof.
  set (Σ := #[distΣ]).
  eapply (@dist_adequacy Σ _ ips fixed_dom); try done; last first.
  { intros i.
    rewrite /ips !elem_of_union !elem_of_singleton.
    intros [[]|]; subst; set_solver. }
  { rewrite /ips /= !dom_insert_L dom_empty_L right_id_L !assoc_L //. }
  iIntros (dinvG).
  iExists calc_socket_interp. iModIntro.
  iIntros "#Hfix #Hsc Hips".
  iApply (calculator_runner_spec fixed_dom with "[-] []"); eauto;
    rewrite /fixed_dom /server; try iFrame; try iFrame "#"; try set_solver.
  rewrite big_sepS_singleton. rewrite /socket_interp. iFrame "#".
Qed.

Section calc_lb_runner.
  Context `{dG : distG Σ, lG : lbG (Z * Z) Σ, N : namespace}.

  Definition calc_lb_ips : gset string :=
    {[ "0.0.0.0" ; "0.0.0.1" ; "0.0.0.2" ; "0.0.0.3" ; "127.0.0.1" ; "127.0.0.2" ]}.

  (* Definition calc_lb_ips : list string := *)
  (*   ["0.0.0.0"; "0.0.0.1" ; "0.0.0.2" ; "0.0.0.3" ; "127.0.0.1" ; "127.0.0.2"]. *)
  
  Definition calc_servers :=
    [
      SocketAddressInet "0.0.0.1" 80;
      SocketAddressInet "0.0.0.2" 80;
      SocketAddressInet "0.0.0.3" 80
    ].

  Definition lb_ports : gset port :=
    {[ 1100%positive ; 1101%positive ; 1102%positive ]}.
  
  Lemma calc_lb_runner_spec A :
    SocketAddressInet "0.0.0.0" 80 ∈ A ->
    SocketAddressInet "0.0.0.1" 80 ∈ A ->
    SocketAddressInet "0.0.0.2" 80 ∈ A ->
    SocketAddressInet "0.0.0.3" 80 ∈ A ->
    SocketAddressInet "127.0.0.1" 80 ∉ A →
    SocketAddressInet "127.0.0.2" 80 ∉ A →
    {{{ gen_heap_ctx (L:=socket_address) (V:=Z * Z) ∅ ∗ f↦ A ∗
        SocketAddressInet "0.0.0.0" 80 ⤇ calculator_si (P:=(λ v, True%I)) ∗
        ([∗ set] p ∈ lb_ports, ⌜SocketAddressInet "0.0.0.0" p ∉ A⌝) ∗
        ([∗ list] s∈calc_servers, s ⤇ calculator_si (P:=lb_server_P s)) ∗
        ([∗ set] ip ∈ calc_lb_ips, FreeIP ip)
    }}}
        calc_lb_runner
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (? ? ? ? ? ? Φ)
            "(Hw & #Hfix & #Hsi & #Hfree & #Hcalcsi & Hips) HΦ".
    rewrite /calc_lb_runner.
    do 3 (wp_makeaddress; wp_let).
    wp_apply list_make_spec; auto. iIntros (? ?). simpl. wp_let.
    wp_apply list_cons_spec; auto. iIntros (? ?). simpl. wp_let.
    wp_apply list_cons_spec; auto. iIntros (? ?). simpl. wp_let.
    wp_apply list_cons_spec; auto. iIntros (servers Hservers).
    simpl. rewrite /calc_lb_ips. simpl. wp_let.
    iDestruct (gen_heap_alloc (L:=socket_address)
                              (V:=Z * Z) _
                              (SocketAddressInet "0.0.0.1" 80)
                              (0,0)%Z with "Hw") as ">[Hw Hw1]"; eauto.
    iDestruct (gen_heap_alloc (L:=socket_address)
                              (V:=Z * Z) _
                              (SocketAddressInet "0.0.0.2" 80)
                              (0,0)%Z with "Hw") as ">[Hw Hw2]"; eauto.
    { rewrite lookup_insert_ne; eauto. }
    iDestruct (gen_heap_alloc (L:=socket_address)
                              (V:=Z * Z) _
                              (SocketAddressInet "0.0.0.3" 80)
                              (0,0)%Z with "Hw") as ">[Hw Hw3]"; eauto.
    { rewrite lookup_insert_ne; eauto.
      rewrite lookup_insert_ne; eauto. }
    iApply fupd_wp.
    iMod (inv_alloc lb_inv_w_n _
                    (∃ w, gen_heap_ctx (L:=socket_address) (V:=Z * Z) w)%I
            with "[Hw]") as "#HwI".
    { iNext. iExists _. iFrame. }
    iModIntro.
    iDestruct "Hcalcsi" as "(Hip1 & Hip2 & Hip3 & _)".
    iDestruct (big_sepS_delete _ _ "0.0.0.0" with "Hips") as "(Hlb & Hips)";
      first set_solver.
    iDestruct (big_sepS_delete _ _ "127.0.0.1" with "Hips") as "(Hc1 & Hips)";
      first set_solver.
    iDestruct (big_sepS_delete _ _ "127.0.0.2" with "Hips") as "(Hc2 & Hips)";
      first set_solver.
    iDestruct (big_sepS_delete _ _ "0.0.0.1" with "Hips") as "(Hcalc1 & Hips)";
      first set_solver.
    iDestruct (big_sepS_delete _ _ "0.0.0.2" with "Hips") as "(Hcalc2 & Hips)";
      first set_solver.
    iDestruct (big_sepS_delete _ _ "0.0.0.3" with "Hips") as "(Hcalc3 & _)";
      first set_solver.
    wp_apply (wp_start _ _ (lb_ports ∪ {[80%positive]}) with "[-]"); first auto;
      iFrame. simpl.
    iSplitR "Hw1 Hw2 Hw3"; last first.
    { iNext. iIntros "Hn Hip".
      iDestruct "Hn" as (γs) "Hn".
      iApply (lb_spec A (SocketAddressInet "0.0.0.0" 80)
                      _ _ _ "0.0.0.0" calc_servers  with "[Hn Hip Hw1 Hw2 Hw3] []");
        eauto.
      rewrite /lb_ports /calc_servers /=.
      rewrite !FreePorts_distribute; try set_solver.
      iDestruct "Hip" as "[[[Hp1100 Hp1101] Hp1102] Hp80]". iFrame; iFrame "#".
      iDestruct (big_sepS_elem_of _ _ 1100%positive with "Hfree") as "#Hf1";
        first set_solver.
      iDestruct (big_sepS_elem_of _ _ 1101%positive with "Hfree") as "#Hf2";
        first set_solver.
      iDestruct (big_sepS_elem_of _ _ 1102%positive with "Hfree") as "#Hf3";
        first set_solver. iFrame "#".
      iSplitL "Hw1". by iExists (0,0)%Z.
      iSplitL "Hw2". by iExists (0,0)%Z.
      iSplitL; last done.
      by iExists (0,0)%Z. }
    iNext. wp_seq.
    wp_apply (wp_start with "[-]"); first auto; iFrame.
    iSplitR ""; last first.
    { iNext. iIntros "Hn Hip".
      iDestruct "Hn" as (γs) "Hn".
      iApply (calculator_spec with "[Hn Hip] []");
        try iFrame "#"; simpl;
          eauto; try done.  }
    iNext. wp_seq.
    wp_apply (wp_start with "[-]"); first auto; iFrame. 
    iSplitR ""; last first.
    { iNext. iIntros "Hn Hip".
      iDestruct "Hn" as (γs) "Hn".
      iApply (calculator_spec with "[Hn Hip] []");
        try iFrame "#"; simpl;
          eauto; try done.  }
    iNext. wp_seq.
    wp_apply (wp_start with "[-]"); first auto; iFrame. 
    iSplitR ""; last first.
    { iNext. iIntros "Hn Hip".
      iDestruct "Hn" as (γs) "Hn".
      iApply (calculator_spec with "[Hn Hip] []");
        try iFrame "#"; simpl;
          eauto; try done.  }
    iNext. wp_seq. wp_makeaddress. wp_let.
    wp_apply (wp_start with "[-]"); first auto; iFrame. 
    iSplitR ""; last first.
    { iNext. iIntros "Hn Hip".
      iDestruct "Hn" as (γs) "Hn".
      iApply (client_spec with "[Hn Hip] []");
        try iFrame "#"; simpl;
          eauto; try done.  }
    iNext. wp_seq.
    wp_apply (wp_start with "[-]"); first auto; iFrame. 
    iSplitR ""; last first.
    { iNext. iIntros "Hn Hip".
      iDestruct "Hn" as (γs) "Hn".
      iApply (client_spec with "[Hn Hip] []");
        try iFrame "#"; simpl;
          eauto; try done.  }
      by iApply "HΦ".
    Unshelve. done.
  Qed.
    
End calc_lb_runner.

Definition calc_lb_is :=
  {|
    state_heaps := ∅;
    state_sockets := ∅;
    state_lookup := ∅;
    state_ports_in_use :=
      <["0.0.0.0" := ∅ ]> $
      <["0.0.0.1" := ∅ ]> $
      <["0.0.0.2" := ∅ ]> $
      <["0.0.0.3" := ∅ ]> $
      <["127.0.0.1" := ∅ ]> $
      <["127.0.0.2" := ∅ ]> $ ∅;
    state_ms := ∅;
  |}.

Definition calc_lb_socket_interp `{distG Σ, lbG (Z * Z) Σ} sa : socket_interp Σ :=
  (match sa with
  | SocketAddressInet "0.0.0.0" 80 => calculator_si (P:=(λ v, True%I))
  | SocketAddressInet "0.0.0.1" 80 =>
    calculator_si (P:=lb_server_P (SocketAddressInet "0.0.0.1" 80))
  | SocketAddressInet "0.0.0.2" 80 => 
    calculator_si (P:=lb_server_P (SocketAddressInet "0.0.0.2" 80))
  | SocketAddressInet "0.0.0.3" 80 =>
    calculator_si (P:=lb_server_P (SocketAddressInet "0.0.0.3" 80))
  | _ => λ msg, ⌜True⌝
   end)%I.

Definition calc_fixed_dom : gset socket_address :=
  {[ SocketAddressInet "0.0.0.0" 80;
     SocketAddressInet "0.0.0.1" 80;
     SocketAddressInet "0.0.0.2" 80;
     SocketAddressInet "0.0.0.3" 80 ]}.

Lemma make_lbG `{lbPreG (X:=Z * Z)} :
  (|==> ∃ _ : lbG (X:=Z * Z) (Σ:=Σ), gen_heap_ctx (L:=socket_address) ∅)%I.
Proof.
  iStartProof.
  iMod (gen_heap_init (L:=socket_address) (V:=(Z*Z)) ∅) as (γlb) "Hlb".
  iExists {|
      lb_relayG := γlb;
    |}. by iFrame.
Qed.
Theorem calc_lb_safe : adequate NotStuck calc_lb_runner calc_lb_is (λ v, True).
Proof.
  set (Σ := #[distΣ;lbΣ (X:=Z * Z)]).
  eapply (dist_adequacy (Σ:=Σ) calc_lb_ips calc_fixed_dom); eauto; last first.
  { intros i.
    rewrite /ips !elem_of_union !elem_of_singleton.
    intros [[]|]; subst; set_solver. }
  { rewrite /ips /= !dom_insert_L dom_empty_L right_id_L !assoc_L //. }
  iIntros (dinvG).
  iMod (@make_lbG Σ) as (?) "H".
  iExists calc_lb_socket_interp. iModIntro.
  iIntros "#Hfix #Hsc Hips".
  iApply (calc_lb_runner_spec (N:=nroot) calc_fixed_dom with "[-] []"); eauto;
    rewrite /calc_fixed_dom /calc_servers /lb_ports /=;
            try iFrame; try iFrame "#"; try set_solver. 
  iDestruct (big_sepS_elem_of _ _ (SocketAddressInet "0.0.0.0" 80) with "Hsc")
    as "Hp0"; first set_solver. iFrame "#".
  iDestruct (big_sepS_elem_of _ _ (SocketAddressInet "0.0.0.1" 80) with "Hsc")
    as "Hp1"; first set_solver. iFrame "#".
  iDestruct (big_sepS_elem_of _ _ (SocketAddressInet "0.0.0.2" 80) with "Hsc")
    as "Hp2"; first set_solver. iFrame "#".
  iDestruct (big_sepS_elem_of _ _ (SocketAddressInet "0.0.0.3" 80) with "Hsc")
    as "Hp3"; first set_solver. iFrame "#".
  rewrite !big_sepS_union; try set_solver. rewrite !big_sepS_singleton.
  iPureIntro. repeat split; set_solver.
Qed.
