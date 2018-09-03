From iris Require Import invariants.
From iris.algebra Require Import gmap frac agree frac_auth.
From iris.base_logic Require Export gen_heap.
From iris.base_logic.lib Require Export own saved_prop.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics.
From stdpp Require Import base.
From distris Require Import tactics proofmode notation adequacy.
From distris.examples.library Require Import proof frac_auth.
From distris.examples.counter_with_contributions Require Import counter.

Set Default Proof Using "Type".

Import Network.
Import String.
Import uPred.

Class ccounterG Σ := MCounterG {
  ccounter_inG :> inG Σ (frac_authR (mnatUR));
  ccounter_name : gname
}.

Definition ccounterΣ : gFunctors := #[GFunctor (frac_authR mnatUR)].

Instance subG_inG_ccounterΣ {Σ} :
  subG ccounterΣ Σ → inG Σ (frac_authR (mnatUR)) .
Proof.
  solve_inG.
Qed.

Section ccounter_server.
  Context `{cG : ccounterG Σ}
          `{dG : distG Σ}
          `{node : Network.node}.

  Definition ownC := own (A:=frac_authR mnatUR) ccounter_name.

  Definition ccounter_si : socket_interp Σ :=
    λ msg,
    match ms_body msg with
    | "INC" =>
      (∃ (n : mnat) π φ, ms_sender msg ⤇ φ ∗ ownC (◯!{π} n) ∗
         ▷ (∀ m (k : nat),
            ⌜ms_body m = StringOfZ((n + k + 1 : mnat)%nat)⌝ ∗
            ownC (◯!{π} (n + k + 1 : mnat)%nat) -∗ φ m))
      | _ => ⌜True⌝
      end%I.
  Arguments ccounter_si : simpl never.

  Definition handlerR  l :=
    (∃ (v : mnat), ownC (●! v) ∗ l ↦[node] #v)%I.

  Lemma server_s A address e1 e2 :
    IntoVal ⟨node;e1⟩ 〈node;#(ip_of_address address)〉 ->
    IntoVal ⟨node;e2⟩ 〈node;#(Z.pos (port_of_address address))〉 ->
    address ∈ A ->
    {{{ address ⤇ ccounter_si ∗
        f↦ A ∗ FreePorts (ip_of_address address) {[port_of_address address]} ∗
        ownC (●! (0 : mnat)) ∗ ∃ γs, node n↦ γs }}}
      ⟨node; ccounter_server e1 e2⟩
    {{{ v, RET 〈node;v〉; True }}}.
  Proof.
    iIntros (<-%to_base_val'%ground_lang.of_to_val
                <-%to_base_val'%ground_lang.of_to_val
                Haddress Φ) "(#Hsi & #Hfixed & Hip & Hauth & Hn) HΦ".
    iDestruct "Hn" as (γs) "Hn". do 2 wp_let.
    wp_alloc l as "Hl". wp_let.
    wp_socket h as "Hsocket". do 2 wp_let.
    wp_makeaddress. wp_let.
    wp_apply (wp_bind_socket_fix_suc with "[Hfixed $Hip $Hsocket]"); eauto;
      simpl.  destruct address; simpl; solve_into_val.
    iIntros "HX". iDestruct "HX" as (g) "(Hip & Hsocket & Hbind &  _)". wp_seq.
    wp_apply (listen_spec (handlerR l) (λ v, ⌜True⌝)%I
                with "[] [-HΦ]"); last first.
    - iApply "HΦ".
    - iFrame. iExists 0. iFrame.
    - iLöb as "IH" forall (g).
      iIntros (m n φ Φ') "!# ([% %] & HP & Hs & Hrecs & Hm & #Hsi' & Hsipred) HΦ'".
      iDestruct "HP" as (v) "(Hca & Hl)".
      iDestruct (si_pred_agree _ _ _ (message_stable_from_message n) with "Hsi Hsi'")
        as "#HX".
      wp_rec. iRewrite -"HX" in "Hsipred".
      wp_let. wp_op. case_bool_decide; wp_if; simplify_eq. 
      + rewrite {3}/ccounter_si /=. rewrite H1.
        iDestruct "Hsipred" as (v' π' φa) "(Hsia & Hc & Hvs)".
        wp_load. wp_op. wp_let. wp_store.
        iDestruct (own_valid_2 with "Hca Hc") as %Hvalid.
        apply frac_auth_mnat_valid in Hvalid. 
        iMod (frac_auth_mnat_own_update with "Hca Hc") as "[Hca Hc]". wp_op.
        wp_apply (wp_send_to_bound ⌜True⌝%I ⌜True⌝%I _ (StringOfZ (S v)) 
                    with "[$Hs Hsia Hc Hvs]"); eauto.
        { by rewrite Nat2Z.inj_succ Z.add_1_r. }
        iSplitR; auto. iFrame.
        iIntros (M sent mId) "(Hsent & HmId & _)". iFrame. iSplitL; last done.
        apply nat_le_sum in Hvalid.
        destruct Hvalid as [z Hvalid].
        iApply ("Hvs" $! _ z).
        { rewrite Hvalid Nat.add_1_r. iFrame. iPureIntro; auto. }
        iIntros "(Hs & _)"; simpl. wp_seq.
        wp_apply (listen_spec (handlerR l) (λ v, ⌜True⌝)%I with "[] [-HΦ']"); last first.
        * iApply "HΦ'".
        * iFrame. rewrite /handlerR. iExists (S v). iFrame.
          { by rewrite Nat2Z.inj_succ Z.add_1_r. }
        * iApply "IH".
        * eauto.
      + wp_seq.
        wp_apply (listen_spec (handlerR l) (λ v, ⌜True⌝)%I with "[] [-HΦ']"); last first.
        eauto using to_val_rec.
        * iFrame. iExists v. iFrame.
        * iApply "IH".
        * eauto.
    - eauto. 
  Qed.

End ccounter_server.

Section ccounter_client.
  Context `{cG : ccounterG Σ}
          `{dG : distG Σ}.

  Definition client_si π n : socket_interp Σ :=
    (λ msg, ∃ k : mnat,
      ⌜ms_body msg = StringOfZ (n + k + 1)%nat⌝ ∗
      ownC (◯!{π} (n + k + 1 : mnat)%nat))%I.

  Definition handlerR' π v ip port := SocketAddressInet ip port ⤇ client_si π v.

  Lemma client_s (n : node) A ip port π v (server : socket_address) :
    SocketAddressInet ip port ∉ A →
    {{{ ∃ γs, f↦ A ∗ server ⤇ ccounter_si ∗
        FreePorts ip {[port]} ∗ n n↦ γs ∗ ownC (◯!{π} v) }}}
      ⟨n;ccounter_client #ip #(Z.pos port) #server⟩
      {{{ r, RET 〈n;r〉; ∃ (v' : mnat) π', ⌜r = #(StringOfZ v')⌝ ∗
           ⌜v < v'⌝ ∗ ownC (◯!{π'} (v' : mnat))
      }}}.
  Proof.
    iIntros (Hfree Φ) "H HΦ".
    iDestruct "H" as (γs) "(#Hnetwork & #Hserver & Hip & Hn & Hc)".
    wp_lam. do 2 wp_let.
    wp_socket h as "Hsocket". wp_let.
    wp_makeaddress. wp_let.
    wp_apply (wp_bind_socket_dyn_suc _ _ _ _ _ {|
                            sfamily := PF_INET;
                            stype := SOCK_DGRAM;
                            sprotocol := IPPROTO_UDP;
                            saddress := None |} _ _ (client_si π v)
                with "[Hip Hsocket]"); simpl; try done. iFrame; iFrame "#".
    iIntros "H". iDestruct "H" as (g) "(Hsocket & Hbind & Hrecs & #Hsi)".
    wp_seq.
    wp_apply (wp_send_to_bound ⌜True⌝%I ⌜True⌝%I _ _ h
                with "[$Hsocket Hc]"); eauto; iFrame "#".
    { iSplitR. done.
      iIntros (M sent mId) "(Hsent & HmId & _)". iFrame. iModIntro. simpl.
      iSplitL; last done. iNext.
      rewrite /message_stable_from_message /ccounter_si /=.
      iExists v,π,(client_si π v). iSplitR; eauto.
      iFrame; iFrame "#". iNext.
      iIntros (m k) "(% & H')".
      iExists k. iFrame. eauto. }
    iIntros "(Hsocket & _)". wp_seq.
    wp_apply (listen_spec   (handlerR' π v ip port)
                            (λ r,  ∃ π (v' : mnat),
                                ⌜v < v'⌝ ∗ ⌜r = #(StringOfZ v')⌝ ∗
                                                 ownC (◯!{π} (v' : mnat)))%I
                            _ with "[] [-HΦ]"); eauto; last first.
    - iIntros (v') "H'". iApply "HΦ". iDestruct "H'" as (π' m Hlt Heq) "H'".
      iExists m. iFrame; iFrame "#". rewrite Heq. auto.
    - iFrame; iFrame "#".
    - iIntros (mId m φ Φ') "!# H'' HΦ'".
      iDestruct "H''" as "(% & Hhandler & Hsh & Hip & HmId & Hsi' & HP)".
      iDestruct (si_pred_agree _ _ _ (message_stable_from_message m)
                   with "Hsi Hsi'") as "#Hagree".
      do 2 wp_let.
      iApply ("HΦ'" with "[HP]").
      iRewrite -"Hagree" in "HP". iDestruct "HP" as (k) "(% & HP)".
      iExists π,(v + k + 1 : mnat).
      destruct m. simpl in *. rewrite H0. iFrame. iSplitR; iPureIntro; auto. lia.
    - eauto.
  Qed.

End ccounter_client.

Lemma make_ccounterG `{inG Σ (frac_authR (mnatUR))} :
  (|==> ∃ _ : ccounterG Σ, ownC (●! (0 : mnat)) ∗ ownC (◯! (0 : mnat)))%I.
Proof.
  iMod (own_alloc (●! (0 : mnat) ⋅ ◯! (0 : mnat))) as (γ) "[Hγ Hγ']"; first done.
  by iExists {|ccounter_name := γ |}; iFrame.
Qed.

Section ccounter_runner.
  Context `{dG : distG Σ, ccounterG Σ}.

  Definition ips : gset string := {[ "0.0.0.0" ; "127.0.0.1" ; "localhost" ]}.
  Definition server := SocketAddressInet "127.0.0.1" 1337.

  Lemma ccounter_runner_s A :
    server ∈ A ->
    SocketAddressInet "localhost" 1338 ∉ A →
    SocketAddressInet "0.0.0.0" 1339 ∉ A →
    {{{ ownC (●! (0 : mnat)) ∗ ownC (◯! (0 : mnat)) ∗ f↦ A ∗
        server ⤇ ccounter_si ∗ [∗ set] ip ∈ ips, FreeIP ip }}}
        ccounter_runner
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (? ? ? Φ) "(Hs & Hc & #Hfix & #Hsi & Hips) HΦ".
    rewrite /ccounter_runner.
    iDestruct (big_sepS_delete _ _ "127.0.0.1" with "Hips") as "(Hserver & Hips)";
      first set_solver.
    iDestruct (big_sepS_delete _ _ "0.0.0.0" with "Hips") as "(Hc1 & Hips)";
      first set_solver.
    iDestruct (big_sepS_delete _ _ "localhost" with "Hips") as "(Hc2 & _)";
      first set_solver.
    wp_makeaddress. wp_let. rewrite /server.
    wp_apply (wp_start with "[-]"); first auto. iFrame. simpl.
    iSplitL "Hc Hc1 Hc2 HΦ"; last first.
    { iNext. iIntros "Hn Hip".
      iApply (server_s with "[Hn Hip $Hs] []");
        try iFrame "#"; simpl;
        eauto; try done.  }
    iDestruct "Hc" as "(Hc1' & Hc2')". iNext. wp_seq.
    wp_apply (wp_start with "[-]"); first auto. iFrame.
    iSplitL "Hc1 Hc1' HΦ"; last first.
    { iNext. iIntros "Hn Hip".
      iDestruct "Hn" as (γ) "Hn".
      iApply (client_s with "[Hn Hip Hc2'] []"); eauto;
        last by iExists _; iFrame; iFrame "#". }
    iNext. wp_seq.
    wp_apply (wp_start with "[-]"); first auto. iFrame.
    iSplitL "HΦ". by iApply "HΦ".
    { iNext. iIntros "Hn Hip".
      iDestruct "Hn" as (γ) "Hn".
      iApply (client_s with "[-] []"); eauto;
      last by iExists _; iFrame; iFrame "#". }
  Qed.

End ccounter_runner.

Definition counter_is :=
  {|
    state_heaps := ∅;
    state_sockets := ∅;
    state_lookup := ∅;
    state_ports_in_use :=
      <["0.0.0.0" := ∅ ]> $ <["127.0.0.1" := ∅ ]> $ <["localhost" := ∅ ]> $ ∅;
    state_ms := ∅;
  |}.

Definition socket_interp `{distG, ccounterG Σ} sa : socket_interp Σ :=
  (match sa with
  | SocketAddressInet "127.0.0.1" 1337 => ccounter_si
  | _ => λ msg, ⌜True⌝
   end)%I.

Definition fixed_dom : gset socket_address := {[ server ]}.

Theorem ccounter_safe : adequate NotStuck ccounter_runner counter_is (λ v, True).
Proof.
  set (Σ := #[distΣ; ccounterΣ]).
  eapply (@dist_adequacy Σ _ ips fixed_dom); try done; last first.
  { intros i.
    rewrite /ips !elem_of_union !elem_of_singleton.
    intros [[]|]; subst; set_solver. }
  { rewrite /ips /= !dom_insert_L dom_empty_L right_id_L !assoc_L //. }
  iIntros (dinvG).
  iMod (@make_ccounterG Σ) as (?) "[? ?]".
  iModIntro.
  iExists socket_interp.
  iIntros "Hsi #Hsc Hips".
  iApply (@ccounter_runner_s with "[-] []"); eauto;
    rewrite /fixed_dom /server; try iFrame; try set_solver.
  rewrite big_sepS_singleton. rewrite /socket_interp. iFrame "#".
Qed.
