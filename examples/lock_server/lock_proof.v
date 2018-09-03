From iris Require Import invariants.
From iris.algebra Require Import gmap frac agree frac_auth.
From iris.base_logic Require Export gen_heap.
From iris.base_logic.lib Require Export own saved_prop.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics.
From stdpp Require Import base.
From distris Require Import tactics proofmode notation adequacy.
From distris.examples.library Require Import code proof.
From distris.examples.lock_server Require Import lock.
From iris.base_logic.lib Require Import fractional.

Set Default Proof Using "Type".

Import Network.
Import String.
Import uPred.

Definition lkCmra : cmraT := (prodR fracR
                                    (agreeR (leibnizC (option socket_address)))).

Class lkG Σ := LkG { LkG_inG :> inG Σ lkCmra }.
Definition lkΣ : gFunctors := #[GFunctor lkCmra ].

Instance subG_lkΣ {Σ} : subG lkΣ Σ → lkG Σ.
Proof. solve_inG. Qed.

Class lockG Σ := MLockG {
  lock_inG :> inG Σ lkCmra;
  lock_name : gname
}.

Section lock.
  Context `{lG : lockG Σ}
          `{dG : distG Σ}
          `{node : Network.node}.

  Definition ownLk :=
    own (A:= lkCmra) lock_name.

  Definition makeLkElem (q : Qp) (i : socket_address) : lkCmra :=
    (q, to_agree (Some i)).

  Definition makeLkElemNone (q : Qp) : lkCmra := (q, to_agree None).

  Definition lock_si R S : (socket_interp Σ) :=
    (λ msg, ∃ φ, ms_sender msg ⤇ φ ∗ S ∗
    (⌜ms_body msg = "LOCK"⌝ ∗ ▷ (∀ m, ⌜ms_body m = "NO"⌝ ∗ S ∨
       ⌜ms_body m = "YES"⌝ ∗ R ∗ ownLk (makeLkElem ¾ (ms_sender msg)) ∗ S -∗ φ m) ∨
    ⌜ms_body msg = "RELEASE"⌝ ∗ R ∗ ownLk (makeLkElem ¾ (ms_sender msg)) ∗ 
    ▷ (∀ m, ⌜ms_body m = "RELEASED"⌝ ∗ S -∗ φ m)))%I.

  Arguments lock_si : simpl never.

  Definition handlerR R l :=
    (∃ v, l ↦[node] v ∗
     (⌜v = NONEV⌝ ∗ R ∗ ownLk (makeLkElemNone 1) ∨
      ∃ a, ⌜v = SOMEV (LitV $ LitSocketAddress a)⌝ ∗ ownLk (makeLkElem ¼ a)))%I.

  Lemma lock_server_s R A S (address : socket_address) e1 e2 :
    IntoVal ⟨node;e1⟩ 〈node;#(ip_of_address address)〉 ->
    IntoVal ⟨node;e2⟩ 〈node;#(Z.pos (port_of_address address))〉 ->
    address ∈ A ->
    {{{ R ∗ address ⤇ lock_si R S ∗ f↦ A ∗
        FreePorts (ip_of_address address) {[port_of_address address]} ∗
        ownLk (makeLkElemNone 1) ∗ ∃ γ's, node n↦ γ's }}}
      ⟨node; lock_server e1 e2⟩
    {{{ v, RET v; ∃ v', ⌜v = 〈node;v'〉⌝ }}}.
  Proof.
    iIntros (<-%to_base_val'%ground_lang.of_to_val
                <-%to_base_val'%ground_lang.of_to_val
                Haddress Φ)
            "(HR & #Hsi & #Hnetwork & Hip & Hauth & Hn) HΦ".
    iDestruct "Hn" as (γs) "Hn". wp_let. wp_seq.
    wp_alloc l as "Hl". wp_let.
    wp_socket h as "Hsocket". do 2 wp_let.
    wp_makeaddress. wp_let. destruct address; subst.
    wp_apply (wp_bind_socket_fix_suc with "[$Hnetwork $Hip $Hsocket]");
      simpl; try done.
    iDestruct 1 as (g) "(Hsocket & Hbind & Hrecs & _)". wp_seq.
    wp_apply (listen_spec (handlerR R l) (λ v, True)%I
                with "[] [-HΦ]"); last first; auto.
    - iIntros (v) "_". iApply "HΦ"; eauto.
    - iFrame. iExists (InjLV #()). iFrame. iLeft. by iFrame.
    - iLöb as "IH" forall (g).
      iIntros (m n φ Φ') "!# ([% %] & HP & Hs & Hrecs & Hm & #Hsi' & Hsipred) HΦ'".
      iDestruct "HP" as (v) "(Hl & Hdisj)".
      iDestruct (si_pred_agree _ _ _ (message_stable_from_message n) with "Hsi Hsi'")
        as "#HX".
      wp_rec. simpl. iRewrite -"HX" in "Hsipred".
      wp_let. iDestruct "Hsipred" as (si)
           "(#Hsp & HS & [[Hbody Hwand] | (Hbody & HR & Hown & Hwand)])".
      + (* Lock request *)
        simpl. iDestruct "Hbody" as %->. simpl. wp_op.
        case_bool_decide; last done; wp_if.
        iDestruct "Hdisj" as "[[-> [HR Hown]]| H]".
        * (* Lock is free *)
          wp_load. wp_match. wp_store.
          iMod (own_update (A := lkCmra) _ _ (1%Qp, to_agree (Some _)) with "Hown")
            as "Hown".
          { by apply cmra_update_exclusive. }
          rewrite -{15}Qp_quarter_three_quarter.
          iDestruct "Hown" as "[Ho1 Ho2]".
          wp_apply (wp_send_to_bound ⌜True⌝%I ⌜True⌝%I _ "YES" h
                      with "[HR Ho2 $Hs HS Hwand]"); eauto; iFrame "#".
          iSplit; trivial.
          -- simpl. iIntros (M sent mId) "[Hsent Hstable]".
             iFrame. iModIntro. iSplit; trivial. iNext.
             iApply ("Hwand" $! _). simpl. iRight. iFrame; eauto.
          -- iIntros "[Hs _]". simpl. wp_seq.
             wp_apply (listen_spec (handlerR R l) (λ v, ⌜True⌝)%I
                         with "[] [-HΦ']"); eauto using to_val_rec; last first.
             { iFrame. iExists _. iFrame. iRight. eauto. }
             { iApply "IH". }
             eauto.
        * (* Lock already taken *)
          iDestruct "H" as (a') "[#Hv Hown]".
          iSimplifyEq. wp_load. wp_match.
          wp_apply (wp_send_to_bound ⌜True⌝%I ⌜True⌝%I _ "NO" h
                      with "[$Hs Hwand HS]"); eauto; iFrame "#". iSplit; trivial.
          -- simpl. iIntros (M sent mId) "[Hsent Hstable]".
             iFrame. iModIntro. iSplit; trivial. iNext.
             iApply ("Hwand" $! _). iLeft. by iFrame.
          -- iIntros "[Hs _]". simpl. wp_seq.
             wp_apply (listen_spec (handlerR R l) (λ v, ⌜True⌝)%I
                         with "[] [-HΦ']"); eauto using to_val_rec; last first.
             iFrame. iExists _. iFrame. iRight. eauto.
             iApply "IH". eauto.
      + simpl. iDestruct "Hbody" as %->. simpl.
        wp_op. case_bool_decide; first done. wp_if.
        iDestruct "Hdisj" as "[[-> [HR' Hown']] | H]".
        { iDestruct (own_valid_2 with "Hown Hown'") as %Hvalid.
          rewrite /makeLkElem /makeLkElemNone pair_op in Hvalid.
          destruct Hvalid as [? _]. simpl in H2. done. }
        iDestruct "H" as (a') "[#Hv Hown']". iSimplifyEq.
        iDestruct (own_valid_2 with "Hown Hown'") as
              %[_ Ho2%(agree_op_invL' (A := leibnizC (option _)))]. simplify_eq.
        iCombine "Hown'" "Hown" as "Hown". rewrite frac_op' Qp_quarter_three_quarter.
        iMod (own_update (A := lkCmra) _ _ (1%Qp, to_agree None) with "Hown")
            as "Hown".
        { by apply cmra_update_exclusive. }
        wp_store.
        wp_apply (wp_send_to_bound ⌜True⌝%I ⌜True⌝%I  _ "RELEASED" h
                    with "[HS $Hs Hwand]"); eauto; iFrame "#"; iFrame.
        iSplit; trivial.
        { simpl. iIntros (M sent mId) "[Hsent Hstable]".
          iFrame. iModIntro. iSplit; trivial. iNext.
            iApply "Hwand". by iFrame. }
        iIntros "[Hs _]".  wp_seq.
        wp_apply (listen_spec (handlerR R l) (λ v, True)%I
                    with "[] [-HΦ']"); eauto using to_val_rec; last first.
        * iFrame. iExists _. iFrame. iLeft. by iFrame.
        * iApply "IH".
        * eauto.
    -  eauto.
  Qed.

End lock.