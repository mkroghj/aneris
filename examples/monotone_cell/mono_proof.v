From iris Require Import invariants.
From iris.algebra Require Import gmap frac agree frac_auth.
From iris.base_logic Require Export gen_heap.
From iris.base_logic.lib Require Export own saved_prop.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics.
From stdpp Require Import base.
From distris Require Import tactics proofmode notation adequacy.
From distris.examples.lock_server Require Import lock_proof.
From distris.examples.monotone_cell Require Import monotone_cell.

From iris.base_logic.lib Require Import fractional.

Set Default Proof Using "Type".

Import Network.
Import String.
Import uPred.

Lemma ms_sender_message m a :
  ms_sender (message_stable_from_message m) = a -> m_sender m = a.
Proof. eauto. Qed.

Lemma ms_body_message m s :
  ms_body (message_stable_from_message m) = s -> m_body m = s.
Proof. eauto. Qed.

Inductive client_state : Type :=
| ST_LOCKING
| ST_WRITING
| ST_RELEASING.

Definition monoCmra : cmraT := prodR fracR (agreeR (leibnizC nat)).
Definition stateC := prodR fracR (agreeR (leibnizC client_state)).

Class monoG Σ := MonoG { monoG_inG :> inG Σ monoCmra;
                         stateG_inG :> inG Σ stateC;
                         mono_name : gname;
                         statec_name : gname;
                       }.
Definition monoΣ : gFunctors := #[GFunctor monoCmra; GFunctor stateC].

Instance subG_monoΣ {Σ} : subG monoΣ Σ → inG Σ monoCmra.
Proof. solve_inG. Qed.

Definition mono_server_address := SocketAddressInet "localhost" 1338.
Definition mono_si_fix : gset socket_address := {[ mono_server_address ]}.

Section mono.
  Context `{lG : lockG Σ}
          `{mG : monoG Σ}
          `{dG : distG Σ}.

  Definition makeElem (q : Qp) (m : nat) : monoCmra := (q, to_agree m).
  Definition ownMono (q : Qp) (m : nat) :=
    own (A:= monoCmra) mono_name (makeElem q m).

  Definition ownS (s : client_state) :=
    own (A:= stateC) statec_name (½, to_agree s).

  Global Instance makeElem_Exclusive m : Exclusive (makeElem 1 m).
  Proof.
    intros [y ?] [H' _]. apply (exclusive_l _ _ H').
  Qed.

  Lemma makeElem_op p q n:
    makeElem p n ⋅ makeElem q n ≡ makeElem (p + q) n.
  Proof.
    rewrite /makeElem; split; first done.
      by rewrite /= agree_idemp.
  Qed.

  Global Instance monoAsFractional q n : AsFractional (ownMono q n)
                                                      (λ q, (ownMono q n)) q.
  Proof.
    constructor; first trivial.
    intros p p'. by rewrite /ownMono -makeElem_op own_op.
  Qed.

  Lemma makeElem_eq p q n m:
    ownMono p m -∗ ownMono q n -∗ ⌜m = n⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %HValid.
    destruct HValid as [_ H2].
    iIntros "!%". by apply agree_op_invL'.
  Qed.

  Lemma makeElem_entail p q m n:
    ownMono p m -∗ ownMono q n -∗ ownMono (p + q) m.
  Proof.
    iIntros "H1 H2".
    iDestruct (makeElem_eq with "H1 H2") as %->.
    iCombine "H1" "H2" as "H".
      by rewrite makeElem_op.
  Qed.

  Lemma makeElem_update n m k:
    ownMono ½ n -∗ ownMono ½ m ==∗ ownMono 1 k.
  Proof.
    iIntros "H1 H2".
    iDestruct (makeElem_entail with "H1 H2") as "H".
    rewrite Qp_div_2.
    iApply (own_update with "H"); by apply cmra_update_exclusive.
  Qed.

  Lemma state_eq s1 s2:
    ownS s1 -∗ ownS s2 -∗ ⌜s1 = s2⌝.
  Proof.
    iIntros "H1 H2". rewrite /ownS.
    iCombine "H1" "H2" as "H".
    iDestruct (own_valid with "H") as %HValid.
    destruct HValid as [_ H2]; simpl in H2;
    iIntros "!%". by apply (agree_op_invL' (A:=leibnizC client_state)).
  Qed.

  Lemma state_update s1 s2 s3:
    ownS s1 -∗ ownS s2 ==∗ ownS s3 ∗ ownS s3.
  Proof.
    iIntros "H1 H2". rewrite /ownS.
    iDestruct (state_eq with "H1 H2") as %->.
    iCombine "H1" "H2" as "H".
    rewrite -own_op pair_op frac_op' Qp_div_2.
    iApply (own_update with "H"); apply cmra_update_exclusive.
    by rewrite agree_idemp.
  Qed.

  Definition mono_si S : socket_interp Σ :=
    (λ msg, ∃ φ, ms_sender msg ⤇ φ ∗ S ∗
    ((∃ π n, ⌜ms_body msg = "READ"⌝ ∗ ownMono π n ∗
    (∀ m, ⌜ms_body m = StringOfZ (Z.of_nat n)⌝ ∗ ownMono π n ∗ S -∗ φ m)) ∨
     ∃ n n', ⌜ms_body msg = "WRITE" +:+ "_" +:+ StringOfZ (Z.of_nat n')⌝ ∗
             ⌜n < n'⌝ ∗ ownMono ½ n ∗
           (∀ m, ⌜ms_body m = StringOfZ (Z.of_nat n')⌝ ∗ ownMono ½ n' ∗ S -∗ φ m)))%I.

  Arguments mono_si : simpl never.

  Definition handlerR n l :=
    (∃ (m : nat), l ↦[n] #m ∗ ownMono ½ m)%I.

  Lemma mono_server_s n γs A S :
    SocketAddressInet "localhost" 1338 ∈ A ->
    {{{ f↦ A ∗ mono_server_address ⤇ mono_si S ∗
        n n↦ γs ∗ FreePorts "localhost" {[1338%positive]} ∗ ownMono 1 0 }}}
      ⟨n; mono_server #()⟩
    {{{ v, RET v; ∃ v', ⌜v = 〈n;v'〉⌝ }}}.
  Proof.
    iIntros (Hin Φ) "(#Hfixed & #Hsi & Hn & Hfp & Hown) HΦ". wp_lam.
    wp_alloc l as "Hl". wp_let.
    wp_socket h as "Hs"; do 3 wp_let.
    wp_apply (wp_bind_socket_fix_suc _ _ _ _ _ {|
                            sfamily := PF_INET;
                            stype := SOCK_DGRAM;
                            sprotocol := IPPROTO_UDP;
                            saddress := None |} _ _
                with "[Hfp Hs]"); try iFrame; simpl; try done.
    iDestruct 1 as (g) "(Hsocket & Hbind & Hrecs & #Hsi')".
    wp_seq.
    wp_apply (listen_spec (handlerR n l) (λ v, ⌜True⌝)%I
                with "[] [-HΦ]"); last first; eauto.
    - iIntros (v) "_". iApply "HΦ"; eauto.
    - iFrame. iExists 0. iFrame. by iDestruct "Hown" as "[Ho1 Ho2]".
    - iLöb as "IH" forall (g).
      iIntros (mId m φ ϕ) "!# (_ & HP & Hs & Hrecs & Hm & #Hsi'' & Hsipred) HΦ'".
      iDestruct "HP" as (v) "(Hl & HownM)". rewrite /mono_server_address.
      iDestruct (si_pred_agree _ _ _ (message_stable_from_message m) with "Hsi Hsi''")
        as "#HX".
      wp_rec. simpl. iRewrite -"HX" in "Hsipred". wp_let.
      iDestruct "Hsipred" as (si) "(#Hsia & HS & [Hread | Hwrite])".
      + iDestruct "Hread" as (Hsp n0 Hmsg) "(HownM' & Hwand)"; subst.
        wp_load. wp_let. rewrite (ms_body_message _ "READ"); last auto.
        wp_op. case_bool_decide; last done. wp_if. wp_op.
        iDestruct (makeElem_eq with "HownM HownM'") as %Heq; subst.
        wp_apply (wp_send_to_bound True%I True%I
                                   _
                                   (StringOfZ (Z.of_nat n0))
                                 with "[$Hs Hwand HownM' HS]"); eauto; iFrame "#".
        { iSplitR; eauto.
          iIntros (M sent mId') "(Hms & HmId')". simpl. iFrame.
          iModIntro. iSplitL; last auto. iNext.
          iApply "Hwand". iFrame. eauto. }
        iIntros "(Hsocket & _)". wp_seq.
        wp_apply (listen_spec (handlerR n l) (λ v, ⌜True⌝)%I
                    with "[] [-HΦ']"); last first; eauto. iFrame.
        iExists n0. iFrame.
        iApply "IH". eauto.
      + iDestruct "Hwrite" as (n0 n' Hmsg Hlt) "(HownM' & Hwand)"; subst.
        wp_load. wp_let. apply ms_body_message in Hmsg. rewrite Hmsg.
        wp_op. case_bool_decide; first done. wp_if.
        wp_apply (value_of_message_spec _ #("WRITE" +:+ "_" +:+ StringOfZ n')
                                        ("WRITE" +:+ "_" +:+ StringOfZ n')
                                        "WRITE" (StringOfZ n')); try done.
        iIntros (s) "#Hstr". iSimplifyEq. wp_op. simpl. by rewrite ZOfString_inv.
        wp_apply unSOME_spec; first done. iIntros (_). wp_let.
        iDestruct (makeElem_eq with "HownM HownM'") as %Heq.
        iSimplifyEq.
        wp_lam. wp_seq. wp_op. case_bool_decide; last first.
        { destruct H0. omega. }
        wp_if. wp_seq. wp_store.
        iMod (makeElem_update _ _ n' with "HownM HownM'") as "[HownM HownM']". wp_op.
        wp_apply (wp_send_to_bound ⌜True⌝%I ⌜True⌝%I
                                   _ (StringOfZ n')
                                 with "[$Hs Hwand HownM' HS]"); eauto.
        { iFrame. iFrame "#". iSplit; first done. simpl.
          iIntros (M sent mId') "(HM & HmId' & _)". simpl. iFrame.
          iModIntro. iSplitL; last done. iNext. iApply "Hwand". iFrame. eauto. }
        iIntros "(Hsocket & _)". simpl. wp_seq.
        wp_apply (listen_spec (handlerR n l) (λ v, ⌜True⌝)%I
                    with "[] [-HΦ']"); last first; auto. iFrame.
        iExists n'. iFrame; iFrame "#".
        iApply "IH". eauto.
    - eauto.
Qed.

  Definition client_si client : socket_interp Σ :=
    (λ msg,
    (∃ n, ⌜ms_body msg = StringOfZ (Z.of_nat n)⌝ ∗ ownMono ½ n ∗ ownS ST_WRITING) ∨
    (∃ n, ⌜ms_body msg = "YES"⌝ ∗ ownS ST_LOCKING ∗ ownMono ½ n ∗
            ownLk (makeLkElem ¾ client)) ∨
    ⌜ms_body msg = "NO"⌝ ∗ ownS ST_LOCKING ∨
    ⌜ms_body msg = "RELEASED"⌝ ∗ ownS ST_LOCKING)%I.

  Lemma client_s (n : node) (ip : ip_address) port address
        (lsaddr msaddr : socket_address) A e1 e2 e3 e4 :
    SocketAddressInet ip port = address ->
    IntoVal ⟨n;e1⟩ 〈n;#ip〉 →
    IntoVal ⟨n;e2⟩ 〈n;#(Z.pos port)〉 →
    IntoVal ⟨n;e3⟩ 〈n;#lsaddr〉 →
    IntoVal ⟨n;e4⟩ 〈n;#msaddr〉 →
    address ∉ A →
    {{{ ∃ γs , f↦ A ∗ FreePorts ip {[port]} ∗ n n↦ γs ∗
        lsaddr ⤇ lock_si (∃ m, ownMono ½ m) (ownS ST_LOCKING) ∗
        msaddr ⤇ mono_si (ownS ST_WRITING) ∗ ownS ST_LOCKING ∗ ownS ST_LOCKING
    }}}
      ⟨n;client e1 e2 e3 e4⟩
      {{{ r, RET r; ⌜True⌝ }}}.
  Proof.
    iIntros (Haddress <-%to_base_val'%ground_lang.of_to_val
                     <-%to_base_val'%ground_lang.of_to_val
                     <-%to_base_val'%ground_lang.of_to_val
                     <-%to_base_val'%ground_lang.of_to_val Hnotin Φ) "H HΦ".
    iDestruct "H" as (γs) "(#Hfixed & Hip & Hn & #Hlock & #Hmono & Hst & Hst')".
    wp_lam. do 3 wp_let.
    wp_socket h as "Hsocket". wp_let.
    wp_pure (MakeAddress _ _).
    wp_apply (wp_bind_socket_dyn_suc _ _ _ _ _ {|
                            sfamily := PF_INET;
                            stype := SOCK_DGRAM;
                            sprotocol := IPPROTO_UDP;
                            saddress := None |} _ _ (client_si address)
                with "[$Hfixed Hip $Hsocket]"); simpl; eauto; try done.
    { by rewrite Haddress. }
    iIntros "H". iDestruct "H" as (g) "(Hsocket & Hbind & Hrecs & #Hsi)".
    wp_seq.
    wp_apply (wp_send_to_bound True%I True%I
              (lock_si (∃ m, ownMono ½ m) (ownS ST_LOCKING)) _ h
                with "[$Hsocket $Hlock Hst']"); eauto.
    { iSplitR; first done.
      iIntros (M sent mId) "(Hsent & HmId & _)". iFrame.
      iModIntro. simpl. iNext. iExists _. repeat (iSplitR; first done).
      iLeft. iSplitR; eauto. iNext.
      iIntros (ms) "[[% Hst'] | [% (Hres & Hl & Hst')]]";
        rewrite /client_si; iFrame; eauto. rewrite H Haddress. iRight. iLeft.
      iDestruct "Hres" as (m) "Hres".
      iExists _. by iFrame. }
    iIntros "(Hs & _)". wp_seq.
    wp_apply (listen_spec
                (ownS ST_LOCKING)%I
                (λ v, ⌜True⌝)%I
                with "[][-HΦ][HΦ]"); last first; auto.
    - iIntros (v) "_". by iApply "HΦ".
    - by iFrame.
    - iLöb as "IH" forall (g).
      iIntros (mId lockA φ ϕ)
              "!# (_ & Hst & Hs & Hrecs & Hm & #Hsi'' & Hsipred) HΦ'".
      iDestruct (si_pred_agree _ _ _ (message_stable_from_message lockA)
                   with "Hsi Hsi''") as "#Heq".
      wp_rec. wp_let. iRewrite -"Heq" in "Hsipred".
      wp_op. case_bool_decide as Hop. inversion Hop as [Hop'].
      wp_op. wp_if. rewrite /client_si.
      iDestruct "Hsipred" as "[Hres | [Hyes | [[Hmsg Hno] | [Hmsg _]]]]"; eauto.
      + iDestruct "Hres" as (n0) "[-> (Hown & Hst')]".
        iDestruct (state_eq with "Hst Hst'") as %Heq. inversion Heq.
      + iDestruct "Hyes" as (n0 Hmsg) "(Hst' & HownM & HownL)".
        iDestruct (state_update _ _ ST_WRITING with "Hst Hst'") as ">(Hst & Hst')".
        wp_apply (wp_send_to_bound ⌜True⌝%I ⌜True⌝%I
                                 (mono_si (ownS ST_WRITING)) _ h
                    with "[$Hs Hst' HownM]"); eauto.
        { iFrame. iFrame "#". iSplitR; first done.
          iIntros (M sent mId') "(Hsent & HmId & _)". iFrame. iModIntro. simpl. iNext.
          iExists (client_si address). iFrame "#".
          iLeft. iExists _,_. iFrame. iSplitR. done. iIntros (m0) "[% H]".
          iLeft. iExists n0. eauto. }
        iIntros "[Hs _]". wp_seq.
        wp_apply (listen_wait_spec with "[$Hs Hrecs Hsi]"); eauto.
        iIntros (m mId') "(_ & Hs & Hrecs & HmId' & Hφ)".
        iDestruct (si_pred_agree _ _ _ (message_stable_from_message m)
                     with "Hsi Hsi''") as "#Heq'".
        wp_let. wp_proj. iRewrite -"Heq'" in "Hφ".
        iAssert (∃ n1 : nat,
          ⌜ms_body (message_stable_from_message m) = StringOfZ n1⌝
          ∗ ownMono ½ n1 ∗ ownS ST_WRITING ∗ ownS ST_WRITING)%I
          with "[Hst Hφ]" as "Hφ".
        { iDestruct "Hφ" as "[Hok | [Hfalse | [[_ Hst'] | [_ Hst']]]]".
          - iFrame; eauto.
          - iDestruct "Hfalse" as (n1) "(_ & Hst' & _)".
            iDestruct (state_eq with "Hst Hst'") as %Heq. inversion Heq.
          - iDestruct (state_eq with "Hst Hst'") as %Heq. inversion Heq.
          - iDestruct (state_eq with "Hst Hst'") as %Heq. inversion Heq. }
        iDestruct "Hφ" as (n1) "(Hmsg & HownM & Hst & Hst')".
        iDestruct "Hmsg" as %Hmsg'%ms_body_message. rewrite Hmsg'.
        wp_op. simpl. by rewrite ZOfString_inv.
        wp_apply unSOME_spec; eauto. iIntros (_). wp_let.
        do 4 wp_op.
        wp_apply (wp_send_to_bound True%I True%I
                                 (mono_si (ownS ST_WRITING))
                                 _ h
                    with "[$Hs Hst' HownM]"); eauto; iFrame "#".
        { iSplitR. done. simpl.
          iIntros (M ms x1) "(Hms & HmId)". iFrame.
          iModIntro. iNext. iExists (client_si address).
          iFrame; iFrame "#".
          iRight. iExists n1,(n1 + 1). iFrame; eauto. iSplitR. rewrite -append_assoc.
            by rewrite Nat.add_1_r Z.add_1_r Nat2Z.inj_succ.
            iSplitR. iPureIntro. lia.
            iIntros (m') "H". iLeft. iExists (n1 + 1). eauto. }
        iIntros "[Hs _]". wp_seq.
        wp_apply (listen_wait_spec with "[$Hs Hrecs Hsi]"); eauto.
        iIntros (m' mId'') "(_ & Hs & Hrecs & HmId'' & Hφ)".
        iDestruct "Heq" as "_". iDestruct "Heq'" as "_".
        iDestruct (si_pred_agree _ _ _ (message_stable_from_message m')
                     with "Hsi Hsi''") as "#Heq".
        wp_let. iRewrite -"Heq" in "Hφ".
        iAssert (∃ n1 : nat,
          ⌜ms_body (message_stable_from_message m') = StringOfZ n1⌝
          ∗ ownMono ½ n1 ∗ ownS ST_WRITING ∗ ownS ST_WRITING)%I
          with "[Hst Hφ]" as "Hφ".
        { iDestruct "Hφ" as "[Hok | [Hfalse | [[_ Hst'] | [_ Hst']]]]".
          - iFrame; eauto.
          - iDestruct "Hfalse" as (n2) "(_ & Hst' & _)".
            iDestruct (state_eq with "Hst Hst'") as %Heq. inversion Heq.
          - iDestruct (state_eq with "Hst Hst'") as %Heq. inversion Heq.
          - iDestruct (state_eq with "Hst Hst'") as %Heq. inversion Heq. }
        iDestruct "Hφ" as (n2) "(Hmsg & HownM & Hst & Hst')".
        iDestruct (state_update _ _ ST_LOCKING with "Hst Hst'") as ">(Hst & Hst')".
        wp_apply (wp_send_to_bound ⌜True⌝%I ⌜True⌝%I
                                   (lock_si (∃ m, ownMono ½ m) (ownS ST_LOCKING))
                                   _ h
                    with "[$Hlock Hst' HownM HownL $Hs]"); eauto.
        { iSplitR. done.
          iIntros (M ms x1) "(Hms & HmId)". iFrame. simpl.
          iExists (client_si address). iFrame "#". iModIntro.
          iRight. iSplitR. done. iSplitL "HownM". eauto.
          rewrite Haddress. iFrame. iNext. iNext.
          iIntros (m0) "(Hmsg & HownL)". rewrite /client_si. eauto.  }
        iIntros "(Hs & _)". by iApply "HΦ'".
      + iDestruct "Hmsg" as %Hmsg. inversion Hmsg as [Hfalse].
          by rewrite Hop' in Hfalse.
      + iDestruct "Hmsg" as %Hmsg. inversion Hmsg as [Hfalse].
          by rewrite Hop' in Hfalse.
      + wp_op. wp_if.
        iAssert (ownS ST_LOCKING ∗ ownS ST_LOCKING)%I with "[Hsipred Hst]"
          as "(Hst & Hst')".
        { iDestruct "Hsipred" as "[Hfalse | [Hfalse | [[% Hok] | [_ Hst']]]]".
          - iDestruct "Hfalse" as (?) "(_ & _ & Hst')".
            iDestruct (state_eq with "Hst Hst'") as %Heq. inversion Heq.
          - iDestruct "Hfalse" as (n1) "(Hfalse & Hst' & _)".
            iDestruct "Hfalse" as %Hfalse. inversion Hfalse as [Hfalse'].
            destruct Hop. rewrite Hfalse'. eauto.
          - iFrame.
          - iFrame. }
        wp_apply (wp_send_to_bound True%I True%I
                                   (lock_si (∃ m, ownMono ½ m) (ownS ST_LOCKING))
                                   _ h
                with "[$Hs $Hlock Hst']"); eauto.
        { iSplitR; first done.
          iIntros (M sent mId') "(Hsent & HmId & _)". iFrame.
          iModIntro. simpl. iNext. iExists(client_si address).
          repeat (iSplitR; first done).
          iLeft. iSplitR; eauto. iNext.
          iIntros (ms) "[[% Hst'] | [% (Hres & Hl & Hst')]]";
            rewrite /client_si; iFrame; eauto. rewrite H Haddress. iRight. iLeft.
          iDestruct "Hres" as (m) "Hres".
          iExists _. by iFrame. }
        iIntros "[Hs _]". wp_seq.
        wp_apply (listen_spec
                    (ownS ST_LOCKING)%I
                    (λ v, ⌜True⌝)%I
                    with "[][-HΦ']"); eauto; last iFrame; last first.
        iApply "IH". eauto.
    - eauto.
  Qed.

End mono.