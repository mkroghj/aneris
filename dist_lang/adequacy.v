From iris.program_logic Require Export weakestpre adequacy.
From iris.algebra Require Import auth gmap frac agree coPset gset frac_auth.
From iris.base_logic Require Export own gen_heap.
From iris.base_logic.lib Require Import fractional viewshifts saved_prop.
From iris.proofmode Require Import tactics.
From distris Require Export tactics lifting network notation.
Set Default Proof Using "Type".

Import Network.

Class distPreG Σ := DistPreG {
  distPre_invG :> invPreG Σ;
  distPre_mapG :> inG Σ (authR system_state_mapUR);
  distPre_heapG :> gen_heapPreG loc ground_lang.val Σ;
  (* network *)
  distPre_lookupG :> gen_heapPreG socket_address node Σ;
  distPre_socketG :> gen_heapPreG socket_handle socket Σ;
  distPre_messagesG :> gen_heapPreG message_id message Σ;
  distPre_messagesSentG :> gen_heapPreG message_id message_stable Σ;
  distPre_messagesReceivedG :> gen_heapPreG socket_address message_soup Σ;
  distPre_freeipsG :> inG Σ (authUR (gset_disjUR ip_address));
  distPre_freeportsG :> inG Σ (authUR (gmapUR ip_address (gset_disjUR port)));
  distPre_siG :> inG Σ socket_interpR;
  distPre_fixedG :> inG Σ (agreeR (gsetUR socket_address));
  distPre_savedPredG :> savedPredG Σ message_stable
}.

Definition distΣ : gFunctors :=
  #[invΣ; gen_heapΣ loc ground_lang.val;
      GFunctor (authR system_state_mapUR);
      gen_heapΣ socket_address node;
      gen_heapΣ socket_handle socket;
      gen_heapΣ message_id message;
      gen_heapΣ message_id message_stable;
      gen_heapΣ socket_address message_soup;
      GFunctor (authUR (gset_disjUR ip_address));
      GFunctor (authUR (gmapUR ip_address (gset_disjUR port)));
      GFunctor socket_interpR;
      GFunctor (agreeR (gsetUR socket_address));
      savedPredΣ message_stable
   ].

Global Instance subG_heapPreG {Σ} : subG distΣ Σ → distPreG Σ.
Proof. constructor; solve_inG. Qed.

Definition gen_heap_frag `{g : gen_heapG L V Σ} σ :=
  own (gen_heap_name g) (◯ to_gen_heap σ).

Lemma gen_heap_init_frag `{gen_heapPreG L V Σ} σ :
  (|==> ∃ g : gen_heapG L V Σ, gen_heap_ctx σ ∗ gen_heap_frag σ)%I.
Proof.
  iMod (own_alloc (● to_gen_heap σ ⋅ ◯ to_gen_heap σ)) as (γ) "H".
  { apply auth_valid_discrete_2. split; auto. exact: to_gen_heap_valid. }
  iDestruct "H" as "[H1 H2]".
  iModIntro. iExists (GenHeapG L V Σ _ _ _ γ). simpl. iFrame.
Qed.

Lemma gen_heap_frag_set `{hG : gen_heapG L V Σ} σ :
  (gen_heap_frag σ -∗ [∗ map] l ↦ v ∈ σ, mapsto l 1 v)%I.
Proof.
  rewrite mapsto_eq /=.
  unfold big_opM.
  assert (∃ h, h ≡ₚ map_to_list σ).
  { by exists (map_to_list σ). }
  destruct H0. revert x σ H0.
  induction x as [|[l v] x'] => σ Heqh; simpl.
  - rewrite -Heqh. by iIntros.
  - iIntros "Hσ".
    assert (Hin : σ !! l = Some v).
    { rewrite -elem_of_map_to_list -Heqh. apply elem_of_list_here. }
    iAssert ((own (gen_heap_name hG) (◯ {[l := (1%Qp, to_agree v)]}) ∗
              own (gen_heap_name hG) (◯ to_gen_heap (delete l σ)))%I)
      with "[Hσ]" as "[Hf Hσ]".
    { rewrite -own_op -auth_frag_op -insert_singleton_op.
        by rewrite -to_gen_heap_insert insert_delete insert_id.
        by rewrite to_gen_heap_delete lookup_delete.
    }
    rewrite -Heqh big_sepL_cons.
    rewrite -(insert_id σ l v) in Heqh; last auto. revert Heqh.
    rewrite -insert_delete map_to_list_insert. intros Heq.
    apply Permutation.Permutation_cons_inv in Heq. rewrite Heq.
    iFrame. iApply (IHx' (delete l σ)); auto.
    apply lookup_delete.
Qed.

Theorem dist_adequacy `{distPreG Σ}
           (IPs : gset ip_address) (A : gset socket_address)
           s e σ φ :
  (∀ `{distG Σ}, (|={⊤}=> ∃ (f : socket_address → socket_interp Σ),
                    f↦ A -∗ ([∗ set] a ∈ A, a ⤇ (f a)) -∗
                     ([∗ set] ip ∈ IPs, FreeIP ip) -∗ WP e @ s; ⊤ {{v, ⌜φ v⌝ }})%I) →
  dom (gset ip_address) (state_ports_in_use σ) = IPs →
  (∀ i, i ∈ IPs → state_ports_in_use σ !! i = Some ∅) →
  state_heaps σ = ∅ →
  state_sockets σ = ∅ →
  state_lookup σ = ∅ →
  state_ms σ = ∅ →
  @adequate dist_lang s e σ φ.
Proof.
  intros Hwp Hipdom Hpiiu Hste Hsce Hlue Hmse;
    eapply (wp_adequacy _ _); iIntros (?); simpl.
  iMod (own_alloc (● (to_agree <$> ∅) : authR system_state_mapUR)) as
      (γmp) "Hmp"; first by rewrite fmap_empty.
  iMod (gen_heap_init (state_lookup σ : gmap socket_address node)) as (γl) "Hl".
  iMod (gen_heap_init (state_ms σ : gmap message_id message)) as (γm) "Hm".
  iMod (gen_heap_init (∅ : gmap message_id message_stable)) as (γms) "Hms".
  iMod (gen_heap_init (∅ : gmap socket_address message_soup)) as (γr) "Hr".
  iMod (own_alloc (● ∅ ⋅ ◯ ∅: socket_interpR)) as (γsi) "[Hsi Hsi']".
  { split; last done; simpl. intros. by rewrite left_id. }
  iMod (own_alloc (to_agree A : agreeR (gsetUR socket_address)))
    as (γsif) "#Hsif"; first done.
  iMod (FreeIps_alloc IPs) as (γips) "[HIPsCtx HIPs]".
  iMod (own_alloc (● (∅: gmap ip_address (gset_disjUR port)))) as (γpiu) "HPiu";
    first done.
  set (dg :=
         {|
           dist_map_name := γmp;
           dist_si_name := γsi;
           dist_fixed_name := γsif;
           dist_freeips_name := γips;
           dist_freeports_name := γpiu;
         |}).
  iMod (Hwp dg) as (f) "Hwp".
  iAssert (|==>
             ∃ M : gmap socket_address gname,
               (⌜elements (dom (gset socket_address) M) ≡ₚ elements A⌝)
                 ∗ own (A:=socket_interpR) γsi (● (to_agree <$> M)) ∗
                 [∗ map] a ↦ γ ∈ M,
             own (A:=socket_interpR)
                 γsi (◯ {[ a := (to_agree γ) ]}) ∗
                 saved_pred_own (A:=message_stable) γ (f a))%I with
      "[Hsi Hsi']" as "Hsid".
  { pose proof (NoDup_elements A) as Hnd.
    iInduction (elements A) as [|a l] "IHl" forall "Hsi Hsi'".
    - iModIntro. iExists ∅.
      rewrite big_sepM_empty fmap_empty; iFrame.
      iPureIntro. by rewrite dom_empty_L.
    - inversion Hnd as [|? ? ? Hrd']; subst.
      iMod ("IHl" $! Hrd' with "Hsi Hsi'") as (M HMl) "[HM HML]"; iFrame.
      iMod (saved_pred_alloc (f a)) as (γ) "Hγ".
      assert (a ∉ dom (gset _) M) as Hnm.
      { by rewrite -elem_of_elements HMl. }
      iMod (own_update (A:=socket_interpR) _ (● (to_agree <$> M))
                       (● (<[a := to_agree γ ]>(to_agree <$> M) :
                             gmapUR socket_address (agreeR (leibnizC gname)))
                          ⋅ (◯ ({[a := to_agree γ]} :
                                  gmapUR socket_address (agreeR (leibnizC gname)
                       )))) with "HM") as "[HM Hγ']".
      { apply auth_update_alloc. rewrite -insert_empty.
        rewrite /ε /= /gmap_unit.
        apply (alloc_local_update
                 (to_agree <$> M : gmapUR
                                     socket_address (agreeR (leibnizC gname)))
                 ∅ a (@to_agree (leibnizC gname) γ)); last done.
        eapply (not_elem_of_dom (D := gset socket_address)).
        by rewrite dom_fmap. }
      iModIntro.
      iExists (<[a:= γ]> M).
      rewrite fmap_insert; iFrame.
      rewrite big_sepM_insert;
        last by apply (not_elem_of_dom (D := gset socket_address)).
      iFrame. iPureIntro.
      rewrite dom_insert_L elements_union_singleton; auto. }
  iMod "Hsid" as (M HMfs) "[HM #Hsa]".
  assert (dom (gset _) M = A) as Hdmsi.
  { apply elem_of_equiv_L => x; split => Hx;
    apply elem_of_elements; apply elem_of_elements in Hx;
    first by rewrite -HMfs. by rewrite HMfs. }
  iModIntro.
  iAssert ([∗ set] s ∈ A, s ⤇ f s)%I as "#Hsa'".
  { rewrite -Hdmsi -!big_sepM_dom.
    iApply (@big_sepM_mono with "[$Hsa]"); simpl; auto.
    iIntros (? ? Hx) "[? ?]"; iExists _; iFrame. }
  iExists state_interp; simpl.
  iSplitR "Hwp HIPs"; last first.
  - iApply "Hwp"; iFrame "#"; iFrame.
  - iFrame.
    iExists _; iFrame.
    iSplit.
    { iPureIntro. by split; rewrite ?Hste ?Hsce !dom_empty_L. }
    iSplit.
    { iPureIntro. rewrite /network_coherence Hlue; intros ??;
      rewrite lookup_empty. by intros [? ?]. }
    iSplitL "HM".
    { rewrite /socket_interp_coherence. iExists _; iFrame.
      iExists _; iFrame.
      rewrite Hlue -!Hdmsi dom_empty_L right_id_L dom_fmap_L.
      iSplit; first done.
      rewrite Hdmsi; iFrame "#".
      iApply (@big_sepS_mono with "[$Hsa']"); simpl; auto. }
    iSplitR.
    { by rewrite big_sepM_empty. }
    iSplitL "HIPsCtx HPiu".
    { iExists _, _; iFrame.
      iPureIntro; repeat split; trivial.
      - by rewrite dom_empty.
      - intros ? ?; by rewrite lookup_empty. }
      iExists _, _; iFrame.
      rewrite Hmse Hlue !big_sepM_empty; repeat iSplit; trivial; iPureIntro.
     * rewrite /messages_socket_coherence.
       by rewrite !dom_empty_L.
     * by rewrite !dom_empty_L.
Qed.

Definition safe e σ := @adequate dist_lang NotStuck e σ (λ _, True).

Theorem adequacy `{distPreG Σ}
        (IPs : gset ip_address) (A : gset socket_address)
        e σ :
  (∀ `{distG Σ}, (|={⊤}=> ∃ (f : socket_address → socket_interp Σ),
                    f↦ A -∗ ([∗ set] a ∈ A, a ⤇ (f a)) -∗
                     ([∗ set] ip ∈ IPs, FreeIP ip) -∗ WP e {{v, True }})%I) →
  dom (gset ip_address) (state_ports_in_use σ) = IPs →
  (∀ i, i ∈ IPs → state_ports_in_use σ !! i = Some ∅) →
  state_heaps σ = ∅ → state_sockets σ = ∅ → state_lookup σ = ∅ → state_ms σ = ∅ →
  safe e σ.
Proof.
  intros.
  eapply dist_adequacy; eauto.
Qed.