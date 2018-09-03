From iris.algebra Require Import auth gmap frac agree coPset gset frac_auth.
From iris.base_logic Require Export own gen_heap.
From iris.base_logic.lib Require Import fractional viewshifts saved_prop.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From iris.proofmode Require Import tactics.
From distris Require Export helpers lang notation tactics network.
From stdpp Require Import fin_maps.
Set Default Proof Using "Type".

Import uPred.
Import Network.

Definition node_gnames : Type := (gname * gname).
Definition π_heap (x : node_gnames) := x.1.
Definition π_socket (x : node_gnames) := x.2.
Definition node_gnamesC := leibnizC node_gnames.
Definition socket_received := gmap socket_address message_soup.

Definition system_state_mapUR : ucmraT := gmapUR node (agreeR node_gnamesC).
Definition socket_interpR : cmraT := authR (gmapUR socket_address
                                                   (agreeR (leibnizC gname))).

Instance system_state_mapUR_unit : Unit (gmap node (agree node_gnames)) :=
  (∅ : gmap node (agree node_gnames)).
Global Instance system_state_core_id (x : system_state_mapUR) : CoreId x.
Proof.
  apply gmap_core_id.
  apply agree_core_id.
Qed.

Definition socket_interp Σ := message_stable -c> iProp Σ.

(** The system CMRA we need. *)
Class distG Σ := DistG {
  dist_invG :> invG Σ;
  dist_mapG :> inG Σ (authR system_state_mapUR);
  dist_map_name : gname;
  dist_heapG :> gen_heapPreG loc ground_lang.val Σ;
  (* network *)
  dist_lookupG :> gen_heapG socket_address node Σ;
  dist_socketG :> gen_heapPreG socket_handle socket Σ;
  dist_messagesG :> gen_heapG message_id message Σ;
  dist_messagesSentG :> gen_heapG message_id message_stable Σ;
  dist_messagesReceivedG :> gen_heapG socket_address message_soup Σ;
  dist_freeipsG :> inG Σ (authUR (gset_disjUR ip_address));
  dist_freeips_name : gname;
  dist_freeportsG :> inG Σ (authUR (gmapUR ip_address (gset_disjUR port)));
  dist_freeports_name : gname;
  dist_siG :> inG Σ socket_interpR;
  dist_si_name : gname;
  dist_fixedG :> inG Σ (agreeR (gsetUR socket_address));
  dist_fixed_name : gname;
  dist_savedPredG :> savedPredG Σ message_stable
}.

Definition gen_heap_loc_instance γ `{distG Σ} :=
  GenHeapG loc ground_lang.val _ _ _ _ γ.

Definition gen_heap_soc_instance γ `{distG Σ} :=
  GenHeapG socket_handle socket _ _ _ _ γ.

Section Definitions.
  Context `{dG : distG Σ}.

  Definition mapsto_node_def (n : node) (x : node_gnames) :=
    own (dist_map_name) (◯ {[ n := to_agree x ]} : auth system_state_mapUR).
  Definition mapsto_node_aux : seal (@mapsto_node_def). by eexists. Qed.
  Definition mapsto_node := unseal mapsto_node_aux.
  Definition mapsto_node_eq : @mapsto_node = @mapsto_node_def :=
    seal_eq mapsto_node_aux.

  Global Instance mapsto_node_persistent n x : Persistent (mapsto_node n x).
  Proof. rewrite mapsto_node_eq /mapsto_node_def. apply _. Qed.

  Definition mapsto_l n l q v :=
    (∃ γ's, mapsto_node n γ's ∗
            mapsto (hG := gen_heap_loc_instance (π_heap γ's)) l q v)%I.
  Definition mapsto_s n h q s :=
    (∃ γ's, mapsto_node n γ's ∗
            mapsto (hG := gen_heap_soc_instance (π_socket γ's)) h q s)%I.

End Definitions.

(** For some reason, Coq cannot find these RAs, so we define them explicitly *)
Definition ownS γ (m : gmap node node_gnames) `{distG Σ} :=
  own (A := authR system_state_mapUR) γ (● (to_agree <$> m)).

Definition ownF (f : gset socket_address) `{distG} :=
  own dist_fixed_name (to_agree f).

Notation "n n↦ x" := (mapsto_node n x)
     (at level 20, format "n  n↦  x") : uPred_scope.

(** Fixed socket end-points in the system *)
Notation "f↦ F" := (ownF F) (at level 20).

Lemma ownF_agree `{distG Σ} A B : f↦ A -∗ f↦ B -∗ ⌜A = B⌝.
Proof.
  iIntros "HA HB".
  by iDestruct (own_valid_2 with "HA HB") as %?%agree_op_invL'.
Qed.

(** Points-to locations on nodes *)
Notation "l ↦[ n ]{ q } v" := (mapsto_l n l q v)
  (at level 20, q at level 50, format "l  ↦[ n ]{ q }  v") : uPred_scope.
Notation "l ↦[ n ] v" := (mapsto_l n l 1 v) (at level 20) : uPred_scope.
Notation "l ↦[ n ]{ q } -" := (∃ v, l ↦[n]{q} v)%I
  (at level 20, q at level 50, format "l  ↦[ n ]{ q }  -") : uPred_scope.
Notation "l ↦[ n ] -" := (l ↦[n]{1} -)%I (at level 20) : uPred_scope.

(** Sockets s↦ *)
Notation "h s↦[ n ]{ q } s" := (mapsto_s n h q s)
  (at level 20, q at level 50, format "h  s↦[ n ]{ q }  s") : uPred_scope.
Notation "h s↦[ n ] s" := (mapsto_s n h 1 s) (at level 20) : uPred_scope.

(** Lookup l↦ *)
Notation "a l↦{ q } n" := (mapsto (L:=socket_address) (V:=node) a q n)
  (at level 20, q at level 50, format "a l↦{ q } n") : uPred_scope.
Notation "a l↦ n" :=
  (mapsto (L:=socket_address) (V:=node) a 1 n) (at level 20) : uPred_scope.

(** Lookup stored socket interpretation γ↦ *)
Notation "a γ↦ γ" :=
  (own (A:=socket_interpR)
       dist_si_name (◯ {[ a := (to_agree γ) ]})) (at level 20) : uPred_scope.

(** Messages m↦ *)
Notation "i m↦{ q } m" := (mapsto (L:=message_id) (V:=message) i q m)
  (at level 20, q at level 50, format "i  m↦{ q }  m") : uPred_scope.
Notation "i m↦ m" :=
  (mapsto (L:=message_id) (V:=message) i 1 m) (at level 20) : uPred_scope.

(** Sent messages c↦ *)
Notation "i o↦{ q } s" := (mapsto (L:=positive) (V:=message_stable) i q s)
  (at level 20, q at level 50, format "i o↦{ q } s") : uPred_scope.
Notation "i o↦ s" :=
  (mapsto (L:=positive) (V:=message_stable) i 1 s) (at level 20) : uPred_scope.

(** Received messages r↦ *)
Notation "a r↦{ q } g" := (mapsto (L:=socket_address) (V:=message_soup) a q g)
  (at level 20) : uPred_scope.
Notation "a r↦ g" := (mapsto (L:=socket_address) (V:=message_soup) a 1 g)
  (at level 20) : uPred_scope.

(** Socket interpretations ρ ⤇ *)

Global Instance saved_pred_proper `{savedPredG Σ A} n γ:
  Proper ((dist n) ==> (dist n)) (@saved_pred_own Σ A _ γ : (A -c> iProp Σ) -c> iProp Σ).
Proof.
  intros Φ Ψ Hps.
  f_equiv.
  destruct n; first done.
    by apply dist_S.
Qed.

Global Instance saved_pred_proper' `{savedPredG Σ A} γ:
  Proper ((≡) ==> (≡)) (@saved_pred_own Σ A _ γ : (A -c> iProp Σ) -c> iProp Σ).
Proof.
  apply ne_proper => n. apply _.
Qed.

Definition si_pred `{distG Σ} a (Φ : socket_interp Σ) : iProp Σ :=
  (∃ γ, a γ↦ γ ∗ saved_pred_own (A:=message_stable) γ Φ)%I.

Global Instance si_pred_prop `{distG Σ} a : Proper ((≡) ==> (≡)) (si_pred a).
Proof.
  intros x y Heq.
  apply exist_proper => z; f_equiv.
  by rewrite Heq.
Qed.

Notation "a ⤇ Φ" := (si_pred a Φ) (at level 20).

Definition FreeIPs_ctx `{distG Σ} (F : gset ip_address) :=
  own dist_freeips_name (● GSet F).

Definition FreeIP `{distG Σ} (ip : ip_address) :=
  own dist_freeips_name (◯ GSet {[ ip ]}).

Lemma is_FreeIP `{distG Σ} F ip :
  FreeIPs_ctx F -∗ FreeIP ip -∗ ⌜ip ∈ F⌝.
Proof.
  iIntros "HF Hip". iDestruct (own_valid_2 with "HF Hip") as %[Hi _].
  revert Hi; rewrite /= left_id => Hi.
  specialize (Hi 0); apply cmra_discrete_included_iff in Hi;
    apply gset_disj_included in Hi.
  iPureIntro. by apply elem_of_subseteq_singleton.
Qed.

Lemma Use_FreeIP `{distG Σ} F ip :
  FreeIPs_ctx F -∗ FreeIP ip ==∗ FreeIPs_ctx (F ∖ {[ ip ]}).
Proof.
  iIntros "HF Hip".
  iDestruct (is_FreeIP with "HF Hip") as %Hip.
  replace F with ({[ ip ]} ∪ (F ∖ {[ ip ]})) at 1; last first.
  { rewrite (comm_L _ {[ _ ]}) difference_union_L
    -(comm_L _ {[ _ ]}) subseteq_union_1_L //.
    by apply elem_of_subseteq_singleton. }
  iCombine "HF" "Hip" as "H".
  iMod (own_update with "H") as "H"; last by iFrame "H".
  apply auth_update_dealloc.
  rewrite -gset_disj_union; last by set_solver.
  by apply gset_disj_dealloc_empty_local_update.
Qed.

Lemma FreeIps_alloc `{inG Σ (authUR (gset_disjUR ip_address))}
      (F : gset ip_address) :
  (|==> ∃ γ, own γ (● GSet F) ∗ [∗ set] ip ∈ F, own γ (◯ GSet {[ ip ]}))%I.
Proof.
  iMod (own_alloc (● GSet ∅)) as (γ) "HM"; first done.
  iAssert (|==>
             ∃ M : gset ip_address,
               (⌜elements M ≡ₚ elements F⌝)
                 ∗ own γ (● GSet M) ∗ [∗ set] ip ∈ M, own γ (◯ GSet {[ ip ]}))%I
    with "[HM]" as "HF".
  { pose proof (NoDup_elements F) as Hnd.
    iInduction (elements F) as [|a l] "IHl".
    - iModIntro. iExists ∅.
      rewrite big_sepS_empty. iFrame.
      by iPureIntro.
    - inversion Hnd as [|? ? ? Hrd']; subst.
      iMod ("IHl" $! Hrd' with "HM") as (M HMl) "[HM HML]"; iFrame.
      assert (a ∉ M) as Hnm.
      { by rewrite -elem_of_elements HMl. }
      iMod (own_update _ _ (● GSet ({[a]} ∪ M) ⋅ ◯ GSet {[a]}) with "HM")
        as "[HM Ha]".
      { apply auth_update_alloc.
        apply gset_disj_alloc_empty_local_update; last by set_solver. }
      iModIntro.
      iExists ({[a]} ∪ M); iFrame.
      iSplit; first by iPureIntro; rewrite elements_union_singleton // HMl.
      rewrite big_sepS_insert; last done. iFrame. }
  iMod "HF" as (M HMF) "[? ?]".
  replace M  with F; first by iModIntro; iExists _; iFrame.
  apply elem_of_equiv_L => x.
  rewrite -!elem_of_elements.
  rewrite -elem_of_list_permutation_proper; eauto.
Qed.

Definition FreePorts_ctx `{distG Σ} (P : gmap ip_address (gset_disjUR port)) :=
  own dist_freeports_name (● P).

Definition FreePorts `{distG Σ} (ip : ip_address) (ports : gset port) :=
  own dist_freeports_name (◯ ({[ ip := (GSet ports)]})).

Lemma FreePorts_included `{distG Σ} P ip ports :
  FreePorts_ctx P -∗ FreePorts ip ports -∗
    ∃ ports', ⌜P !! ip = Some (GSet ports') ∧ ports ⊆ ports'⌝.
Proof.
  iIntros "HP Hip"; rewrite /FreePorts_ctx /FreePorts.
  iDestruct (own_valid with "HP") as %[_ HP].
  iCombine "HP" "Hip" as "HPip".
  iDestruct (own_valid with "HPip") as %[Hvld _].
  revert Hvld; rewrite //= left_id_L => Hvld.
  specialize (Hvld 0);
    apply cmra_discrete_included_iff, singleton_included in Hvld.
  destruct Hvld as [ports' [Hports'%leibniz_equiv HS]].
  specialize (HP ip); rewrite Hports' in HP.
  revert HS; rewrite Some_included_total => HS.
  destruct ports' as [ports'|]; last done.
  apply gset_disj_included in HS.
  by iExists _.
Qed.

Lemma FreePorts_distribute `{distG Σ} ip ports ports' :
  ports ## ports' →
  FreePorts ip (ports ∪ ports') ⊣⊢ FreePorts ip ports ∗ FreePorts ip ports'.
Proof.
  intros ?.
  by rewrite /FreePorts -gset_disj_union // -own_op -auth_frag_op op_singleton.
Qed.

Lemma FreePorts_alloc `{distG Σ} P ip ports :
  ip ∉ (dom (gset _) P) →
  FreePorts_ctx P ==∗ FreePorts_ctx (<[ ip := GSet ports ]>P) ∗ FreePorts ip ports.
Proof.
  iIntros (?) "HP"; rewrite /FreePorts_ctx /FreePorts.
  iMod (own_update _ _ (● _ ⋅ ◯ {[ ip := (GSet ports)]}) with "HP")
    as "[HP Hip]"; last by iFrame.
  apply auth_update_alloc, alloc_singleton_local_update; last done.
  by eapply not_elem_of_dom.
Qed.

Lemma FreePorts_dealloc `{distG Σ} P ip ports :
  FreePorts_ctx P -∗ FreePorts ip ports ==∗
    ∃ ports', ⌜P !! ip = Some (GSet ports') ∧ ports ⊆ ports'⌝ ∗
      FreePorts_ctx (<[ip := GSet (ports' ∖ ports)]> P).
Proof.
  iIntros "HP Hip"; rewrite /FreePorts_ctx /FreePorts.
  iDestruct (own_valid with "HP") as %[_ HP].
  iCombine "HP" "Hip" as "HPip".
  iDestruct (own_valid with "HPip") as %[Hvld _].
  revert Hvld; rewrite //= left_id_L => Hvld.
  specialize (Hvld 0);
    apply cmra_discrete_included_iff, singleton_included in Hvld.
  destruct Hvld as [ports' [Hports'%leibniz_equiv HS]].
  specialize (HP ip); rewrite Hports' in HP.
  revert HS; rewrite Some_included_total => HS.
  destruct ports' as [ports'|]; last done.
  apply gset_disj_included in HS.
  iMod (own_update _ _ (● _ ⋅ ◯ {[ ip := (GSet ∅)]}) with "HPip")
    as "[? ?]"; last by iExists _; iFrame; eauto.
  eapply auth_update, singleton_local_update; eauto.
  assert (ports' = ports' ∖ ports ∪ ports) as HPeq.
  { by rewrite difference_union_L (comm_L _ _ ports) subseteq_union_1_L. }
  rewrite {1}HPeq.
  rewrite -gset_disj_union; last set_solver.
  rewrite (comm_L (⋅)).
  apply gset_disj_dealloc_empty_local_update.
Qed.

Definition local_state_coherence (γmap : gmap node node_gnames)
           (heaps : gmap node heap) (sockets : gmap node sockets) :=
  dom (gset node) γmap = dom (gset node) heaps ∧
  dom (gset node) γmap = dom (gset node) sockets.

Definition network_coherence (L : lookup_table) (ips : gmap ip_address (gset port)) :=
  ∀ a P, is_Some (L !! a) →
         ips !! ip_of_address a = Some P →
         (port_of_address a) ∈ P.

Definition local_state_i `{distG Σ} (σ : state) (n : node) (x : node_gnames) :=
  (∃ (h : heap) (S : sockets),
      ⌜state_heaps σ !! n = Some h⌝ ∗
      ⌜state_sockets σ !! n = Some S⌝ ∗
      n n↦ x ∗
      gen_heap_ctx (hG := gen_heap_loc_instance (π_heap x)) h ∗
      gen_heap_ctx (hG := gen_heap_soc_instance (π_socket x)) S
  )%I.

Definition socket_interp_coherence `{distG Σ}
           (L : lookup_table) :=
  (∃ si fx,
      (⌜dom (gset socket_address) si = fx ∪ dom (gset socket_address) L⌝)
        ∗ f↦ fx ∗
       own (A:=socket_interpR) dist_si_name (● si) ∗
       ([∗ set] s ∈ (dom (gset socket_address) si), ∃ φ, s ⤇ φ))%I.

Definition messages_socket_coherence (rec : socket_received) (L : lookup_table) :=
  dom (gset socket_address) L = dom (gset socket_address) rec.

Definition messages_received_coherence (rec : socket_received) (M : message_soup) :=
  ∀ i M', rec !! i = Some M' →
          messages_received_at i M = M'.

Definition messages_sent_coherence (sent : messages_stable) (M : message_soup) :=
  dom (gset message_id) sent = dom (gset message_id) M ∧
  ∀ mId, sent !! mId = message_stable_from_message <$> (M !! mId).

Definition messages_coherence (rec : socket_received) (sent : messages_stable)
           (M : message_soup) (L : lookup_table) :=
  messages_socket_coherence rec L ∧
  messages_received_coherence rec M ∧
  messages_sent_coherence sent M.

Definition messages {Σ} `{distG Σ} (M : message_soup) (L : lookup_table) :=
  (
    ∃ sent rec,
      ⌜messages_coherence rec sent M L⌝ ∗
      gen_heap_ctx M ∗
      gen_heap_ctx sent ∗
      gen_heap_ctx rec ∗
      ([∗ map] sa↦g ∈ rec,
       ⌜g = messages_received_at sa M⌝ ∗
       sa r↦{½} g) ∗
      ([∗ map] mId↦m ∈ M,
       ∃ π (Φ : message_stable -c> iProp Σ), (⌜m_state m = MS_RECEIVED⌝ ∨
                     ⌜π = 1%Qp⌝ ∗ (m_destination m) ⤇ Φ ∗
                     ▷ Φ (message_stable_from_message m)) ∗
       mId m↦{π} m))%I.

Global Instance distG_irisG `{distG Σ} :
  irisG dist_lang Σ :=
  {|
    iris_invG := _;
    state_interp σ :=
      (
        ∃ (m : gmap node node_gnames),
          ⌜local_state_coherence m (state_heaps σ) (state_sockets σ)⌝ ∗
          ⌜network_coherence (state_lookup σ) (state_ports_in_use σ)⌝ ∗
           socket_interp_coherence (state_lookup σ) ∗
           ownS dist_map_name m ∗
           ([∗ map] n ↦ γs ∈ m, local_state_i σ n γs) ∗
           gen_heap_ctx (state_lookup σ) ∗
           (∃ Fip Piu, (⌜dom (gset _) Piu ## Fip ∧
                        (∀ ip, ip ∈ Fip → state_ports_in_use σ !! ip = Some ∅) ∧
                        (∀ ip P, Piu !! ip = Some (GSet P) →
                           ∃ Q, (state_ports_in_use σ) !! ip = Some Q ∧ P ## Q)⌝)
                         ∗ FreeIPs_ctx Fip ∗ FreePorts_ctx Piu)
           ∗ messages (state_ms σ) (state_lookup σ)
      )%I;
  |}.

Global Opaque iris_invG.

Local Hint Extern 0 (atomic _ _) => solve_atomic.
Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _; simpl.

Local Hint Constructors head_step.
Local Hint Resolve alloc_fresh.
Local Hint Resolve to_of_val.

Lemma network_coherence_insert σ a n P :
  state_ports_in_use σ !! ip_of_address a = Some P →
  network_coherence (state_lookup σ) (state_ports_in_use σ) →
  network_coherence (<[a:=n]> (state_lookup σ))
   (<[ip_of_address a:={[port_of_address a]} ∪ P]> (state_ports_in_use σ)).
Proof.
  rewrite /network_coherence; simpl.
  intros Hlookup H a' P' Hlookup'; simpl in *.
  destruct (decide (a = a')); simplify_eq.
  - rewrite lookup_insert. intros. simplify_eq.
      by apply elem_of_union_l,elem_of_singleton.
  - destruct (decide (ip_of_address a = ip_of_address a')) as [Heq|Hneq].
    + rewrite lookup_insert_ne in Hlookup'; auto.
      rewrite Heq lookup_insert. intro; simplify_eq.
      rewrite elem_of_union; right.
      apply H; eauto. by rewrite -Heq.
    + rewrite lookup_insert_ne; auto.
      rewrite lookup_insert_ne in Hlookup'; try done.
        by apply H.
Qed.

Section GhostStateLemmas.
  Context `{distG Σ}.

Definition message_soup_info M sent :=
  (⌜messages_sent_coherence sent M⌝ ∗
    gen_heap_ctx M ∗ gen_heap_ctx sent)%I.

Lemma mapsto_node_agree n γs γs' :
  n n↦ γs -∗ n n↦ γs' -∗ ⌜γs = γs'⌝.
Proof.
  apply wand_intro_r.
  rewrite /ownS mapsto_node_eq -own_op own_valid discrete_valid.
  f_equiv=> /auth_own_valid /=. rewrite op_singleton singleton_valid.
  apply (agree_op_invL' (A := node_gnamesC)).
Qed.

Lemma node_in_map n γ's (m : gmap node node_gnames) :
  (n n↦ γ's -∗
     ownS dist_map_name m -∗
     ⌜m !! n = Some γ's⌝)%I.
Proof.
  iIntros "H1 H2".
  iCombine "H2" "H1" as "H".
  rewrite /ownS mapsto_node_eq -own_op own_valid.
  iDestruct "H" as %HvalidR. iPureIntro.
  revert HvalidR.
  rewrite auth_valid_discrete_2.
  rewrite (singleton_included)=> -[[y [Hlookup Hless]] Hvalid].
  assert (Hvalidy := lookup_valid_Some _ n y Hvalid Hlookup).
  revert Hlookup.
  rewrite lookup_fmap fmap_Some_equiv=> -[v' [Hl Heq]]. revert Hless Heq.
  rewrite Some_included_total.
  destruct (to_agree_uninj y Hvalidy) as [y' <-].
  rewrite to_agree_included.
  intros Heq Heq'%(to_agree_inj y' v').
  apply leibniz_equiv in Heq.
  apply leibniz_equiv in Heq'.
    by simplify_eq.
Qed.

Lemma node_in_state_heaps n γ's (m : gmap node node_gnames) σ :
  m !! n = Some γ's →
  (([∗ map] n' ↦ γ's ∈ m, local_state_i σ n' γ's) -∗
  ⌜∃ x, (state_heaps σ) !! n = Some x⌝)%I.
Proof.
  iIntros (Hninm) "Hmap".
  iDestruct (big_sepM_lookup (local_state_i σ) m n _ with "[Hmap]") as "Hl";
    first done; iFrame.
  iDestruct "Hl" as (h s p) "(% & _)". iPureIntro; by exists h.
Qed.

Lemma node_in_state_sockets n γ's (m : gmap node node_gnames) σ :
  m !! n = Some γ's →
  (([∗ map] n' ↦ γ's ∈ m, local_state_i σ n' γ's) -∗
   ⌜∃ x, (state_sockets σ) !! n = Some x⌝)%I.
Proof.
  iIntros (Hninm) "Hmap".
  iDestruct (big_sepM_lookup (local_state_i σ) m n _ with "[Hmap]") as "Hl";
    first done; iFrame.
  iDestruct "Hl" as (h s) "(_ & % & _)". iPureIntro; by exists s.
Qed.

Lemma node_local_state n γ's m (σ : state) :
  m !! n = Some γ's →
  (([∗ map] n' ↦ x ∈ m, local_state_i σ n' x) -∗
  local_state_i σ n γ's ∗
  [∗ map] n' ↦ x ∈ (delete n m), local_state_i σ n' x)%I.
Proof.
  iIntros (Hinm) "Hmap".
  by rewrite -(big_sepM_delete (local_state_i σ) m n).
Qed.

Lemma map_local_state_i_update_heaps n m h (σ : state) :
  (([∗ map] n' ↦ x ∈ (delete n m), local_state_i σ n' x) -∗
  [∗ map] n' ↦ x ∈ (delete n m), local_state_i {|
                                     state_heaps := <[n:=h]>(state_heaps σ);
                                     state_sockets := state_sockets σ;
                                     state_lookup := state_lookup σ;
                                     state_ports_in_use := state_ports_in_use σ;
                                     state_ms := state_ms σ;
                                   |} n' x)%I.
Proof.
  erewrite (big_sepM_mono (local_state_i σ) (local_state_i _)).
  - iIntros "Hmap"; iFrame.
  - set_solver.
  - intros k x Hdel.
    destruct (decide (k = n)); rewrite /local_state_i; subst.
    + by rewrite lookup_delete in Hdel.
    + by rewrite lookup_insert_ne; last done.
Qed.

Lemma map_local_state_i_update_sockets n m S (σ : state) :
  (([∗ map] n' ↦ x ∈ (delete n m), local_state_i σ n' x) -∗
  [∗ map] n' ↦ x ∈ (delete n m), local_state_i {|
                                     state_heaps := state_heaps σ;
                                      state_sockets := <[n:=S]> (state_sockets σ);
                                      state_lookup := state_lookup σ;
                                      state_ports_in_use := state_ports_in_use σ;
                                      state_ms := state_ms σ;
                                    |} n' x)%I.
Proof.
  erewrite (big_sepM_mono (local_state_i σ) (local_state_i _)).
  - iIntros "Hmap"; iFrame.
  - set_solver.
  - intros k x Hdel.
    destruct (decide (k = n)); rewrite /local_state_i; subst.
    + by rewrite lookup_delete in Hdel.
    + by rewrite lookup_insert_ne; last done.
Qed.

Lemma map_local_state_i_update m σ L P M :
  (([∗ map] n ↦ x ∈ m, local_state_i σ n x) -∗
  [∗ map] n ↦ x ∈ m, local_state_i {|
                          state_heaps := state_heaps σ;
                          state_sockets := state_sockets σ;
                          state_lookup := L;
                          state_ports_in_use := P;
                          state_ms := M;
                        |} n x)%I.
Proof.
  rewrite /local_state_i; simpl. iIntros "H". iFrame.
Qed.

Lemma node_local_state_rev n γ's m (σ : state) :
  m !! n = Some γ's →
  (local_state_i σ n γ's -∗
  ([∗ map] n' ↦ x ∈ (delete n m), local_state_i σ n' x) -∗
  [∗ map] n' ↦ x ∈ m, local_state_i σ n' x )%I.
Proof.
  iIntros (Hinm) "Hl Hmap".
  iDestruct (big_sepM_insert (local_state_i σ)
                             (delete n m) n γ's with "[Hl Hmap]") as "HP".
  - apply lookup_delete.
  - iFrame.
  - apply insert_id in Hinm.
      by rewrite insert_delete Hinm.
Qed.

Lemma si_pred_agree a Φ Ψ x :
  a ⤇ Φ -∗ a ⤇ Ψ -∗ ▷ (Φ x ≡ Ψ x).
Proof.
  iIntros "#H1 #H2".
  iDestruct "H1" as (γ) "[H1 H1']".
  iDestruct "H2" as (γ') "[H2 H2']".
  iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
  rewrite -auth_frag_op op_singleton in Hvalid.
  apply singleton_valid in Hvalid.
  eapply @agree_op_invL' in Hvalid; last by typeclasses eauto.
  rewrite Hvalid.
  iDestruct (saved_pred_agree _ _ _ x with "H1' H2'") as "H".
  iExact "H".
Qed.

Lemma find_fixed_socket_interp σ a A :
  a ∈ A →
  f↦ A -∗ socket_interp_coherence σ -∗ ∃ Φ, a ⤇ Φ.
Proof.
  iIntros (HaA) "#HA H". iDestruct "H" as (si fx ->) "(#Hsi & Hfix & #Hdyn)".
  iDestruct (ownF_agree with "HA Hsi") as %?; subst.
  iDestruct (big_sepS_elem_of (A:=socket_address) with "Hdyn") as "$".
  by apply elem_of_union_l.
Qed.

Lemma message_sepM_later M :
  (([∗ map] mId↦m ∈ M,
    ∃ π (Φ : message_stable -c> iProp Σ), (⌜m_state m = MS_RECEIVED⌝ ∨
        ⌜π = 1%Qp⌝ ∗ (m_destination m) ⤇ Φ ∗ Φ (message_stable_from_message m)) ∗
        mId m↦{π} m) -∗
  ([∗ map] mId↦m ∈ M,
    ∃ π (Φ : message_stable -c> iProp Σ), (⌜m_state m = MS_RECEIVED⌝ ∨
        ⌜π = 1%Qp⌝ ∗ (m_destination m) ⤇ Φ ∗ ▷ Φ (message_stable_from_message m)) ∗
        mId m↦{π} m))%I.
Proof.
  iIntros "H".
  rewrite big_sepM_mono.
  - iFrame.
  - set_solver.
  - iIntros (k x H') "H".
    iDestruct "H" as (π φ) "([% | (H1 & H1' & H1'')] & H2)"; iExists π, φ; iFrame.
    + by iLeft.
    + iRight. iFrame.
Qed.

Lemma message_state_later M L :
  ((∃ sent rec,
      ⌜messages_coherence rec sent M L⌝ ∗
      gen_heap_ctx M ∗
      gen_heap_ctx sent ∗
      gen_heap_ctx rec ∗
      ([∗ map] sa↦g ∈ rec,
       ⌜g = messages_received_at sa M⌝ ∗
       sa r↦{½} g) ∗
      ([∗ map] mId↦m ∈ M,
       ∃ π (Φ : message_stable -c> iProp Σ), (⌜m_state m = MS_RECEIVED⌝ ∨
                     (⌜π = 1%Qp⌝ ∗ (m_destination m) ⤇ Φ ∗
                     Φ (message_stable_from_message m))) ∗
       mId m↦{π} m)) -∗ messages M L)%I.
Proof.
  iIntros "H". iDestruct "H" as (sent rec) "(H1 & H2 & H3 & H4 & H5 & H6)".
  iDestruct (message_sepM_later with "H6") as "H6".
  iExists sent, rec. iFrame.
Qed.

Lemma messages_received_id M sa mId m :
  M !! mId = None →
  m_state m = MS_SENT →
  messages_received_at sa (<[mId:=m]> M) =
  messages_received_at sa M.
Proof.
  intros.
  rewrite /messages_received_at map_filter_lookup_None_insert; auto.
  rewrite map_filter_lookup_None. by left.
  intros []; simpl in *. by rewrite H1 in H3.
Qed.

Lemma messages_insert M L mId msg :
  M !! mId = None →
  m_state msg = MS_SENT →
  (messages M L ==∗
  mId m↦ msg ∗
  mId o↦ message_stable_from_message msg ∗
  ∃ sent rec,
    ⌜messages_coherence
     rec
     (<[mId:=(message_stable_from_message msg)]>sent)
     (<[mId:=msg]>M)
     L⌝ ∗
    gen_heap_ctx (<[mId:=msg]>M) ∗
    gen_heap_ctx (<[mId:=message_stable_from_message msg]>sent) ∗
    gen_heap_ctx rec ∗
    ([∗ map] sa↦g ∈ rec, ⌜g = messages_received_at sa M⌝ ∗ sa r↦{½} g) ∗
    ([∗ map] mId↦m ∈ M,
     ∃ π (Φ : message_stable -c> iProp Σ),
       (⌜m_state m = MS_RECEIVED⌝ ∨
       ⌜π = 1%Qp⌝ ∗ (m_destination m) ⤇ Φ ∗
       ▷ Φ (message_stable_from_message m)) ∗
       mId m↦{π} m))%I.
Proof.
  iIntros (Hlookup Hsent) "Hmessages".
  iDestruct "Hmessages" as (sent rec [Hsoccoh [Hreccoh [Hdom Hsentcoh]]])
                             "(Hm & Hsent & Hrec & Hrecs & Hmsgs)".
  iMod (gen_heap_alloc M mId _ with "Hm") as "(Hms & HmId)"; first done.
  iMod (gen_heap_alloc sent mId (message_stable_from_message msg)
          with "Hsent") as "(Hsent & HsentId)".
  { by rewrite -(not_elem_of_dom (D:=gset message_id)) Hdom not_elem_of_dom. }
  iModIntro; iFrame. iExists _, _; iFrame. iPureIntro.
  split; first done.
  rewrite /messages_coherence /messages_received_coherence /messages_sent_coherence /=.
  repeat split.
  - intros. rewrite messages_received_id //=. by apply Hreccoh.
  - by rewrite !dom_insert_L Hdom.
  - intro. destruct (decide (mId = mId0)); subst.
    + rewrite !lookup_insert //=.
    + rewrite !lookup_insert_ne //=.
Qed.

Lemma message_split π1 π2 π m v :
  (π = π1 + π2)%Qp →
  m m↦{π1} v ∗ m m↦{π2} v ⊣⊢ m m↦{π} v.
Proof.
  intros ->.
  iSplit; iIntros "H";
  iDestruct "H" as "[H1 H2]"; iFrame.
Qed.

Lemma messages_update_received M mId m m' :
  M !! mId = Some m →
  m_state m = MS_SENT →
  m' = {| m_from_node := m_from_node m;
                          m_sender := m_sender m;
                          m_destination := m_destination m;
                          m_protocol := m_protocol m;
                          m_body := m_body m;
                          m_state := MS_RECEIVED;
                          m_sent := m_sent m;
                          m_received := (max_received M) + 1 |} →
  (gen_heap_ctx M ∗
  ([∗ map] k↦x ∈ M,
    (∃ (π : Qp) (φ : message_stable -c> iProp Σ),
        (⌜m_state x = MS_RECEIVED⌝
        ∨ ⌜π = 1%Qp⌝ ∗ m_destination x ⤇ φ ∗
          φ (message_stable_from_message x)) ∗ k m↦{π} x)) ==∗
  ∃ φ, (m_destination m ⤇ φ ∗ φ (message_stable_from_message m)) ∗ mId m↦{¾} m' ∗
  gen_heap_ctx (<[mId:=m']>M) ∗ ([∗ map] k↦x ∈ (<[mId:=m']>M),
       (∃ (π : Qp) (φ : message_stable -c> iProp Σ),
        (⌜m_state x = MS_RECEIVED⌝
        ∨ ⌜π = 1%Qp⌝ ∗ m_destination x ⤇ φ ∗
          φ (message_stable_from_message x)) ∗ k m↦{π} x)))%I.
Proof.
  iIntros (Hlookup Hsent Hm') "(Hms & Hmsg)".
  iDestruct (big_sepM_delete _ M with "Hmsg") as "[Hm Hmsg]". done.
  iDestruct "Hm" as (π φ) "([% | (% & Hsi & HP)] & Hm)".
  by rewrite H0 in Hsent.
  subst.
  iMod (gen_heap_update M mId _ {|
                                   m_from_node := m_from_node m;
                                   m_sender := m_sender m;
                                   m_destination := m_destination m;
                                   m_protocol := m_protocol m;
                                   m_body := m_body m;
                                   m_state := MS_RECEIVED;
                                   m_sent := m_sent m;
                                   m_received := max_received M + 1 |} with "Hms Hm")
    as "[Hms Hm]".
  iExists φ. iFrame.
  rewrite -(message_split ¼ ¾ 1%Qp mId);
    last by rewrite Qp_quarter_three_quarter.
  iDestruct "Hm" as "[Hm Hm']". iSplitL "Hm'"; first by iFrame.
  iModIntro.
  iDestruct (big_sepM_insert _ (delete mId M) mId _ with "[Hmsg Hm]") as "H";
  first by rewrite lookup_delete.
  - iFrame. iExists ¼,φ; iFrame; eauto.
  - by rewrite insert_delete; iFrame.
Qed.

Lemma messages_received_at_update M d msg m rec mId :
  M !! mId = Some m →
  m_state m ≠ MS_RECEIVED →
  msg = {| m_from_node := m_from_node m;
           m_sender := m_sender m;
           m_destination := d;
           m_protocol := m_protocol m;
           m_body := m_body m;
           m_state := MS_RECEIVED;
           m_sent := m_sent m;
           m_received := max_received M + 1 |} →
  (([∗ map] k↦y ∈ (delete d rec),
   ⌜y = messages_received_at k M⌝ ∗ k r↦{ ½} y) -∗
  d r↦{ ½} <[mId:=msg]> (messages_received_at d M) -∗
  ([∗ map] k↦y ∈ (<[d:=<[mId:=msg]>(messages_received_at d M)]> rec),
   ⌜y = messages_received_at k (<[mId:=msg]>M)⌝ ∗ k r↦{ ½} y))%I.
Proof.
  iIntros (Hlookup Hstate Hmsg) "Hrecs Hrec".
  iDestruct (big_sepM_mono
               (λ k y, (⌜y = messages_received_at k M⌝ ∗ k r↦{ ½} y))%I
               (λ k y, (⌜y = messages_received_at k (<[mId:=msg]>M)⌝
                                                  ∗ k r↦{ ½} y))%I
               (delete d rec) (delete d rec)
               with "[Hrecs]") as "Hrecs"; auto.
  iIntros (k M' Hlookup') "(% & H)".
  - iFrame.
  destruct (decide (d = k)).
  { rewrite e in Hlookup'. rewrite lookup_delete in Hlookup'.
    inversion Hlookup'. }
  iPureIntro.
  rewrite H0 /messages_received_at map_filter_lookup_None_insert //=.
  { rewrite map_filter_lookup_None. right. intros; simplify_eq.
    rewrite Hlookup in H1; simplify_eq.
    intros [H2 H3]. simpl in *. by destruct Hstate. }
  { intros [H3 H4]. rewrite Hmsg in H3. simpl in *. by destruct n. }
  - iDestruct (big_sepM_insert _ (delete d rec) d _ with "[Hrecs Hrec]") as "H".
    by rewrite lookup_delete. iFrame. iFrame.
    iPureIntro. rewrite /messages_received_at map_filter_lookup_insert Hmsg //=.
    by rewrite insert_delete.
Qed.

End GhostStateLemmas.
(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply to_base_val in H
  | H : ground_lang.head_step ?e _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H; subst; clear H
  | H : head_step ?e _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H; subst; clear H
end.

Local Ltac solve_exec_safe :=
  intros; inv_head_step; subst;
  repeat match goal with
         | H: _ ∧ _ |- _ => destruct H as [??]
         end;
  do 3 eexists; eapply (LocalStepPureS _ ∅); econstructor; subst;
  try done; by apply ground_lang.to_of_val.

Local Ltac solve_exec_puredet :=
  intros; inv_head_step;
  first (by repeat match goal with
           | H: _ ∧ _ |- _ => destruct H as [??]; simplify_eq
           | H : ground_lang.to_val _ = Some _ |- _ =>
                    rewrite ground_lang.to_of_val in H; simplify_eq
           end);
    try by match goal with
       | H : socket_step _  _ _ _ _ _ _ _ _ _ _ |- _ =>
         inversion H
       end.

Local Ltac solve_pure_exec :=
  unfold AsVal in *; subst;
  repeat
    match goal with
    | H: IntoVal ⟨_;?e⟩ 〈_;?v〉 |- _ =>
      rewrite -(ground_lang.of_to_val e v (to_base_val ⟨_;e⟩ 〈_;v〉 H)); clear H
    | H: AsVal ⟨_;?e⟩ |- _ => idtac
    | H: is_Some _ |- _ => destruct H as [??]
    end;
  intros; apply det_head_step_pure_exec; [ solve_exec_safe | solve_exec_puredet ].

Class AsRec (n : node) (e : ground_lang.expr)
      (f x : binder) (erec : ground_lang.expr) :=
  as_rec : ⟨n;e⟩ = ⟨n;Rec f x erec⟩.
Instance AsRec_rec n f x e : AsRec n (Rec f x e) f x e := eq_refl.
Instance AsRec_rec_locked_val n v f x e :
  AsRec n (ground_lang.of_val v) f x e → AsRec n (ground_lang.of_val (locked v)) f x e.
Proof. by unlock. Qed.

Instance pure_rec n f x (erec e1 e2 : ground_lang.expr)
    `{!AsVal ⟨n;e2⟩, AsRec n e1 f x erec, Closed (f :b: x :b: []) ⟨n;erec⟩} :
  PureExec True ⟨n;App e1 e2⟩ ⟨n;subst' x e2 (subst' f e1 erec)⟩.
Proof. unfold AsRec in *.
       unfold AsVal in *; subst.
       destruct AsVal0 as [??].
       apply det_head_step_pure_exec.
       - solve_exec_safe.
       - intros; inv_head_step; last inversion SocketStep.
         apply ground_lang.of_to_val in H1. by simplify_eq.
Qed.

Instance pure_unop op e v v' `{!IntoVal ⟨n;e⟩ 〈n;v〉} :
  PureExec (un_op_eval op v = Some v') ⟨n;UnOp op e⟩ ⟨n;ground_lang.of_val v'⟩.
Proof. solve_pure_exec. Qed.

Instance pure_binop op e1 e2 v1 v2 v'
         `{!IntoVal ⟨n;e1⟩ 〈n;v1〉, !IntoVal ⟨n;e2⟩ 〈n;v2〉} :
  PureExec (bin_op_eval op v1 v2 = Some v')
           ⟨n;BinOp op e1 e2⟩ ⟨n;ground_lang.of_val v'⟩.
Proof. solve_pure_exec. Qed.

Instance pure_if_true e1 e2 : PureExec True ⟨n;If (Lit (LitBool true)) e1 e2⟩ ⟨n;e1⟩.
Proof. solve_pure_exec. Qed.

Instance pure_if_false e1 e2 : PureExec True ⟨n;If (Lit (LitBool false)) e1 e2⟩ ⟨n;e2⟩.
Proof. solve_pure_exec. Qed.

Instance pure_find_from e0 e1 e2 v0 v1 n1 v2 v'
         `{!IntoVal ⟨n;e0⟩ 〈n;LitV $ LitString v0〉,
           !IntoVal ⟨n;e1⟩ 〈n;LitV $ LitInt v1〉,
           !IntoVal ⟨n;e2⟩ 〈n;LitV $ LitString v2〉} :
  PureExec (index n1 v2 v0 = v' ∧ Z.of_nat n1 = v1)
           ⟨n;FindFrom e0 e1 e2⟩ ⟨n;ground_lang.of_val (option_nat_to_val v')⟩.
Proof. solve_pure_exec. Qed.

Instance pure_substring e0 e1 e2 v0 v1 n1 v2 n2 v'
         `{!IntoVal ⟨n;e0⟩ 〈n;LitV $ LitString v0〉,
           !IntoVal ⟨n;e1⟩ 〈n;LitV $ LitInt v1〉,
           !IntoVal ⟨n;e2⟩ 〈n;LitV $ LitInt v2〉} :
  PureExec (substring n1 n2 v0 = v' ∧ Z.of_nat n1 = v1 ∧ Z.of_nat n2 = v2)
           ⟨n;Substring e0 e1 e2⟩ ⟨n;ground_lang.of_val (LitV $ LitString v')⟩.
Proof. solve_pure_exec. Qed.

Instance pure_fst e1 e2 v1 `{!IntoVal ⟨n;e1⟩ 〈n;v1〉, !AsVal ⟨n;e2⟩} :
  PureExec True ⟨n;Fst (Pair e1 e2)⟩ ⟨n;e1⟩.
Proof. solve_pure_exec. Qed.

Instance pure_snd e1 e2 v2 `{!AsVal ⟨n;e1⟩, !IntoVal ⟨n;e2⟩ 〈n;v2〉} :
  PureExec True ⟨n; Snd (Pair e1 e2)⟩ ⟨n;e2⟩.
Proof. solve_pure_exec. Qed.

Instance pure_case_inl e0 v e1 e2 `{!IntoVal ⟨n;e0⟩ 〈n;v〉} :
  PureExec True ⟨n; Case (InjL e0) e1 e2⟩ ⟨n; App e1 e0⟩.
Proof. solve_pure_exec. Qed.

Instance pure_case_inr e0 v e1 e2 `{!IntoVal ⟨n;e0⟩ 〈n;v〉} :
  PureExec True ⟨n;Case (InjR e0) e1 e2⟩ ⟨n;App e2 e0⟩.
Proof. solve_pure_exec. Qed.

Instance pure_make_address e1 e2 v1 v2
         `{!IntoVal ⟨n;e1⟩ 〈n;LitV (LitString v1)〉,
           !IntoVal ⟨n;e2⟩ 〈n;LitV (LitInt (v2))〉} :
  PureExec True
           ⟨n;MakeAddress e1 e2⟩
           ⟨n;LitV (LitSocketAddress (SocketAddressInet v1 (Z.to_pos v2)))⟩.
Proof. solve_pure_exec. Qed.

Section lifting.
  Context `{distG Σ}.

Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.

(** Base axioms for core primitives of the language: Stateless reductions *)
Lemma wp_fork n s E e Φ :
  ▷ Φ 〈n;LitV LitUnit〉 ∗ ▷ WP ⟨n;e⟩ @ s; ⊤ {{ _, True }} ⊢ WP ⟨n;Fork e⟩ @ s; E {{ Φ }}.
Proof.
  iIntros "[HΦ He]".
  iApply (@wp_lift_pure_det_head_step dist_ectx_lang with "[-]").
  - solve_exec_safe.
  - solve_exec_puredet.
  - iModIntro. iNext. iModIntro. iSplitL "HΦ".
    + iApply wp_value; eauto.
    + by rewrite big_opL_singleton.
Qed.

Lemma wp_start (n : node) (i : ip_address) (P : gset port) s E e Φ :
  n ≠ "system" →
  ▷ FreeIP i ∗
  ▷ Φ 〈"system";LitV LitUnit〉 ∗
  ▷ ((∃ γs, n n↦ γs) -∗ FreePorts i P -∗ WP ⟨n;e⟩ @ s; ⊤ {{ _, True }}) ⊢
  WP ⟨"system";Start (LitString n) (LitString i) e⟩ @ s; E {{ Φ }}.
Proof.
  iIntros (Hneq) "(>Hip & HΦ & Hwp)".
  iApply (@wp_lift_head_step dist_ectx_lang with "[-]"); first auto.
  - iIntros (σ1) "H".
    iMod (fupd_intro_mask _ ∅ True%I with "[]") as "H'";
      first set_solver; auto.
    iDestruct "H" as (x [Hdomheap Hdomsock] Hncoh)
                       "(Hsi & Hγs & HlocS & Hlookup & Hips & Hmsg)".
    iDestruct "Hips" as (Fip Piu (Hdsj & HFip & HPiu)) "[HFip HPiu]".
    iDestruct (is_FreeIP with "HFip Hip") as %Hip.
    iMod (Use_FreeIP with "HFip Hip") as "HFip".
    iMod (FreePorts_alloc _ i P with "HPiu") as "[HPiu Hports]";
      first set_solver.
    iModIntro; iSplit; first iPureIntro.
    + do 3 eexists. apply StartStepS; eauto.
    + iNext. iIntros (e2 σ2 efs Hrd). iMod "H'" as "_".
      iDestruct (message_state_later with "Hmsg") as "Hmsg".
      inversion Hrd; last inversion SocketStep; subst; try inversion BaseStep.
      destruct (state_heaps σ1 !! n) eqn:Heq1;
        destruct (state_sockets σ1 !! n) eqn:Heq2; destruct σ1; simpl in *;
          rewrite Heq1 Heq2 /=.
      * assert (Hin : is_Some (x !! n)).
        { rewrite -(elem_of_dom (D:=gset node)) Hdomheap elem_of_dom; eauto. }
        destruct Hin.
        iDestruct (node_local_state with "HlocS") as "(Hloc & HlocS)";
          first done.
        iDestruct "Hloc" as (heap sockets Hheap Hsockets)
                              "(Hγs' & Hheap & Hsockets)".
        rewrite {2}mapsto_node_eq /mapsto_node_def.
        iDestruct "Hγs'" as "#Hγs'".
        iDestruct (node_local_state_rev with "[Hheap Hsockets] HlocS") as
            "HlocS"; first done.
        -- iExists heap,sockets; iFrame; simpl. repeat iSplitR; auto.
           rewrite mapsto_node_eq /mapsto_node_def. iFrame "#".
        -- iSplitR "HΦ Hwp Hports".
           ++ iExists (<[n:=x0]>x).
              rewrite ![<[ _ := _]> state_sockets0](insert_id) //.
              rewrite ![<[ _ := _]> state_heaps0](insert_id) //.
              rewrite ![<[ _ := _]> x](insert_id) //.
              iFrame; auto.
              simpl in *.
              iModIntro; repeat iSplit; auto.
              iExists _, _; iFrame. iPureIntro; repeat split.
              { rewrite dom_insert. set_solver. }
              { intros ? ?; apply HFip; set_solver. }
              { intros ip Q HipQ.
                destruct (decide (i = ip)); subst.
                - rewrite lookup_insert in HipQ; simplify_eq.
                  rewrite HFip //. eexists; split; eauto.
                  set_solver.
                - rewrite lookup_insert_ne // in HipQ.
                  eapply HPiu; eauto. }
           ++ iSplitL "HΦ". iApply wp_value; unfold IntoVal; eauto.
              iSplitL; last done.
              iApply ("Hwp" with "[]"); last done.
              rewrite mapsto_node_eq /mapsto_node_def; iFrame "#"; iFrame; eauto.
      * revert Heq1 Heq2.
        rewrite -(not_elem_of_dom (D:=gset node)).
        rewrite -Hdomsock Hdomheap not_elem_of_dom.
        intros Hsh1 Hsh2; rewrite Hsh1 in Hsh2; simplify_eq.
      * revert Heq1 Heq2.
        rewrite -(not_elem_of_dom (D:=gset node)).
        rewrite -Hdomheap Hdomsock not_elem_of_dom.
        intros Hsh1 Hsh2. rewrite Hsh1 in Hsh2. simplify_eq.
      * iMod (own_alloc (A:=authR (gen_heapUR loc ground_lang.val))
                        (● to_gen_heap ∅)) as (γh) "Hheap".
        { apply: auth_auth_valid. exact: to_gen_heap_valid. }
        iMod (own_alloc (A:=authR (gen_heapUR socket_handle socket))
                        (● to_gen_heap ∅)) as (γs) "Hsocket".
        { apply: auth_auth_valid. exact: to_gen_heap_valid. }
        iMod (own_update (A:=authR (gmapUR node (agreeR node_gnamesC)))
                         _
                         (● (to_agree <$> x))
                         (● (to_agree <$> (<[n:=(γh,γs)]>x)) ⋅
                            (◯ {[ n := to_agree (γh,γs) ]} : auth system_state_mapUR))
                            with "Hγs") as "[Hγs #Hγl]".
        { rewrite fmap_insert.
          apply @auth_update_alloc.
          apply @alloc_singleton_local_update; last done.
          by rewrite -(not_elem_of_dom (D:=gset node))
                        dom_fmap_L Hdomheap not_elem_of_dom. }
        iSplitR "HΦ Hwp Hports".
        -- iExists (<[n:=(γh,γs)]>x).
           iFrame. iSplitR.
           { iPureIntro. rewrite /local_state_coherence.
             rewrite !dom_insert_L. rewrite -Hdomheap Hdomsock /= //. }
           iSplitR; first done.
           assert (x !! n = None).
           { by rewrite -(not_elem_of_dom (D:=gset node))
                           Hdomheap not_elem_of_dom. }
           rewrite big_sepM_insert; auto. rewrite -{1}(delete_notin x n); auto.
           iDestruct (map_local_state_i_update_heaps with "HlocS") as "HlocS".
           iDestruct (map_local_state_i_update_sockets with "HlocS") as "HlocS".
           rewrite /= delete_notin; auto. iFrame.
           iSplitL "Hheap Hsocket".
           ++ iExists _,_.
              rewrite !lookup_insert mapsto_node_eq /mapsto_node_def /= //.
              iFrame; iFrame "#". iModIntro. iSplit; iPureIntro; auto.
           ++ iModIntro; iExists _, _; iFrame. iPureIntro; repeat split.
              { rewrite dom_insert. set_solver. }
              { intros ? ?; apply HFip; set_solver. }
              { intros ip Q HipQ.
                destruct (decide (i = ip)); subst.
                - rewrite lookup_insert in HipQ; simplify_eq.
                  rewrite HFip //. eexists; split; eauto.
                  set_solver.
                - rewrite lookup_insert_ne // in HipQ.
                  eapply HPiu; eauto. }
        -- iSplitL "HΦ". iApply wp_value; unfold IntoVal; eauto.
           iSplitL; last done.
           iApply ("Hwp" with "[]"); last done.
           rewrite mapsto_node_eq /mapsto_node_def; iFrame "#"; iFrame; eauto.
Qed.

(** State Lemmas **)

Global Instance mapsto_n_timeless (n : node) v : Timeless (n n↦ v).
Proof. rewrite mapsto_node_eq /mapsto_node_def. apply _. Qed.

Global Instance mapsto_l_timeless (n : node) l q v : Timeless (mapsto_l n l q v).
Proof. rewrite /mapsto_l /Timeless.
       iIntros "H".
       iDestruct "H" as (γ's) "(>H1 & >H2)".
       iExists γ's. iFrame.
Qed.

(* Global Instance dist_fixedG_timeless F : Timeless (ownF dist_fixed_name F). *)
(* Proof. apply _. Qed. *)

(** Heap *)
Lemma wp_alloc n s E e v γ's:
  IntoVal ⟨n;e⟩ 〈n;v〉 →
  {{{ ▷ n n↦ γ's }}} ⟨n;Alloc e⟩ @ s; E {{{ l, RET 〈n;LitV (LitLoc l)〉; l ↦[n] v }}}.
Proof.
  iIntros (Heq%of_to_val Φ) ">Hn HΦ"; inversion Heq; subst.
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "H !>"; simpl in *.
  iDestruct "H" as (m Hloch Hncoh) "(Hsicoh & Hmaps & HlocS & Hrest)".
  iDestruct (node_in_map with "Hn Hmaps") as %Hninm.
  iDestruct (node_in_state_heaps with "HlocS") as %[h Hninss];
    first by apply Hninm.
  iSplitR.
  { iPureIntro. do 3 eexists.
    eapply LocalStepS; eauto.
    apply alloc_fresh, ground_lang.to_of_val. }
  iIntros (v2 σ2 efs Hstep); inv_head_step; last inversion SocketStep.
  rewrite /messages /messages_coherence //=. iFrame.
  destruct γ's as [γh γs]; iSplitR; auto; iFrame. iNext.
  iDestruct (node_local_state with "[HlocS]") as "(Hl & HlocS)";
    first done; iFrame.
  iDestruct "Hl" as (h' S' Hh Hs) "(Hn' & Hheap & Hsockets)";
    rewrite Hh in Hninss; simplify_eq; simpl.
  iMod (gen_heap_alloc (H0 := gen_heap_loc_instance γh) with "[Hheap]")
    as "[Hheap Hl]"; eauto.
  iDestruct (map_local_state_i_update_heaps with "HlocS") as "HlocS".
  iModIntro. iSplitR "HΦ Hl Hn".
  + iExists m; iFrame.
    iDestruct (node_local_state_rev with "[Hn' Hheap Hsockets] HlocS")
      as "HX"; first done; simpl.
    { iExists (<[l:=v0]> h),_. simpl in *; iFrame; simpl. iPureIntro.
      by rewrite lookup_insert. }
    iFrame. rewrite /local_state_coherence.
    rewrite (dom_insert_Some (D:=gset node) _ _ h) /= //.
  + iApply "HΦ".
    rewrite ground_lang.to_of_val in H1; simplify_eq.
    iExists (γh,γs). iFrame.
Qed.

Lemma wp_load n s E l q v :
  {{{ ▷ l ↦[n]{q} v }}}
    ⟨n; Load (Lit (LitLoc l))⟩ @ s; E
  {{{ RET 〈n;v〉; l ↦[n]{q} v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ !>".
  iDestruct "Hσ" as (m Hlcoh Hncoh) "(Hsic & Hmaps & HlocS & Hrest)".
  iDestruct "Hl" as ([γh γs]) "(Hn & Hl)".
  iDestruct (node_in_map with "Hn Hmaps") as %Hninm.
  iDestruct (node_in_state_heaps _ _ _ _ Hninm with "HlocS") as %[h Hninss].
  iDestruct (node_local_state with "[HlocS]") as "(Hloc & HlocS)";
    first done; iFrame.
  iDestruct "Hloc" as (h' S' Hheap Hsockets) "(Hn' & Hheap & Hsockets)".
  rewrite Hheap in Hninss; simplify_eq.
  iDestruct (@gen_heap_valid with "Hheap Hl") as %?.
  iSplit.
  { iPureIntro. do 3 eexists. eapply LocalStepS; eauto. eapply LoadS; eauto. }
  iIntros (v2 σ2 efs Hstep); inv_head_step; last inversion SocketStep.
  iFrame. iNext; iModIntro; iSplit => //=.
  iSplitR "HΦ Hl Hn".
  + iExists m; iFrame.
    iDestruct (node_local_state_rev with "[Hn' Hheap Hsockets] HlocS")
      as "HX"; first done; eauto.
    { iExists h',S'; iFrame; auto. }
    { rewrite insert_id; last auto. iFrame. auto. }
  + rewrite /to_val ground_lang.to_of_val; simpl.
    iApply "HΦ". iExists _; iFrame.
Qed.

Lemma wp_store n s E l v' e v :
  IntoVal ⟨n;e⟩ 〈n;v〉 →
  {{{ ▷ l ↦[n] v' }}}
    ⟨n;Store (Lit (LitLoc l)) e⟩ @ s; E
  {{{ RET 〈n;LitV LitUnit〉; l ↦[n] v }}}.
Proof.
  iIntros (Hval Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ !>".
  iDestruct "Hσ" as (m Hlcoh Hncoh) "(Hsic & Hmaps & HlocS & Hrest)".
  iDestruct "Hl" as ([γh γs]) "(Hn & Hl)".
  iDestruct (node_in_map with "Hn Hmaps") as %Hninm.
  iDestruct (node_in_state_heaps _ _ _ _ Hninm with "HlocS") as %[h Hninss].
  iDestruct (node_local_state with "[HlocS]") as "(Hloc & HlocS) ";
    first done; iFrame.
  iDestruct "Hloc" as (h' S' Hheap Hsockets) "(Hn' & Hheap & Hsockets)".
  rewrite Hheap in Hninss; simplify_eq.
  iDestruct (@gen_heap_valid with "Hheap Hl") as %?.
  iSplit.
  { iPureIntro; do 3 eexists. eapply LocalStepS; eauto.
    apply to_base_val' in Hval. by eapply StoreS; eauto. }
  iIntros (v2 σ2 efs Hstep); inv_head_step; last inversion SocketStep.
  iFrame; iNext.
  iMod (gen_heap_update (H0 := gen_heap_loc_instance γh) with "Hheap Hl")
    as "(Hheap & Hl)".
  iFrame. iModIntro. iSplit=>//.
  iSplitR "HΦ Hl Hn".
  + iExists m; iFrame.
    iDestruct (map_local_state_i_update_heaps with "HlocS") as "HlocS".
    iDestruct (node_local_state_rev with "[Hn' Hheap Hsockets] HlocS")
      as "HX"; first done; eauto.
    iExists (<[l:=v0]>h),S'.
    iFrame; iSplit; iPureIntro;
      [ apply lookup_insert | auto ].
    iFrame. rewrite /local_state_coherence.
    rewrite (dom_insert_Some (D:=gset node) _ _ h) /= //.
  + iApply "HΦ".
    apply to_base_val' in Hval. simplify_eq.
    iExists (γh,γs). iFrame.
Qed.

Lemma wp_cas_fail n s E l q v' e1 v1 e2 :
  IntoVal ⟨n;e1⟩ 〈n;v1〉 → AsVal ⟨n;e2⟩ → v' ≠ v1 →
  {{{ ▷ l ↦[n]{q} v' }}}
    ⟨n;CAS (Lit (LitLoc l)) e1 e2⟩ @ s; E
  {{{ RET 〈n;LitV (LitBool false)〉; l ↦[n]{q} v' }}}.
Proof.
  iIntros (Hv1 [[n' v2] Hv2] ? Φ) ">Hl HΦ".
  (* apply of_to_val in Hv1. apply of_to_val in Hv2. *)
  (* iIntros (<-%of_to_val [v2 <-%of_to_val] ? Φ) ">Hl HΦ". *)
  apply of_to_val in Hv2; inversion Hv2; simplify_eq.
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ !>".
  iDestruct "Hσ" as (m Hlcoh Hncoh) "(Hsic & Hmaps & HlocS & Hrest)".
  iDestruct "Hl" as ([γh γs]) "(Hn & Hl)".
  iDestruct (node_in_map with "Hn Hmaps") as %Hninm.
  iDestruct (node_in_state_heaps _ _ _ _ Hninm with "HlocS") as %[h Hninss].
  iDestruct (node_local_state with "[HlocS]") as "(Hloc & HlocS) ";
    first done; iFrame.
  iDestruct "Hloc" as (h' S' Hheap Hsockets) "(Hn' & Hheap & Hsockets)".
  rewrite Hheap in Hninss; simplify_eq.
  iDestruct (@gen_heap_valid with "Hheap Hl") as %?.
  iSplit.
  { iPureIntro; do 3 eexists.
    eapply LocalStepS; eauto. apply to_base_val' in Hv1.
    eapply CasFailS; eauto. eapply ground_lang.to_of_val. }
  iIntros (v2' σ2 efs Hstep); inv_head_step; last inversion SocketStep.
  iFrame; iNext; iModIntro; iSplit=>//; iSplitR "HΦ Hl Hn".
  + iExists m; iFrame.
      iDestruct (node_local_state_rev with "[Hn' Hheap Hsockets] HlocS")
        as "HX"; first done; eauto.
      { iExists h',S'; iFrame; auto. }
      { rewrite insert_id; last auto. iFrame. auto. }
    + iApply "HΦ". iExists (γh,γs). iFrame.
    + apply to_base_val' in Hv1; simplify_eq.
Qed.

Lemma wp_cas_suc n s E l e1 v1 e2 v2 :
  IntoVal ⟨n;e1⟩ 〈n;v1〉 → IntoVal ⟨n;e2⟩ 〈n;v2〉 →
  {{{ ▷ l ↦[n] v1 }}}
    ⟨n;CAS (Lit (LitLoc l)) e1 e2⟩ @ s; E
  {{{ RET 〈n;LitV (LitBool true)〉; l ↦[n] v2 }}}.
Proof.
  iIntros (Hv1 Hv2 Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ !>".
  iDestruct "Hσ" as (m Hlcoh Hncoh) "(Hsic & Hmaps & HlocS & Hrest)".
  iDestruct "Hl" as ([γh γs]) "(Hn & Hl)".
  iDestruct (node_in_map with "Hn Hmaps") as %Hninm.
  iDestruct (node_in_state_heaps _ _ _ _ Hninm with "HlocS") as %[h Hninss].
  iDestruct (node_local_state with "[HlocS]") as "(Hloc & HlocS) ";
    first done; iFrame.
  iDestruct "Hloc" as (h' S' Hheap Hsockets) "(Hn' & Hheap & Hsockets)".
  rewrite Hheap in Hninss; simplify_eq.
  iDestruct (@gen_heap_valid with "Hheap Hl") as %?.
  iSplit.
  { iPureIntro; do 3 eexists.
    eapply LocalStepS; eauto.
    apply to_base_val' in Hv1. apply to_base_val' in Hv2.
    by eapply CasSucS; eauto. }
  - iIntros (v2' σ2 efs Hstep); inv_head_step; last inversion SocketStep.
    apply to_base_val', ground_lang.of_to_val in Hv1.
    apply ground_lang.of_to_val in H4; simplify_eq.
    iFrame; iNext.
    iMod (gen_heap_update (H0 := gen_heap_loc_instance γh) with "Hheap Hl")
      as "(Hheap & Hl)".
    iFrame. iModIntro. iSplit=>//.
    iSplitR "HΦ Hl Hn".
    + iExists m; iFrame.
      iDestruct (map_local_state_i_update_heaps with "HlocS") as "HlocS".
      iDestruct (node_local_state_rev with "[Hn' Hheap Hsockets] HlocS")
        as "HX"; first done; eauto.
      iExists (<[l:=v3]>h),S'.
      iFrame; iSplit; iPureIntro;
        [ apply lookup_insert | auto ].
      iFrame. rewrite /local_state_coherence.
      rewrite (dom_insert_Some (D:=gset node) _ _ h) /= //.
    + iApply "HΦ".
      apply to_base_val' in Hv2. simplify_eq.
      iExists (γh,γs). iFrame.
Qed.

(* Network *)
Lemma wp_new_socket n s E e1 v1 e2 v2 e3 v3 γ's:
  IntoVal ⟨n;e1⟩ 〈n;#(LitAddressFamily v1)〉 →
  IntoVal ⟨n;e2⟩ 〈n;#(LitSocketType v2)〉 →
  IntoVal ⟨n;e3⟩ 〈n;#(LitProtocol v3)〉 →
  {{{ ▷ n n↦ γ's }}}
    ⟨n;NewSocket e1 e2 e3⟩ @ s; E
  {{{ h, RET 〈n;LitV (LitSocket h)〉;
      h s↦[n] {| Network.sfamily := v1;
                 Network.stype := v2;
                 Network.sprotocol := v3;
                 Network.saddress := None |} }}}.
Proof.
  iIntros (Heq1%of_to_val Heq2%of_to_val Heq3%of_to_val Φ) ">Hn HΦ";
    inversion Heq1; inversion Heq2; inversion Heq3; subst.
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "H !>"; simpl in *.
  iDestruct "H" as (m Hlcoh Hncoh) "(Hsicoh & Hmaps & HlocS & Hrest)".
  iDestruct (node_in_map with "Hn Hmaps") as %Hninm.
  iDestruct (node_in_state_sockets _ _ _ _ Hninm with "HlocS") as %[S Hnins].
  iDestruct (node_local_state with "[HlocS]") as "(Hs & HlocS) ";
    first done; iFrame.
  iSplitR.
  { iPureIntro; do 3 eexists; apply SocketStepS with (S := S) ; try auto; subst.
    apply newsocket_fresh; by eauto. }
  iIntros (v2' σ2 efs Hstep); inv_head_step; inversion SocketStep; subst.
  destruct γ's as [γh γs]; iSplitR; auto; iFrame.
  iDestruct "Hs" as (h' S'' Hh Hs) "(Hn' & Hheap & Hsockets)";
    rewrite Hs in Hnins; simplify_eq; simpl. iNext.
  iMod (gen_heap_alloc (H0 := gen_heap_soc_instance γs) with "[Hsockets]")
    as "[Hsockets Hs]"; first done; iFrame.
  iDestruct (map_local_state_i_update_sockets with "HlocS") as "HlocS".
  iModIntro. iSplitR "HΦ Hs Hn"; iFrame.
  + iExists m. iFrame. inversion SocketStep; simplify_eq.
    iDestruct (node_local_state_rev with "[Hn' Hheap Hsockets] HlocS")
      as "HX"; first done; simpl.
    { iExists h',(<[handle:=_]> S).
      simpl in *. iFrame. iPureIntro.
      split; try auto. apply lookup_insert. }
    try rewrite H6.
    iFrame. rewrite /local_state_coherence.
    rewrite (dom_insert_Some (D:=gset node) _ _ S) /= //.
  + iApply "HΦ".
    iExists (γh,γs). iFrame.
    by repeat match goal with
           | H : address_family |- _ => destruct H
           | H : protocol |- _ => destruct H
           | H : socket_type |- _ => destruct H
           | H : ground_lang.to_val _ = Some _ |- _ =>
             apply ground_lang.of_to_val in H; cbv in H
           end; simplify_eq.
Qed.

Lemma wp_bind_socket_fix_suc n s A
      E sh v e (a : socket_address) :
  IntoVal ⟨n;e⟩ 〈n;#a〉 →
  saddress v = None →
  a ∈ A →
  {{{ f↦ A ∗ ▷ FreePorts (ip_of_address a) {[(port_of_address a)]}
       ∗ ▷ sh s↦[n] v }}}
    ⟨n;SocketBind (Lit (LitSocket sh)) e⟩ @ s; E
  {{{ RET 〈n;LitV (LitInt 0)〉;
      ∃ g, sh s↦[n] {| sfamily := sfamily v;
                    stype := stype v;
                    sprotocol := sprotocol v;
                    saddress := Some a |} ∗
        a l↦ n ∗ a r↦{½} g ∗ ∃ φ, a ⤇ φ }}}.
  Proof.
    iIntros (Heq1%of_to_val Hnone HaA Φ) "(#Hf & >Hip & >Hs) HΦ";
      inversion Heq1; simplify_eq; clear Heq1.
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1) "Hσ".
    iDestruct "Hσ" as (m Hlcoh Hncoh)
              "(Hsicoh & Hmaps & HlocS & Hlookup & Hips & Hms)".
    iDestruct "Hips" as (Fip Piu (Hdsj & HFip & HPiu)) "[HFip HPiu]".
    iMod (FreePorts_dealloc with "HPiu Hip")
      as (ports [Hports Hportsa%elem_of_subseteq_singleton]) "HPiu".
    iModIntro.
    iDestruct "Hs" as ([γh γs]) "(Hn & Hs)".
    iDestruct (node_in_map with "Hn Hmaps") as %Hninm.
    iDestruct (node_in_state_sockets _ _ _ _ Hninm with "HlocS") as %[S Hsin].
    iDestruct (node_local_state with "[HlocS]") as "(Hloc & HlocS) ";
      first done; iFrame.
    iDestruct "Hloc" as (h' S' Hh Hs) "(Hn' & Hheap & Hsockets)".
    rewrite Hs in Hsin; simplify_eq; simpl.
    iDestruct (@gen_heap_valid with "Hsockets Hs") as %Hlookup.
    iDestruct (find_fixed_socket_interp with "Hf Hsicoh") as "#Haφ"; eauto.
    iSplit.
    - destruct (HPiu _ _ Hports) as [Q [Ha Hdisj]].
      iPureIntro; do 3 eexists; eapply SocketStepS; eauto.
      eapply (SocketBindSucS n sh a v S (state_ports_in_use σ1)
                             _ (state_lookup σ1)); try eauto.
      rewrite -(not_elem_of_dom (D:=gset socket_address)).
      rewrite elem_of_dom. eauto.
    - iIntros (v2 σ2 efs Hstep); inv_head_step.
      inversion SocketStep; simplify_eq.
      match goal with
      | H : S !! sh = _ |- _ =>
        rewrite H in Hlookup
      end; simplify_eq.
      iDestruct "Hms" as (seen rec [Hsockets_coh [Hrec_coh Hsent_coh]])
                           "(Hms & Hsent & Hrec & Hrecs & Hmsgs)". iFrame. iNext.
      iMod (gen_heap_update (H0 := gen_heap_soc_instance γs) with "Hsockets Hs")
        as "(Hsockets & Hs)".
      iMod (@gen_heap_alloc with "Hlookup")
        as "[Hlookup Hl]"; first done. iFrame.
      assert (HrecNone : rec !! a = None).
      { match goal with
          | H : state_lookup σ1 !! a = None |- _ => revert H
        end.
        rewrite -(not_elem_of_dom (D:=gset socket_address) (state_lookup σ1) a).
        by rewrite Hsockets_coh not_elem_of_dom. }
      iMod (@gen_heap_alloc _ _ _ _ _ _ rec a
                            (messages_received_at a (state_ms σ1)) with "Hrec")
        as "[Hrec [Hreca Hreca']]"; first done.
      iModIntro. iSplit=>//.
      iSplitR "HΦ Hl Hs Hn Hreca'".
      + iExists m. iFrame.
        iDestruct (map_local_state_i_update_sockets with "HlocS") as "HlocS".
        iDestruct (node_local_state_rev
                     with "[Hn' Hheap Hsockets] HlocS")
          as "HlocS"; first done.
        { iExists _,_. iFrame; repeat iSplit; iPureIntro; eauto; apply lookup_insert. }
        iFrame. iSplitR.
        { rewrite /local_state_coherence.
          rewrite (dom_insert_Some (D:=gset node) _ _ S) /= //. }
        iSplitR. iPureIntro. apply network_coherence_insert; done.
        iSplitL "Hsicoh".
        { iDestruct "Hsicoh" as (si fx Hdms) "(#Hfx & Hsi & Hsis)".
          iExists _, _; iFrame "#"; iFrame.
          iDestruct (ownF_agree with "Hf Hfx") as %?; subst A.
          iPureIntro.
          rewrite dom_insert_L Hdms.
          rewrite assoc_L (comm_L _ _ {[_]}) [ {[_]} ∪ _]subseteq_union_1_L;
            first done.
            by apply elem_of_subseteq_singleton. }
        iSplitL "HFip HPiu".
        { iExists _, _; iFrame. iPureIntro; repeat split.
          - assert (ip_of_address a ∈ dom (gset _) Piu).
            { rewrite elem_of_dom; eauto. }
            rewrite dom_insert. set_solver.
          - intros ip Hip.
            destruct (decide (ip = ip_of_address a)); subst.
            + exfalso; revert Hip. eapply elem_of_disjoint; eauto.
              apply elem_of_dom; eauto.
            + rewrite lookup_insert_ne //; by apply HFip.
          - intros ip Q.
            destruct (decide (ip = ip_of_address a)); subst.
            + rewrite lookup_insert => ?; simplify_eq.
              destruct (HPiu _ _ Hports) as [Q [Ha HQ]].
              match goal with
                Ha : state_ports_in_use σ1 !! ip_of_address a = Some _,
                Hb : state_ports_in_use σ1 !! ip_of_address a = Some _ |- _ =>
                rewrite Ha in Hb; simplify_eq
              end.
              exists ({[port_of_address a]} ∪ Q).
              rewrite lookup_insert; split; first done.
              set_solver.
            + rewrite !lookup_insert_ne //. apply HPiu. }
        * iExists seen,(<[a:=_]>rec). iSplitR. iPureIntro. split; simpl.
          -- by rewrite /messages_socket_coherence !dom_insert_L Hsockets_coh.
          -- split; last done. rewrite /messages_received_coherence. intros.
             destruct (decide (a = i)); subst.
             ++ by rewrite lookup_insert in H0; simplify_eq.
             ++ rewrite lookup_insert_ne in H0; last done.
                rewrite /messages_received_coherence in Hrec_coh.
                  by specialize (Hrec_coh i M' H0).
          -- iFrame. by rewrite big_sepM_insert; simpl; auto; iFrame.
      + iApply "HΦ". iExists _. iFrame; iFrame "#".
        iExists _; iFrame.
  Qed.

Lemma wp_bind_socket_dyn_suc n s A
      E sh v e (a : socket_address) (φ : socket_interp Σ) :
  IntoVal ⟨n;e⟩ 〈n;#a〉 →
  saddress v = None →
  a ∉ A →
  {{{ ▷ f↦ A ∗ ▷ FreePorts (ip_of_address a) {[port_of_address a]} ∗ ▷ sh s↦[n] v }}}
    ⟨n;SocketBind (Lit (LitSocket sh)) e⟩ @ s; E
  {{{ RET 〈n;LitV (LitInt 0)〉;
      ∃ g, sh s↦[n] {| sfamily := sfamily v;
                    stype := stype v;
                    sprotocol := sprotocol v;
                    saddress := Some a |} ∗
        a l↦ n ∗ a r↦{½} g ∗ a ⤇ φ
    }}}.
  Proof.
    iIntros (Hval Hnone Hafix Φ) "(>#HA & >Hip & >Hs) HΦ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1) "Hσ".
    iDestruct "Hσ" as (m Hlcoh Hncoh)
              "(Hsicoh & Hmaps & HlocS & Hlookup & Hips & Hms)".
    iDestruct "Hips" as (Fip Piu (Hdsj & HFip & HPiu)) "[HFip HPiu]".
    iMod (FreePorts_dealloc with "HPiu Hip")
      as (ports [Hports Hportsa%elem_of_subseteq_singleton]) "HPiu".
    iModIntro.
    iDestruct "Hs" as ([γh γs]) "(Hn & Hs)".
    iDestruct (node_in_map with "Hn Hmaps") as %Hninm.
    iDestruct (node_in_state_sockets _ _ _ _ Hninm with "HlocS") as %[S Hsin].
    iDestruct (node_local_state with "[HlocS]") as "(Hloc & HlocS) ";
      first done; iFrame.
    iDestruct "Hloc" as (h' S' Hh Hs) "(Hn' & Hheap & Hsockets)".
    rewrite Hs in Hsin; simplify_eq; simpl.
    iDestruct (@gen_heap_valid with "Hsockets Hs") as %Hlookup.
    iSplit.
    - destruct (HPiu _ _ Hports) as [Q [Ha Hdisj]].
      iPureIntro; do 3 eexists; eapply SocketStepS; eauto.
      apply to_base_val', ground_lang.of_to_val in Hval; simplify_eq.
      eapply (SocketBindSucS n sh a v S (state_ports_in_use σ1) _ (state_lookup σ1));
        eauto.
      rewrite -(not_elem_of_dom (D:=gset socket_address)).
      rewrite elem_of_dom; eauto.
    - iIntros (v2 σ2 efs Hstep); inv_head_step; inversion SocketStep.
      apply to_base_val' in Hval. simpl in *.
      apply ground_lang.of_to_val in Hval. simpl in *.
      match goal with
      | H : (#?Z)%E = e |- _ =>
        assert (Z = a) by congruence
      end; simplify_eq.
      iDestruct "Hms" as (seen rec [Hsockets_coh [Hrec_coh Hsent_coh]])
                           "(Hms & Hsent & Hrec & Hrecs & Hmsgs)".
      iFrame. iNext.
      iMod (gen_heap_update (H0 := gen_heap_soc_instance γs) with "Hsockets Hs")
        as "(Hsockets & Hs)".
      iMod (@gen_heap_alloc with "Hlookup")
        as "[Hlookup Hl]"; first done. iFrame.
      rewrite /socket_interp_coherence.
      iDestruct "Hsicoh" as (si fx Hdms) "(#Hfix & Hsi & #Hall)".
      iDestruct (ownF_agree with "HA Hfix") as %?; subst.
      assert (Hnotin': si !! a = None).
      { rewrite -(not_elem_of_dom (D:=(gset socket_address))) Hdms not_elem_of_union;
          split; try done. by rewrite not_elem_of_dom. }
      iMod (saved_pred_alloc φ) as (γsi) "#Hsipred".
      iMod (own_update _ _ (● <[a:=(to_agree γsi)]>si ⋅ ◯ {[ a:=(to_agree γsi)]})
              with "Hsi") as "[Hsi #Hsip]".
      { apply auth_update_alloc.
          by apply (alloc_singleton_local_update si). }
      simpl.
      assert (HrecNone : rec !! a = None).
      { revert H15.
        rewrite -(not_elem_of_dom (D:=gset socket_address) (state_lookup σ1) a).
        by rewrite Hsockets_coh not_elem_of_dom. }
      iMod (@gen_heap_alloc _ _ _ _ _ _ rec a
                            (messages_received_at a (state_ms σ1)) with "Hrec")
        as "[Hrec [Hreca Hreca']]"; first done.
      iModIntro. iSplit=>//.
      iSplitR "HΦ Hl Hs Hn Hreca'".
      + iExists m. iFrame.
        iDestruct (map_local_state_i_update_sockets with "HlocS") as "HlocS".
        iDestruct (node_local_state_rev
                     with "[Hn' Hheap Hsockets] HlocS")
          as "HlocS"; first done.
        { iExists _,_. iFrame; repeat iSplit; iPureIntro; eauto; apply lookup_insert. }
        iFrame. iSplitR. iPureIntro.
        { rewrite /local_state_coherence.
          rewrite (dom_insert_Some (D:=gset node) _ _ S) /= //. }
        iSplitR. iPureIntro. apply network_coherence_insert; done.
        iSplitL "Hsi Hall".
        iExists (<[a:=(to_agree γsi)]>si), _; iFrame. iSplitR. iPureIntro. simpl.
        by rewrite !dom_insert_L Hdms !union_assoc_L (union_comm_L _ {[a]})
                   -!union_assoc_L.
        rewrite dom_insert_L big_sepS_insert.
        iFrame; iFrame "#". iExists _, _; iFrame "#".
        { by rewrite not_elem_of_dom. }
        iSplitL "HFip HPiu".
        { iExists _, _; iFrame. iPureIntro; repeat split.
          - assert (ip_of_address a ∈ dom (gset _) Piu).
            { rewrite elem_of_dom; eauto. }
            rewrite dom_insert. set_solver.
          - intros ip Hip.
            destruct (decide (ip = ip_of_address a)); subst.
            + exfalso; revert Hip. eapply elem_of_disjoint; eauto.
              apply elem_of_dom; eauto.
            + rewrite lookup_insert_ne //; by apply HFip.
          - intros ip Q.
            destruct (decide (ip = ip_of_address a)); subst.
            + rewrite lookup_insert => ?; simplify_eq.
              destruct (HPiu _ _ Hports) as [Q [Ha HQ]].
              match goal with
                Ha : state_ports_in_use σ1 !! ip_of_address a = Some _,
                Hb : state_ports_in_use σ1 !! ip_of_address a = Some _ |- _ =>
                rewrite Ha in Hb; simplify_eq
              end.
              exists ({[port_of_address a]} ∪ Q).
              rewrite lookup_insert; split; first done.
              set_solver.
            + rewrite !lookup_insert_ne //. apply HPiu. }
        iExists seen,(<[a:=_]>rec). iSplitR. iPureIntro. split; simpl.
          -- by rewrite /messages_socket_coherence !dom_insert_L Hsockets_coh.
          -- split; last done. rewrite /messages_received_coherence. intros.
             destruct (decide (a = i)); subst.
             ++ by rewrite lookup_insert in H0; simplify_eq.
             ++ rewrite lookup_insert_ne in H0; last done.
                rewrite /messages_received_coherence in Hrec_coh.
                  by specialize (Hrec_coh i M' H0).
          -- iFrame. rewrite big_sepM_insert //=. by iFrame.
      + iApply "HΦ". iExists _. iFrame. iSplitL "Hn Hs".
        iExists _; iFrame.
        rewrite H2 in Hlookup. simplify_eq. iFrame.
        iExists _. iFrame; iFrame "#".
  Qed.

  Lemma wp_send_to_bound (P Q : iProp Σ) φ
        (m : message_body) sh
        (a f : socket_address)
        n s E v π e1 e2 :
    IntoVal ⟨n;e1⟩ 〈n;#m〉 →
    IntoVal ⟨n;e2⟩ 〈n;#a〉 →
    saddress v = Some f ->
    let msg M := {| m_from_node := n;
                    m_sender := f;
                    m_destination := a;
                    m_protocol := sprotocol v;
                    m_state := MS_SENT;
                    m_sent := max_sent M;
                    m_received := 0;
                    m_body := m; |} in
    {{{ ▷ sh s↦[n]{π} v ∗ ▷ P ∗ a ⤇ φ ∗
        (∀ M sent mId,
           message_soup_info M sent ∗
           mId o↦ (message_stable_from_message (msg M)) ∗ P ={E}=∗
           message_soup_info M sent ∗
           ▷ φ (message_stable_from_message (msg M)) ∗ Q
          )}}}
      ⟨n;SendTo (Lit (LitSocket sh)) e1 e2⟩ @ s; E
    {{{ RET 〈n;LitV (LitInt (String.length m))〉;
        sh s↦[n]{π} v ∗ Q
    }}}.
  Proof.
    iIntros (Heq1%of_to_val Heq2%of_to_val Hsome Hmsg);
      inversion Heq1; inversion Heq2; simplify_eq;
        clear Heq1 Heq2; simpl.
    iIntros (Φ) "(>Hsocket & Hp & #Hsip & Hvs) HΦ"; simpl.
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1) "Hσ !>".
    iDestruct "Hσ" as (γmap Hlcoh Hncoh)
                        "(Hsi & Hmaps & HlocS & Hlookup & Hips & Hms)".
    iDestruct "Hsocket" as ([γh γs]) "(Hn & Hs)".
    iDestruct (node_in_map with "Hn Hmaps") as %Hninm.
    iDestruct (node_in_state_sockets _ _ _ _ Hninm with "HlocS") as %[S Hnins].
    iDestruct (node_local_state with "[HlocS]") as "(Hloc & HlocS) ";
      first done; iFrame.
    iDestruct "Hloc" as (h' S' Hheaps Hsockets) "(Hmap & Hheap & Hsockets)".
    rewrite Hsockets in Hnins; simplify_eq; simpl.
    iDestruct (@gen_heap_valid with "Hsockets Hs") as %Hv.
    iSplitR.
    { iPureIntro; do 3 eexists; eapply SocketStepS; eauto.
      eapply message_send_bound_fresh; eauto. }
    iIntros (v2' σ2 efs Hstep); inv_head_step;
      inversion SocketStep; iSplitR; auto; subst. iNext.
    iDestruct (message_state_later with "Hms") as "Hms".
    iMod (messages_insert _ _ mId {|
                         m_from_node := n;
                         m_sender := f;
                         m_destination := a0;
                         m_protocol := sprotocol s0;
                         m_body := mbody;
                         m_state := MS_SENT;
                         m_sent := (max_sent (state_ms σ1) + 1)%nat;
                         m_received := 0 |}  with "Hms") as "(HmId & Hstable & Hms)";
      try done.
    repeat match goal with
           | H : ground_lang.to_val _ = Some _ |- _ =>
             apply ground_lang.of_to_val in H; cbv in H
           end; simplify_eq.
    iSimplifyEq. rewrite H3 in Hv. inversion Hv as [Heq].
    rewrite Heq Hsome in H5. inversion H5 as [Heq']. rewrite -Heq'.
    iDestruct "Hms" as (sent rec [Hsoccoh [Hreccoh Hsentcoh]])
                         "(Hms & Hsent & Hrec & Hrecs & Hmsgs)".
    iMod ("Hvs" $! _ _ mId
            with "[$Hms $Hsent Hstable $Hp]")
      as "((_ & Hms & Hsent) & Hsipred & HQ)".
    { iSplitR; first done.
      by rewrite /Hmsg /max_sent map_size_insert //= Nat.add_1_r. }
    iFrame. iSplitR "HΦ HQ Hn Hs".
    - iModIntro. iExists γmap. iFrame. iSplitR.
      { rewrite /local_state_coherence.
        rewrite (dom_insert_Some (D:=gset node) _ _ S') /= //. } iSplitR; auto.
      iDestruct (node_local_state_rev with "[Hmap Hheap Hsockets] HlocS")
        as "HlocS"; first done. iExists _,_. iFrame. auto.
      rewrite /local_state_i /= insert_id //. iFrame.
      iExists _,_. iFrame. iSplitR. auto. iSplitL "Hrecs".
      rewrite big_sepM_mono //.
      iIntros (k x Hl) "(% & H)". iFrame. by rewrite messages_received_id.
      rewrite big_sepM_insert //. iFrame. iExists 1%Qp,φ. iFrame. iRight.
      rewrite /Hmsg /=. iFrame; iFrame "#". iSplit; first done.
      rewrite max_sent_insert //.
    - iModIntro. simpl.
      iApply "HΦ"; iFrame. by iExists _; iFrame.
    - iSimplifyEq. rewrite H3 in Hv. inversion Hv as [Heq].
      rewrite Heq Hsome in H5. inversion H5 as [Heq'].
  Qed.

  Lemma wp_send_to_unbound (P Q : iProp Σ) φ
        (m : message_body)
        (a : socket_address)
        n s E sh v π e1 e2 ip :
    IntoVal ⟨n;e1⟩ 〈n;#m〉 →
    IntoVal ⟨n;e2⟩ 〈n;#a〉 →
    saddress v = None ->
    let msg M f := {| m_from_node := n;
                    m_sender := f;
                    m_destination := a;
                    m_protocol := sprotocol v;
                    m_state := MS_SENT;
                    m_sent := max_sent M;
                    m_received := 0;
                    m_body := m; |} in
    {{{ ▷ sh s↦[n]{π} v ∗ ▷ P ∗ a ⤇ φ ∗ FreePorts ip ∅ ∗
        (∀ M sent mId f,
           message_soup_info M sent ∗
           mId o↦ (message_stable_from_message (msg M f)) ∗ P ={E}=∗
           message_soup_info M sent ∗
           ▷ φ (message_stable_from_message (msg M f)) ∗ Q
          )}}}
      ⟨n;SendTo (Lit (LitSocket sh)) e1 e2⟩ @ s; E
    {{{ RET 〈n;LitV (LitInt (String.length m))〉;
        sh s↦[n]{π} v ∗ Q
    }}}.
  Proof.
    iIntros (Heq1%of_to_val Heq2%of_to_val Hnone Hmsg);
      inversion Heq1; inversion Heq2; simplify_eq;
        clear Heq1 Heq2; simpl.
    iIntros (Φ) "(>Hsocket & Hp & #Hsip & Hfp & Hvs) HΦ"; simpl.
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1) "Hσ !>".
    iDestruct "Hσ" as (γmap Hlcoh Hncoh)
                        "(Hsi & Hmaps & HlocS & Hlookup & Hips & Hms)".
    iDestruct "Hips" as (Fip Piu (Hdsj & HFip & HPiu)) "[HFip HPiu]".
    iDestruct (FreePorts_included with "HPiu Hfp") as %[Prts [Hprts _]].
    destruct (HPiu _ _ Hprts) as [Prts' [Hptrs' Hdsj']].
    iDestruct "Hsocket" as ([γh γs]) "(Hn & Hs)".
    iDestruct (node_in_map with "Hn Hmaps") as %Hninm.
    iDestruct (node_in_state_sockets _ _ _ _ Hninm with "HlocS") as %[S Hnins].
    iDestruct (node_local_state with "[HlocS]") as "(Hloc & HlocS) ";
      first done; iFrame.
    iDestruct "Hloc" as (h' S' Hheaps Hsockets) "(Hmap & Hheap & Hsockets)".
    rewrite Hsockets in Hnins; simplify_eq; simpl.
    iDestruct (@gen_heap_valid with "Hsockets Hs") as %Hv.
    iSplitR.
    { iPureIntro. do 3 eexists; eapply SocketStepS; eauto.
      eapply message_send_unbound_fresh; eauto.
      rewrite -(not_elem_of_dom (D:=gset socket_address)).
      rewrite elem_of_dom.
      intros Hfalse.
      apply (is_fresh Prts').
      eapply (Hncoh _ Prts' Hfalse); eauto. }
    iIntros (v2' σ2 efs Hstep); inv_head_step;
      inversion SocketStep; iSplitR; auto; subst; iNext.
    { iSimplifyEq; rewrite H3 in Hv; inversion Hv as [Heq].
      rewrite Heq Hnone in H5. inversion H5. }
    iDestruct (message_state_later with "Hms") as "Hms".
    iMod (messages_insert _ _ mId {|
                         m_from_node := n;
                         m_sender := f;
                         m_destination := a0;
                         m_protocol := sprotocol s0;
                         m_body := mbody;
                         m_state := MS_SENT;
                         m_sent := (max_sent (state_ms σ1) + 1)%nat;
                         m_received := 0 |}  with "Hms") as "(HmId & Hstable & Hms)";
      try done.
    repeat match goal with
           | H : ground_lang.to_val _ = Some _ |- _ =>
             apply ground_lang.of_to_val in H; cbv in H
           end; simplify_eq.
    iSimplifyEq; rewrite H3 in Hv; inversion Hv as [Heq].
    iDestruct "Hms" as (sent rec [Hsoccoh [Hreccoh Hsentcoh]])
                         "(Hms & Hsent & Hrec & Hrecs & Hmsgs)".
    iMod ("Hvs" $! _ _ mId f
            with "[$Hms $Hsent Hstable $Hp]")
      as "((_ & Hms & Hsent) & Hsipred & HQ)".
    { iSplitR; first done.
      by rewrite /Hmsg /max_sent map_size_insert //= Nat.add_1_r. }
    iFrame. iSplitR "HΦ HQ Hn Hs".
    - iModIntro. iExists γmap. iFrame. iSplitR.
      { rewrite /local_state_coherence.
        rewrite (dom_insert_Some (D:=gset node) _ _ S') /= //. } iSplitR; auto.
      iDestruct (node_local_state_rev with "[Hmap Hheap Hsockets] HlocS")
        as "HlocS"; first done. iExists _,_. iFrame. auto.
      rewrite /local_state_i /= insert_id //. iFrame.
      iSplitL "HFip HPiu".
      { iExists _, _; iFrame; eauto. }
      iExists _,_. iFrame. iSplitR. done. iSplitL "Hrecs".
      rewrite big_sepM_mono //.
      iIntros (k x Hl) "(% & H)". iFrame. by rewrite messages_received_id.
      rewrite big_sepM_insert //. iFrame. iExists 1%Qp,φ. iFrame. iRight.
      rewrite /Hmsg /=. iFrame; iFrame "#". iSplit; first done.
      rewrite max_sent_insert //.
    - iModIntro. simpl.
      iApply "HΦ"; iFrame. by iExists _; iFrame.
  Qed.

  Definition received_message_info a m :=
    m_destination m = a ∧ m_state m = MS_RECEIVED.

  Lemma wp_receive_from n s a E sh v π rm :
    saddress v = Some a →
    {{{ ▷ sh s↦[n]{π} v ∗ ▷ a r↦{½} rm }}}
      ⟨n;ReceiveFrom (Lit (LitSocket sh))⟩ @ s; E
    {{{ r, RET 〈n;r〉; ∃ rm',
        sh s↦[n]{π} v ∗ a r↦{½} rm' ∗
        ((∃ mId m φ, ⌜received_message_info a m⌝ ∗
                     ⌜r = SOMEV (PairV (LitV $ LitString (m_body m))
                                       (LitV $ LitSocketAddress (m_sender m)))⌝ ∗
                     ⌜rm' = <[mId:=m]>rm⌝ ∗
                     mId m↦{¾} m ∗ a ⤇ φ ∗ φ (message_stable_from_message m)) ∨
        (⌜r = NONEV⌝ ∗ ⌜rm' = rm⌝))
    }}}.
  Proof.
    iIntros (Hla Φ) "(>Hs & >Ha) HΦ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros (σ1) "Hσ !>".
    iDestruct "Hσ" as (γmap Hlcoh Hncoh)
                        "(Hsi & Hmaps & HlocS & Hlookup & Hips & Hms)".
    iDestruct "Hs" as ([γh γs]) "(Hn & Hs)".
    iDestruct (node_in_map with "Hn Hmaps") as %Hninm.
    iDestruct (node_in_state_sockets _ _ _ _ Hninm with "HlocS") as %[S Hnins].
    iDestruct (node_local_state with "[HlocS]") as "(Hloc & HlocS) ";
      first done; iFrame.
    iDestruct "Hloc" as (h' S' Hheap Hsocket) "(Hn' & Hheap & Hsockets)".
    rewrite Hsocket in Hnins; simplify_eq; simpl.
    iDestruct (@gen_heap_valid with "Hsockets Hs") as %Hsh.
    destruct (decide (messages_to_receive_at a (state_ms σ1) = ∅)); simplify_eq;
      iSplitR.
    - iPureIntro; do 3 eexists; eapply SocketStepS; eauto.
        by eapply ReceiveFromNoneS.
    - iNext; iIntros (v2' σ2 efs Hstep); inv_head_step;
        inversion SocketStep; iSplitR; auto; subst.
      { rewrite Hsh in H1. simplify_eq. rewrite e lookup_empty in H3. inversion H3. }
      iModIntro. iSplitR "HΦ Hs Hn Ha"; iFrame.
      iExists γmap.
      iDestruct (node_local_state_rev with "[Hn' Hheap Hsockets] HlocS")
        as "HX"; first done.
      { iExists h', S'. iFrame; by iPureIntro. }
      iDestruct (message_state_later with "Hms") as "Hms".
      rewrite insert_id //=. by iFrame.
      iApply "HΦ". iExists _. iFrame. iSplitL. iExists _. iFrame. by iRight.
    - apply map_choose in n0. destruct n0 as [mId [m Hm]].
      iPureIntro; do 3 eexists; eapply SocketStepS; eauto.
        by eapply ReceiveFromSomeS.
    - iDestruct "Hms" as (sent rec [Hmsgsi [Hrec Hsent]])
                           "(Hms & Hsent & Hrec & Hrecs & Hmsg)".
      iDestruct (@gen_heap_valid with "Hrec Ha") as %Hreca.
      iDestruct (big_sepM_delete _ rec with "Hrecs") as "([% Hreca] & Hrecs)";
        first done. iCombine "Ha" "Hreca" as "Ha".
      iNext; iIntros (v2' σ2 efs Hstep); inv_head_step;
        inversion SocketStep; iSplitR; auto; subst.
      +  rewrite H1 in Hsh; simplify_eq.
         iMod (gen_heap_update rec a _ (<[mId:={|
                         m_from_node := m_from_node m;
                         m_sender := m_sender m;
                         m_destination := m_destination m;
                         m_protocol := m_protocol m;
                         m_body := m_body m;
                         m_state := MS_RECEIVED;
                         m_sent := m_sent m;
                         m_received := max_received (state_ms σ1) + 1 |}]>
                                     (messages_received_at a (state_ms σ1)))
                 with "Hrec Ha") as "(Hrec & [Ha Ha'])".
         revert H3. rewrite map_filter_lookup_Some.
         intros [Hlookup [Hp1 Hp2]]; simpl in *; subst.
         iMod (messages_update_received
                   (state_ms σ1) mId _
                   {|
                     m_from_node := m_from_node m;
                     m_sender := m_sender m;
                     m_destination := m_destination m;
                     m_protocol := m_protocol m;
                     m_body := m_body m;
                     m_state := MS_RECEIVED;
                     m_sent := m_sent m;
                     m_received := max_received (state_ms σ1) + 1 |}
                 with "[Hms Hmsg]")
           as (φ) "(Hsi' & Hp & Hms & Hmsg)"; try done; iFrame.
         iDestruct (message_sepM_later with "Hmsg") as "Hmsg"; iFrame.
         iSplitR "HΦ Hs Hn Hsi' Hp Ha'"; iFrame.
         * iExists γmap. iFrame. iSplitR.
           { rewrite /local_state_coherence.
             rewrite (dom_insert_Some (D:=gset node) _ _ S') /= //. }
           { iSplitR; auto.
             iDestruct (node_local_state_rev with "[Hn' Hheap Hsockets] HlocS")
               as "HlocS"; first done.
             { iExists h', S'. iFrame; by iPureIntro. }
             rewrite (insert_id (state_sockets σ1)); last done. iFrame.
             iExists _,_. iFrame. iSplitR. iPureIntro.
             rewrite /messages_coherence /messages_socket_coherence. auto. split.
             { rewrite /messages_socket_coherence in Hmsgsi.
             rewrite Hmsgsi -(insert_id rec (m_destination m)
                                        (messages_received_at (m_destination m)
                                                              (state_ms σ1))).
             rewrite !dom_insert_L. set_solver. done. }
           split. unfold messages_received_coherence, messages_received_at in *.
           intros i M'.
           rewrite lookup_insert_Some. intros [[Heq Hinsert] | [Hneq Hlook]].
           - rewrite -Hinsert -map_filter_lookup_insert Heq //.
           - rewrite map_filter_lookup_None_insert. by apply Hrec.
             rewrite map_filter_lookup_None. right. intros; simplify_eq.
             intros [Hh1 Hh2]; simpl in *. rewrite Hp2 in Hh2. inversion Hh2.
             intros [Hh1 Hh2]. simpl in *. by destruct Hneq.
           - rewrite /messages_sent_coherence //=. split.
             rewrite (dom_insert_Some (state_ms σ1) mId m) //=. by apply Hsent.
             destruct Hsent as [Hsent1 Hsent2].
             intros. destruct (decide (mId = mId0)); trivial; subst.
             + destruct m; simpl in *. specialize (Hsent2 mId0).
             rewrite lookup_insert Hsent2 Hlookup Hp2
                     /message_stable_from_message //=.
             + rewrite lookup_insert_ne //=.
           - iFrame.
             iDestruct (messages_received_at_update with "Hrecs Ha") as "Hx";
               auto; try done.
             intro. rewrite Hp2 //= in H0; done. }
         * iApply "HΦ". iModIntro.
           iExists _. iFrame. iSplitL "Hs Hn". iExists _. iFrame.
           iLeft. iExists mId,{|
              m_from_node := m_from_node m;
              m_sender := m_sender m;
              m_destination := m_destination m;
              m_protocol := m_protocol m;
              m_body := m_body m;
              m_state := MS_RECEIVED;
              m_sent := m_sent m;
              m_received := max_received (state_ms σ1) + 1 |},φ.
           iFrame. iSplitR; first done. iSplitR. iPureIntro; first done.
           iSplitR; first done.
           rewrite /message_stable_from_message Hp2 /=. iFrame.
      + rewrite H1 in Hsh; simplify_eq.
  Qed.

End lifting.
