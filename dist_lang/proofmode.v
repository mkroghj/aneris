From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.proofmode Require Import coq_tactics.
From iris.proofmode Require Export tactics.
From distris Require Export tactics lifting network.
Set Default Proof Using "Type".
Import uPred.

Lemma tac_wp_expr_eval `{distG Σ} Δ s E Φ e e' :
  (∀ (e'':=e'), e = e'') →
  envs_entails Δ (WP e' @ s; E {{ Φ }}) → envs_entails Δ (WP e @ s; E {{ Φ }}).
Proof. by intros ->. Qed.

Tactic Notation "wp_expr_eval" tactic(t) :=
  try (
    iStartProof;
    first [eapply tac_wp_expr_eval];
      [let x := fresh in intros x; t; unfold x; reflexivity
      |]).

Ltac wp_expr_simpl := wp_expr_eval simpl.
Ltac wp_expr_simpl_subst := wp_expr_eval simpl_subst.

Lemma tac_wp_pure `{distG Σ} Δ Δ' s E e1 e2 φ Φ :
  PureExec φ e1 e2 →
  φ →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_entails Δ' (WP e2 @ s; E {{ Φ }}) →
  envs_entails Δ (WP e1 @ s; E {{ Φ }}).
Proof.
  rewrite /envs_entails=> ??? HΔ'. rewrite into_laterN_env_sound /=.
  rewrite HΔ' -lifting.wp_pure_step_later //.
Qed.

Lemma tac_wp_value `{distG Σ} Δ s E Φ e v :
  IntoVal e v →
  envs_entails Δ (Φ v) → envs_entails Δ (WP e @ s; E {{ Φ }}).
Proof. rewrite /envs_entails=> ? ->. by apply wp_value. Qed.

Ltac wp_value_head :=
  first [eapply tac_wp_value];
  [(solve_into_val || by apply to_base_val_inv)
    |iEval (rewrite /=;lazy beta; simpl of_val)].

Tactic Notation "wp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ⟨?n;?e⟩ ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
                           unify e' efoc;
      eapply (tac_wp_pure _ _ _ _ (fill K ⟨n;e'⟩));
      [apply _                        (* PureExec *)
      |try fast_done                  (* The pure condition for PureExec *)
      |apply _                        (* IntoLaters *)
      |wp_expr_simpl_subst; try wp_value_head (* new goal *)
      ]
                       )
    || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | _ => fail "wp_pure: not a 'wp'"
  end.

Tactic Notation "wp_if" := wp_pure (If _ _ _).
Tactic Notation "wp_if_true" := wp_pure (If (Lit (LitBool true)) _ _).
Tactic Notation "wp_if_false" := wp_pure (If (Lit (LitBool false)) _ _).
Tactic Notation "wp_find_from" := wp_pure (FindFrom _ _ _ ).
Tactic Notation "wp_substring" := wp_pure (Substring _ _ _).
Tactic Notation "wp_unop" := wp_pure (UnOp _ _).
Tactic Notation "wp_binop" := wp_pure (BinOp _ _ _).
Tactic Notation "wp_op" := wp_unop || wp_binop.
Tactic Notation "wp_rec" := wp_pure (App _ _).
Tactic Notation "wp_lam" := wp_rec.
Tactic Notation "wp_let" := wp_lam.
Tactic Notation "wp_seq" := wp_lam.
Tactic Notation "wp_proj" := wp_pure (Fst _) || wp_pure (Snd _).
Tactic Notation "wp_case" := wp_pure (Case _ _ _).
Tactic Notation "wp_match" := wp_case; wp_let.
Tactic Notation "wp_makeaddress" := wp_pure (MakeAddress _ _).

Lemma tac_wp_bind `{distG Σ} K Δ s E Φ n (e : ground_lang.expr) f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (WP ⟨n;e⟩ @ s; E {{ v, WP f (of_val v) @ s; E {{ Φ }} }})%I →
  envs_entails Δ (WP fill K ⟨n;e⟩ @ s; E {{ Φ }}).
Proof. rewrite /envs_entails=> -> ->. apply: wp_bind. Qed.

Ltac wp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_wp_bind K); [simpl; reflexivity|lazy beta]
  end.

Tactic Notation "wp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ⟨_;?e⟩ ?Q) =>
    reshape_expr e ltac:(fun K e' => unify e' efoc; wp_bind_core K)
  | _ => fail "wp_bind: not a 'wp'"
  end.

(** Heap and socket tactics *)
Section state.
Context `{distG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (iResUR Σ).

Lemma wp_atomic' s E1 E2 e Φ `{!Atomic (stuckness_to_atomicity s) e} :
  (|={E1,E2}=> WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros "H". iApply (wp_atomic with "[H]"); iFrame.
Qed.

Global Instance elim_modal_fupd_wp_atomic' s E1 E2 e P Φ :
  Atomic (stuckness_to_atomicity s) e →
  ElimModal (|={E1,E2}=> P) P
            (WP e @ s; E1 {{ Φ }}) (WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }})%I.
Proof. intros. by rewrite /ElimModal fupd_frame_r wand_elim_r wp_atomic'. Qed.

Lemma tac_wp_alloc Δ Δ' s E i j K n γ's e v Φ :
  IntoVal ⟨n;e⟩ 〈n;v〉 →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, n n↦ γ's)%I →
  (∀ l, ∃ Δ'',
    envs_app false (Esnoc Enil j (l ↦[n] v)) Δ' = Some Δ'' ∧
    envs_entails Δ'' (WP fill K ⟨n; Lit (LitLoc l)⟩ @ s; E {{ Φ }})) →
  envs_entails Δ (WP fill K ⟨n;Alloc e⟩ @ s; E {{ Φ }}).
Proof.
  rewrite /envs_entails=> ?? Hn HΔ.
  rewrite -wp_bind.
  iIntros "H".
  rewrite into_laterN_env_sound /=.
  iDestruct (envs_lookup_split _ _  with "H") as "[Hn H]"; eauto.
  simpl. iDestruct "Hn" as "#Hn".
  iApply (wp_alloc with "Hn").
  iNext.
  iIntros (l) "Hl".
  destruct (HΔ l) as (Δ''&?&HΔ').
  rewrite envs_app_sound //; simpl.
  rewrite right_id HΔ'.
  by iApply "H".
Qed.

Lemma tac_wp_load Δ Δ' s E i K n l q v Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦[n]{q} v)%I →
  envs_entails Δ' (WP fill K (of_val 〈n;v〉) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K ⟨n;Load (Lit (LitLoc l))⟩ @ s; E {{ Φ }}).
Proof.
  rewrite /envs_entails=> ???.
  rewrite -wp_bind. eapply wand_apply; first exact: wp_load.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  by apply later_mono, sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_store Δ Δ' Δ'' s E i K n l v e v' Φ :
  IntoVal ⟨n;e⟩ 〈n;v'〉 →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦[n] v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦[n] v')) Δ' = Some Δ'' →
  envs_entails Δ'' (WP fill K ⟨n;Lit LitUnit⟩ @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K ⟨n;Store (Lit (LitLoc l)) e⟩ @ s; E {{ Φ }}).
Proof.
  rewrite /envs_entails=> ?????.
  rewrite -wp_bind. eapply wand_apply; first by eapply wp_store.
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.

(* Lemma tac_wp_cas_fail Δ Δ' s E i K l q v e1 v1 e2 Φ : *)
(*   IntoVal e1 v1 → AsVal e2 → *)
(*   MaybeIntoLaterNEnvs 1 Δ Δ' → *)
(*   envs_lookup i Δ' = Some (false, l ↦{q} v)%I → v ≠ v1 → *)
(*   envs_entails Δ' (WP fill K (Lit (LitBool false)) @ s; E {{ Φ }}) → *)
(*   envs_entails Δ (WP fill K (CAS (Lit (LitLoc l)) e1 e2) @ s; E {{ Φ }}). *)
(* Proof. *)
(*   rewrite /envs_entails=> ??????. *)
(*   rewrite -wp_bind. eapply wand_apply; first exact: wp_cas_fail. *)
(*   rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl. *)
(*   by apply later_mono, sep_mono_r, wand_mono. *)
(* Qed. *)

(* Lemma tac_wp_cas_suc Δ Δ' Δ'' s E i K l v e1 v1 e2 v2 Φ : *)
(*   IntoVal e1 v1 → IntoVal e2 v2 → *)
(*   MaybeIntoLaterNEnvs 1 Δ Δ' → *)
(*   envs_lookup i Δ' = Some (false, l ↦ v)%I → v = v1 → *)
(*   envs_simple_replace i false (Esnoc Enil i (l ↦ v2)) Δ' = Some Δ'' → *)
(*   envs_entails Δ'' (WP fill K (Lit (LitBool true)) @ s; E {{ Φ }}) → *)
(*   envs_entails Δ (WP fill K (CAS (Lit (LitLoc l)) e1 e2) @ s; E {{ Φ }}). *)
(* Proof. *)
(*   rewrite /envs_entails=> ???????; subst. *)
(*   rewrite -wp_bind. eapply wand_apply; first exact: wp_cas_suc. *)
(*   rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl. *)
(*   rewrite right_id. by apply later_mono, sep_mono_r, wand_mono. *)
(* Qed. *)

(* Lemma tac_wp_faa Δ Δ' Δ'' s E i K l i1 e2 i2 Φ : *)
(*   IntoVal e2 (LitV (LitInt i2)) → *)
(*   MaybeIntoLaterNEnvs 1 Δ Δ' → *)
(*   envs_lookup i Δ' = Some (false, l ↦ LitV (LitInt i1))%I → *)
(*   envs_simple_replace i false (Esnoc Enil i (l ↦ LitV (LitInt (i1 + i2)))) Δ' = Some Δ'' → *)
(*   envs_entails Δ'' (WP fill K (Lit (LitInt i1)) @ s; E {{ Φ }}) → *)
(*   envs_entails Δ (WP fill K (FAA (Lit (LitLoc l)) e2) @ s; E {{ Φ }}). *)
(* Proof. *)
(*   rewrite /envs_entails=> ?????; subst. *)
(*   rewrite -wp_bind. eapply wand_apply; first exact: (wp_faa _ _ _ i1 _ i2). *)
(*   rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl. *)
(*   rewrite right_id. by apply later_mono, sep_mono_r, wand_mono. *)
(* Qed. *)

Lemma tac_wp_socket Δ Δ' s E i j K n γ's e1 v1 e2 v2 e3 v3 Φ :
  IntoVal ⟨n;e1⟩ 〈n;#(LitAddressFamily v1)〉 →
  IntoVal ⟨n;e2⟩ 〈n;#(LitSocketType v2)〉 →
  IntoVal ⟨n;e3⟩ 〈n;#(LitProtocol v3)〉 →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, n n↦ γ's)%I →
  (∀ h, ∃ Δ'',
        envs_app false (Esnoc Enil j (h s↦[n] {|
                                          Network.sfamily := v1;
                                          Network.stype := v2;
                                          Network.sprotocol := v3;
                                          Network.saddress := None |}))
                 Δ' = Some Δ'' ∧
    envs_entails Δ'' (WP fill K ⟨n; Lit (LitSocket h)⟩ @ s; E {{ Φ }})) →
  envs_entails Δ (WP fill K ⟨n;NewSocket e1 e2 e3⟩ @ s; E {{ Φ }}).
Proof.
  rewrite /envs_entails=> ???? Hn HΔ.
  rewrite -wp_bind.
  iIntros "H".
  rewrite into_laterN_env_sound /=.
  iDestruct (envs_lookup_split with "H") as "[Hn H]"; eauto.
  simpl. iDestruct "Hn" as "#Hn".
  iApply (wp_new_socket with "Hn").
  iNext.
  iIntros (sh) "Hsh".
  destruct (HΔ sh) as (Δ''&?&HΔ').
  rewrite envs_app_sound //; simpl.
  rewrite right_id HΔ'.
  by iApply "H".
Qed.

(* Lemma tac_wp_socket_bind_suc Δ Δ' Δ'' s E i i' i'' j K n (P : coPset) *)
(*       layout sh v e v' Φ : *)
(*   IntoVal ⟨n;e⟩ 〈n;#(LitSocketAddress v')〉 → *)
(*   MaybeIntoLaterNEnvs 1 Δ Δ' → *)
(*   Network.saddress v = None → *)
(*   layout !! n = Some (Network.ip_of_address v') → *)
(*   Network.port_of_address v' ∈ P → *)
(*   envs_lookup i Δ' = Some (false, ownN dist_layout_name layout) → *)
(*   envs_lookup i' Δ' = Some (false, p↦[n] P) → *)
(*   envs_lookup i'' Δ' = Some (false, sh s↦[n] v)%I → *)
(*   envs_simple_replace i' false *)
(*                       (Esnoc Enil i' (p↦[ n] (P ∖ {[Network.port_of_address v']})))                 Δ' = Some Δ'' → *)
(*   envs_simple_replace i'' false (Esnoc Enil i'' (sh s↦[n] {| *)
(*                                           Network.sfamily := Network.sfamily v; *)
(*                                           Network.stype := Network.stype v; *)
(*                                           Network.sprotocol := Network.sprotocol v; *)
(*                                           Network.saddress := Some v' |})) *)
(*                       Δ' = Some Δ'' → *)
(*   envs_app false (Esnoc Enil j (v' l↦ n)) Δ' = Some Δ'' →  *)
(*   envs_entails Δ'' (WP fill K ⟨n;Lit $ LitInt 0⟩ @ s; E {{ Φ }}) → *)
(*   envs_entails Δ (WP fill K ⟨n;SocketBind (Lit (LitSocket sh)) e⟩ @ s; E {{ Φ }}). *)
(* Proof. *)
(*   rewrite /envs_entails=> ????????????. *)
(*   rewrite -wp_bind. eapply wand_apply. by eapply wp_bind_socket_suc.  *)
(*   rewrite !into_laterN_env_sound -!later_sep. *)
(*   rewrite envs_simple_replace_sound //; simpl. *)
(*   rewrite (envs_simple_replace_sound _ _ i'). *)
(*   rewrite right_id. apply later_mono. *)
(*   iIntros "(H1 & Hrest)". iFrame.  *)
(*   iFrame "H1". *)
(* apply sep_mono_r.   *)

(*   _Hyp_ : IntoVal ⟨ n; e ⟩ 〈 n; v' 〉 *)
(*   _Hyp1_ : MaybeIntoLaterNEnvs 1 Δ Δ' *)
(*   _Hyp2_ : envs_lookup i Δ' = Some (false, (l ↦[ n] v)%I) *)
(*   _Hyp3_ : envs_simple_replace i false (Esnoc  i (l ↦[ n] v')) Δ' = Some Δ'' *)
(*   _Hyp4_ : of_envs Δ'' -∗ WP fill K ⟨ n; #() ⟩ @ s; E {{ v, Φ v }} *)
(*   ============================ *)
(*   l ↦[ n] v ∗ (l ↦[ n] v' -∗ of_envs Δ'') -∗ *)
(*   l ↦[ n] ?v' ∗ (l ↦[ n] v' -∗ WP fill K 〈 n; LitV () 〉 @ s; E {{ v, Φ v }}) *)

(*   apply wand_mono. *)
(*   iIntros "(Hsh & Hvs)". *)
(*   apply sep_mono_r. wand_mono. *)

(*   rewrite right_id. apply later_mono. *)

(*     by apply later_mono, sep_mono_r, wand_mono. *)
(* Admitted. *)

End state.

Tactic Notation "wp_apply" open_constr(lem) :=
  iPoseProofCore lem as false true (fun H =>
    lazymatch goal with
    | |- envs_entails _ (wp ?s ?E ⟨_;?e⟩ ?Q) =>
      reshape_expr e ltac:(fun K e' =>
        wp_bind_core K; iApplyHyp H; try iNext; wp_expr_simpl) ||
      lazymatch iTypeOf H with
      | Some (_,?P) => fail "wp_apply: cannot apply" P
      end
    | _ => fail "wp_apply: not a 'wp'"
    end).

Tactic Notation "wp_alloc" ident(l) "as" constr(H) :=
  let solve_node _ :=
    let n := match goal with |- _ = Some (_, (?n n↦ ?γ's)%I) => n end in
    iAssumptionCore || fail "wp_load: cannot find" n "n↦ ?" in
  let finish _ :=
    first [intros l | fail 1 "wp_alloc:" l "not fresh"];
      eexists; split;
        [env_cbv; reflexivity || fail "wp_alloc:" H "not fresh"
        |wp_expr_simpl
         ; try wp_value_head
        ] in
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ⟨?n;?e⟩ ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' =>
         eapply (tac_wp_alloc _ _ _ _ _ H K n);
         first by apply to_base_val_inv)
      | fail 1 "wp_alloc: cannot find 'Alloc' in" e
      ];
    [apply _
    | solve_node ()
    | finish()]
  | _ => fail "wp_alloc: not a 'wp'"
  end.

Tactic Notation "wp_alloc" ident(l) :=
  let H := iFresh in wp_alloc l as H.

Tactic Notation "wp_load" :=
  let solve_mapsto n _ :=
    let l := match goal with |- _ = Some (_, (?l ↦[n]{_} _)%I) => l end in
    iAssumptionCore || fail "wp_load: cannot find" l "↦ ?" in
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ⟨?n;?e⟩ ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_load _ _ _ _ _ K))
      |fail 1 "wp_load: cannot find 'Load' in" e];
    [apply _
    |solve_mapsto n ()
    |wp_expr_simpl; try wp_value_head]
  | _ => fail "wp_load: not a 'wp'"
  end.

Tactic Notation "wp_store" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦[_]{_} _)%I) => l end in
    iAssumptionCore || fail "wp_store: cannot find" l "↦ ?" in
  let finish _ :=
    wp_expr_simpl; try first [wp_pure (Seq (Lit LitUnit) _)|wp_value_head] in
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ⟨?n;?e⟩ ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' =>
         eapply (tac_wp_store _ _ _ _ _ _ K); [apply _|..])
      |fail 1 "wp_store: cannot find 'Store' in" e];
    [apply _
    |solve_mapsto ()
    |env_cbv; reflexivity
    |finish ()]
  | _ => fail "wp_store: not a 'wp'"
  end.

(* Tactic Notation "wp_cas_fail" := *)
(*   let solve_mapsto _ := *)
(*     let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in *)
(*     iAssumptionCore || fail "wp_cas_fail: cannot find" l "↦ ?" in *)
(*   iStartProof; *)
(*   lazymatch goal with *)
(*   | |- envs_entails _ (wp ?s ?E ?e ?Q) => *)
(*     first *)
(*       [reshape_expr e ltac:(fun K e' => *)
(*          eapply (tac_wp_cas_fail _ _ _ _ _ K); [apply _|apply _|..]) *)
(*       |fail 1 "wp_cas_fail: cannot find 'CAS' in" e]; *)
(*     [apply _ *)
(*     |solve_mapsto () *)
(*     |try congruence *)
(*     |simpl; try wp_value_head] *)
(*   | |- envs_entails _ (twp ?s ?E ?e ?Q) => *)
(*     first *)
(*       [reshape_expr e ltac:(fun K e' => *)
(*          eapply (tac_twp_cas_fail _ _ _ _ K); [apply _|apply _|..]) *)
(*       |fail 1 "wp_cas_fail: cannot find 'CAS' in" e]; *)
(*     [solve_mapsto () *)
(*     |try congruence *)
(*     |wp_expr_simpl; try wp_value_head] *)
(*   | _ => fail "wp_cas_fail: not a 'wp'" *)
(*   end. *)

(* Tactic Notation "wp_cas_suc" := *)
(*   let solve_mapsto _ := *)
(*     let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in *)
(*     iAssumptionCore || fail "wp_cas_suc: cannot find" l "↦ ?" in *)
(*   iStartProof; *)
(*   lazymatch goal with *)
(*   | |- envs_entails _ (wp ?s ?E ?e ?Q) => *)
(*     first *)
(*       [reshape_expr e ltac:(fun K e' => *)
(*          eapply (tac_wp_cas_suc _ _ _ _ _ _ K); [apply _|apply _|..]) *)
(*       |fail 1 "wp_cas_suc: cannot find 'CAS' in" e]; *)
(*     [apply _ *)
(*     |solve_mapsto () *)
(*     |try congruence *)
(*     |env_cbv; reflexivity *)
(*     |simpl; try wp_value_head] *)
(*   | |- envs_entails _ (twp ?E ?e ?Q) => *)
(*     first *)
(*       [reshape_expr e ltac:(fun K e' => *)
(*          eapply (tac_twp_cas_suc _ _ _ _ _ K); [apply _|apply _|..]) *)
(*       |fail 1 "wp_cas_suc: cannot find 'CAS' in" e]; *)
(*     [solve_mapsto () *)
(*     |try congruence *)
(*     |env_cbv; reflexivity *)
(*     |wp_expr_simpl; try wp_value_head] *)
(*   | _ => fail "wp_cas_suc: not a 'wp'" *)
(*   end. *)

(* Tactic Notation "wp_faa" := *)
(*   let solve_mapsto _ := *)
(*     let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in *)
(*     iAssumptionCore || fail "wp_cas_suc: cannot find" l "↦ ?" in *)
(*   iStartProof; *)
(*   lazymatch goal with *)
(*   | |- envs_entails _ (wp ?s ?E ?e ?Q) => *)
(*     first *)
(*       [reshape_expr e ltac:(fun K e' => *)
(*          eapply (tac_wp_faa _ _ _ _ _ _ K); [apply _|..]) *)
(*       |fail 1 "wp_faa: cannot find 'CAS' in" e]; *)
(*     [apply _ *)
(*     |solve_mapsto () *)
(*     |env_cbv; reflexivity *)
(*     |wp_expr_simpl; try wp_value_head] *)
(*   | |- envs_entails _ (twp ?s ?E ?e ?Q) => *)
(*     first *)
(*       [reshape_expr e ltac:(fun K e' => *)
(*          eapply (tac_twp_faa _ _ _ _ _ K); [apply _|..]) *)
(*       |fail 1 "wp_faa: cannot find 'CAS' in" e]; *)
(*     [solve_mapsto () *)
(*     |env_cbv; reflexivity *)
(*     |wp_expr_simpl; try wp_value_head] *)
(*   | _ => fail "wp_faa: not a 'wp'" *)
(*   end. *)

Tactic Notation "wp_socket" ident(h) "as" constr(H) :=
  let solve_node _ :=
      let n :=
          match goal with
           | |- _ = Some (_, (?n n↦ ?γ's)%I) => n
           | |- ?foo => idtac foo
          end in
    iAssumptionCore || fail "wp_load: cannot find" n "n↦ ?" in
  let finish _ :=
    first [intros h | fail 1 "wp_socket:" h "not fresh"];
      eexists; split;
        [env_cbv; reflexivity || fail "wp_socket:" H "not fresh"
        |wp_expr_simpl
         ; try wp_value_head
        ] in
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ⟨?n;?e⟩ ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' =>
         eapply (tac_wp_socket _ _ _ _ _ H K n);
         first by apply to_base_val_inv)
      | fail 1 "wp_alloc: cannot find 'Alloc' in" e
      ];
    [ apply _
    | apply _
    | apply _
    | solve_node ()
    | finish()]
  | _ => fail "wp_alloc: not a 'wp'"
  end.

(* Tactic Notation "wp_socket_bind_suc" := *)
(*   let solve_mapsto _ := *)
(*     let h := match goal with |- _ = Some (_, (?h s↦[_]{_} _)%I) => h end in *)
(*     iAssumptionCore || fail "wp_store: cannot find" h "↦ ?" in *)
(*   let finish _ := *)
(*     wp_expr_simpl; try first [wp_pure (Seq (Lit (LitInt _)) _)|wp_value_head] in *)
(*   iStartProof; *)
(*   lazymatch goal with *)
(*   | |- envs_entails _ (wp ?s ?E ⟨?n;?e⟩ ?Q) => *)
(*     first *)
(*       [reshape_expr e ltac:(fun K e' => *)
(*          eapply (tac_wp_socket_bind_suc _ _ _ _ _ _ K); [apply _|..]) *)
(*       |fail 1 "wp_store: cannot find 'Store' in" e]; *)
(*     [apply _ *)
(*     |solve_mapsto () *)
(*     |env_cbv; reflexivity *)
(*     |finish ()] *)
(*   | _ => fail "wp_store: not a 'wp'" *)
(*   end. *)
