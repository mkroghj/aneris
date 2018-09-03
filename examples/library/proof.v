From iris Require Import invariants.
From iris.algebra Require Import gmap frac agree frac_auth.
From iris.base_logic Require Export gen_heap.
From iris.base_logic.lib Require Export own saved_prop.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics.
From stdpp Require Import base.
From distris Require Import lifting tactics proofmode notation adequacy.
From distris.examples.library Require Import code.
From iris.proofmode Require Import coq_tactics.
From iris.proofmode Require Export tactics.

Set Default Proof Using "Type".

Import Network.
Import String.
Import uPred.

Section strings.

  Lemma append_nil_l s :
    "" +:+ s = s.
  Proof. done. Qed.

  Lemma append_cons s1 :
    ∀ s2 a, String a (s1 +:+ s2) = (String a s1) +:+ s2.
  Proof.
    induction s1; intros.
    - by rewrite append_nil_l.
    - rewrite -IHs1. done.
  Qed.

  Lemma append_assoc s1 s2 s3 :
    s1 +:+ s2 +:+ s3 = (s1 +:+ s2) +:+ s3.
  Proof.
    induction s1.
    - by rewrite !append_nil_l.
    - by rewrite -append_cons IHs1 append_cons.
  Qed.

  Lemma length_Sn a s :
    length (String a s) = S (length s).
  Proof. by cbn. Qed.

  Lemma length_app s1 :
    ∀ s2, length (s1 +:+ s2) = length s1 + length s2.
  Proof.
   induction s1; intros.
    - by rewrite append_nil_l.
    - by rewrite -append_cons !length_Sn IHs1.
  Qed.

  Lemma prefix_empty_true s :
    prefix "" s = true.
  Proof. destruct s; cbn; auto. Qed.

  Lemma index_0_empty s :
    index 0 "" s = Some 0.
  Proof. destruct s; by cbn. Qed.

  Lemma index_prefix_true s s' :
    index 0 s s' = Some 0 →
    prefix s s' = true.
  Proof.
    destruct s,s'; simpl; cbn; auto.
    - intro; inversion H.
    - intro; destruct ascii_dec.
      + destruct (prefix s s'); auto; destruct (index 0 _ s'); inversion H.
      + destruct (index 0 _ s'); inversion H.
  Qed.

  Lemma index_cons_0_eq a s s' :
    index 0 s s' = Some 0 → index 0 (String a s) (String a s') = Some 0.
  Proof.
    intros Hindex.
    cbn. destruct ascii_dec.
    - assert (Hprefix: prefix s s' = true).
      { by apply index_prefix_true. }
        by rewrite Hprefix.
    - by destruct n.
  Qed.

  Lemma index_append_here s t :
    index 0 s (s +:+ t) = Some 0.
  Proof.
    induction s.
    - apply index_0_empty.
    - apply index_cons_0_eq.
      apply IHs.
  Qed.

  Lemma index_0_append_char a t v s :
    s = String a "" →
    index 0 s t = None →
    index 0 s (t +:+ s +:+ v) = Some (length t).
  Proof.
    induction t; intros.
    - rewrite append_nil_l. apply index_append_here.
    - rewrite H. rewrite -append_cons. cbn.
      destruct ascii_dec; subst. cbn in H0. destruct ascii_dec.
      rewrite prefix_empty_true in H0. inversion H0.
      by destruct n.
      rewrite IHt; auto. cbn in H0. destruct ascii_dec. by destruct n.
      destruct index; auto. inversion H0.
  Qed.

  Lemma substring_0_length s :
    substring 0 (length s) s = s.
  Proof. induction s; simpl; auto. by rewrite IHs. Qed.

  Lemma substring_Sn a n m s :
    substring (S n) m (String a s) = substring n m s.
  Proof. induction s; destruct n,m; simpl; auto. Qed.

  Lemma substring_add_length_app n m s1 :
    ∀ s2, substring (length s1 + n) m (s1 +:+ s2) = substring n m s2.
  Proof. induction s1; destruct n,m; simpl; auto. Qed.

  Lemma substring_0_length_append s1 s2 :
    substring 0 (length s1) (s1 +:+ s2) = s1.
  Proof. apply prefix_correct, index_prefix_true, index_append_here. Qed.

  Lemma substring_length_append s1 :
    ∀ s2, substring (length s1) (length s2) (s1 +:+ s2) = s2.
  Proof.
    induction s1; intros s2.
    - rewrite append_nil_l. apply substring_0_length.
    - rewrite length_Sn substring_Sn. apply IHs1.
  Qed.

End strings.

Section library.
  Context `{cG : ccounterG Σ}
          `{dG : distG Σ}
          `{siG : socketInterpG Σ}.

Lemma wp_assert n E (Φ : val → iProp Σ) e `{!Closed [] ⟨n;e⟩} :
  WP ⟨n;e⟩ @ E {{ v, ⌜v = 〈n;#true〉⌝ ∧ ▷ Φ 〈n;#()〉 }} -∗ WP ⟨n;assert: e⟩ @ E {{ Φ }}.
Proof.
  iIntros "HΦ". rewrite /assert /=.
  wp_lam. rewrite /ground_lang.subst.
  wp_let.
  wp_apply (wp_wand with "HΦ").
  iIntros (v) "[% ?]"; subst.  by wp_if.
Qed.

Lemma unSOME_spec n e v v' :
  IntoVal ⟨n;e⟩ 〈n;v〉 →
  {{{ ⌜v = SOMEV v'⌝ }}}
    ⟨n;unSOME e⟩
  {{{ RET 〈n;v'〉; True }}}.
Proof.
  iIntros (<-%to_base_val'%ground_lang.of_to_val Φ ->) "HΦ".
  wp_lam. wp_match. by iApply "HΦ".
Qed.

Lemma listen_spec P Q n (h : socket_handle) (s : socket) (a : socket_address)
        (rm : message_soup)
        (handler : ground_lang.expr) :
  AsVal ⟨n;handler⟩ →
  saddress s = Some a →
  (∀ mId m φ,
      {{{ ⌜received_message_info a m⌝ ∗ P ∗ h s↦[n] s ∗ a r↦{½} (<[mId:=m]>rm) ∗
           mId m↦{¾} m ∗ a ⤇ φ ∗ φ (message_stable_from_message m) }}}
        ⟨n;handler #(m_body m) #(m_sender m)⟩
      {{{ v, RET 〈n;v〉; Q v }}}) -∗
  {{{ P ∗ h s↦[n] s ∗ a r↦{½} rm }}}
     ⟨ n; listen (Lit $ LitSocket h) handler ⟩
  {{{ v, RET 〈n;v〉; Q v }}}.
Proof.
  iIntros ([[m handlerV] Hval%of_to_val] Haddr) "#Hhandler";
    inversion Hval;simplify_eq.
  iLöb as "IH".
  iAlways. iIntros (Φ) "(HP & Hsocket & Hrecs) HΦ".
  wp_rec.
  wp_let.
  wp_apply (wp_receive_from _ _ a with "[$Hsocket $Hrecs]"); first done.
  iIntros (r) "HQ".
  iDestruct "HQ" as (rm') "(Hsocket & Hrecs & [HQ | [% %]])".
  - iDestruct "HQ" as (mId message φ) "(Hrec & % & % & Hm & Hsi)"; subst.
    wp_match. wp_proj.
    wp_let. wp_proj.
    wp_apply ("Hhandler" with "[-HΦ] [HΦ]"); last iFrame. iFrame.
  - subst. wp_match.
    iApply ("IH" with "[-HΦ]"). iFrame. iFrame.
Qed.

Lemma listen_wait_spec n (h : socket_handle) (s : socket) (a : socket_address)
        (rm : message_soup) φ :
  saddress s = Some a →
  {{{ h s↦[n] s ∗ a r↦{½} rm ∗ a ⤇ φ}}}
     ⟨ n; listen_wait (Lit $ LitSocket h) ⟩
  {{{ m mId, RET 〈n;(#(m_body m), #(m_sender m))〉;
      ⌜received_message_info a m⌝ ∗ h s↦[n] s ∗ a r↦{½} (<[mId:=m]>rm) ∗
      mId m↦{¾} m ∗ φ (message_stable_from_message m)
  }}}.
Proof.
  iIntros (Haddr Φ) "(Hs & Hrec & Hφ) HΦ".
  iLöb as "IH".
  wp_rec.
  wp_apply (wp_receive_from with "[$Hs $Hrec]"); first done.
  iIntros (r) "HQ"; iDestruct "HQ" as (rm') "(Hs & Hrec & [HQ | [-> ->]])"; simpl.
  - iDestruct "HQ" as (mId message φ' Hri Hm Hrecs) "(Hm & Hφ' & HP)"; subst.
    iDestruct (si_pred_agree _ _ _ (message_stable_from_message message) with "Hφ Hφ'") as "#Heqv".
    wp_match. iApply "HΦ". iRewrite -"Heqv" in "HP". by iFrame.
  - wp_match. iApply ("IH" with "Hs Hrec Hφ"). iFrame.
Qed.

Definition valid_tag t := index 0 "_" t = None.

Lemma tag_of_message_spec n m (s : string) t v:
  IntoVal ⟨n;m⟩ 〈n;#s〉 →
  valid_tag t →
  {{{ ⌜s = t +:+ "_" +:+ v⌝ }}}
    ⟨n;tag_of_message m⟩
  {{{ v, RET 〈n;#v〉; ⌜v = t⌝ }}}.
Proof.
  iIntros (Hv%to_base_val' Htag Φ HP) "HΦ".
  apply ground_lang.of_to_val in Hv; simplify_eq.
  wp_let. wp_find_from. split; eauto.
    by instantiate (1:=0%nat).
  rewrite (index_0_append_char "_"); auto. simpl. wp_match.
  wp_substring. repeat split; eauto. by instantiate (1:=0%nat).
  rewrite substring_0_length_append. by iApply "HΦ".
Qed.

Lemma value_of_message_spec n m (s : string) t v :
  IntoVal ⟨n;m⟩ 〈n;#s〉 →
  valid_tag t →
  {{{ ⌜s = t +:+ "_" +:+ v⌝ }}}
    ⟨n;value_of_message m⟩
  {{{ r, RET 〈n;#r〉; ⌜r = v⌝ }}}.
Proof.
  iIntros (Hv%to_base_val' Htag Φ HP) "HΦ".
  apply ground_lang.of_to_val in Hv; simplify_eq.
  wp_let. wp_find_from; simpl. split; eauto.
  { by instantiate (1:=0%nat). }
  rewrite (index_0_append_char "_"); auto; simpl; wp_match.
  wp_op. wp_let.
  wp_op. wp_let.
  wp_op.
  wp_substring. repeat split; eauto.
  instantiate (1:=(length t + 1)%nat). apply Nat2Z.inj_add.
  instantiate (1:=(length v)%nat).
  { rewrite !length_app plus_assoc length_Sn /= !Nat2Z.inj_add. ring. }
  rewrite substring_add_length_app substring_Sn substring_0_length.
  by iApply "HΦ".
Qed.

Fixpoint list_coh l v :=
  match l with
  | [] => v = NONEV
  | a::l' => ∃ lv : ground_lang.val, v = SOMEV (a,lv) ∧ list_coh l' lv
  end.

Lemma list_make_spec n :
  {{{ True }}}
       ⟨n;list_make #()⟩
  {{{ v, RET 〈n;v〉; ⌜list_coh [] v⌝}}}.
Proof.
  iIntros (Φ) "H HΦ". rewrite /list_make /=.
  wp_lam. by iApply "HΦ".
Qed.

Lemma list_cons_spec n (e1 e2 : ground_lang.expr) a lv l :
  IntoVal ⟨n;e1⟩ 〈n;a〉 →
  IntoVal ⟨n;e2⟩ 〈n;lv〉 →
  {{{ ⌜list_coh l lv⌝ }}}
       ⟨n;list_cons e1 e2⟩
  {{{ v, RET 〈n;v〉; ⌜list_coh (a::l) v⌝}}}.
Proof.
  iIntros (<-%to_base_val'%ground_lang.of_to_val
              <-%to_base_val'%ground_lang.of_to_val Φ) "% HΦ".
  wp_lam.
  wp_let.
  iApply "HΦ".
  iPureIntro. by exists lv.
Qed.

Lemma list_head_spec n e lv l :
  IntoVal ⟨n;e⟩ 〈n;lv〉 →
  {{{ ⌜list_coh l lv⌝ }}}
       ⟨n;list_head e⟩
  {{{ v, RET 〈n;v〉; ⌜(l = [] ∧ v = NONEV) ∨
                      (∃ v' l', l = v' :: l' ∧ v = SOMEV v')⌝}}}.
Proof.
  iIntros (<-%to_base_val'%ground_lang.of_to_val Φ) "% HΦ".
  wp_lam. destruct l; simpl in *; subst.
  - wp_match. iApply "HΦ". iPureIntro. by left.
  - destruct a as [lv' [Hhead Htail]] eqn:Heq; subst.
    wp_match. wp_proj. iApply "HΦ". iPureIntro. right. by exists v,l.
Qed.

Lemma list_tail_spec n e lv l :
  IntoVal ⟨n;e⟩ 〈n;lv〉 →
  {{{ ⌜list_coh l lv⌝ }}}
       ⟨n;list_tail e⟩
  {{{ v, RET 〈n;v〉; ⌜list_coh (tail l) v⌝}}}.
Proof.
  iIntros (<-%to_base_val'%ground_lang.of_to_val Φ) "% HΦ".
  wp_lam. destruct l; simpl in *; subst.
  - wp_match. by iApply "HΦ".
  - destruct a as [lv' [Hhead Htail]] eqn:Heq; subst.
    wp_match. wp_proj. by iApply "HΦ".
Qed.

Lemma list_length_spec n e l lv :
  IntoVal ⟨n;e⟩ 〈n;lv〉 →
  {{{ ⌜list_coh l lv⌝ }}}
    ⟨n;list_length lv⟩
  {{{ v, RET 〈n;#v〉; ⌜v = List.length l⌝ }}}.
Proof.
  iIntros (<-%to_base_val'%ground_lang.of_to_val Φ) "Ha HΦ".
  iInduction l as [|a l'] "IH" forall (lv Φ);
  iDestruct "Ha" as %Ha; simpl in Ha; subst; wp_rec.
  - wp_match. iApply ("HΦ" $! 0 : nat). auto.
  - destruct Ha as [lv' [Hlv Hlcoh]]; subst.
    wp_match. wp_proj. wp_bind (list_length _).
    iApply ("IH" $! _ _ Hlcoh). iNext. iIntros; simpl.
    wp_op. iSpecialize ("HΦ" $! (1 + v)). rewrite Nat2Z.inj_add. iApply "HΦ".
    eauto.
Qed.

Lemma list_iter_spec {A} n e (l : list A) lv handler P Φ Ψ
      (toval : A -> ground_lang.val) :
  AsVal ⟨n;handler⟩ →
  IntoVal ⟨n;e⟩ 〈n;lv〉 →
  (∀ (a : A),
  {{{ ⌜a ∈ l⌝ ∗ P ∗ Φ a }}}
     ⟨n;handler (toval a)⟩
  {{{v, RET 〈n;v〉; P ∗ Ψ a }}}) -∗
  {{{ ⌜list_coh (map (λ a, toval a) l) lv⌝ ∗ P ∗ [∗ list] a∈l, Φ a }}}
    ⟨n;list_iter handler lv⟩
  {{{ RET 〈n;#()〉; P ∗ [∗ list] a∈l, Ψ a }}}.
Proof.
  iIntros ([[m handlerV] Hval%of_to_val] <-%to_base_val'%ground_lang.of_to_val).
  inversion Hval; simplify_eq.
  iInduction l as [|a l'] "IH" forall (lv);
  iIntros "#Helem"; iIntros (Φ') "!# (Ha & HP & Hl) HΦ";
  iDestruct "Ha" as %Ha; simpl in Ha; subst; wp_rec; wp_let.
  - wp_match. iApply "HΦ"; eauto.
  - assert (Helemof: a ∈ a :: l').
    { apply elem_of_list_here. }
    destruct Ha as [lv' [Hlv Hlcoh]]; subst.
    wp_match. wp_proj. wp_let. wp_proj.
    iDestruct (big_sepL_cons with "Hl") as "[Ha Hl']".
    wp_apply ("Helem" with "[HP Ha]"); iFrame; eauto.
    iIntros (v) "[HP Ha]". simpl. wp_seq.
    iApply ("IH" with "[] [$HP $Hl']"); eauto.
    { iIntros (a' HΦ'') "!# (% & HP & Ha) HΦ''".
      wp_apply ("Helem" with "[HP Ha]"); iFrame.
      iPureIntro. by apply elem_of_list_further.
    }
    iNext. iIntros "(HP & Hl)". iApply "HΦ". iFrame.
Qed.

Lemma list_fold_spec {A} n handler (l : list A) e1 e2 acc lv P Φ Ψ
      (toval : A -> ground_lang.val) :
  AsVal ⟨n;handler⟩ →
  IntoVal ⟨n;e1⟩ 〈n;acc〉 →
  IntoVal ⟨n;e2⟩ 〈n;lv〉 →
  (∀ (a : A) acc lacc lrem,
  {{{ ⌜l = lacc ++ a :: lrem⌝ ∗ P lacc acc ∗ Φ a }}}
     ⟨n;handler acc (toval a)⟩
  {{{v, RET 〈n;v〉; P (lacc ++ [a]) v ∗ Ψ a }}}) -∗
  {{{ ⌜list_coh (map (λ a, toval a) l) lv⌝ ∗ P [] acc ∗ [∗ list] a∈l, Φ a }}}
    ⟨n; list_fold handler acc lv⟩
  {{{v, RET 〈n;v〉; P l v ∗ [∗ list] a∈l, Ψ a }}}.
Proof.
  iIntros ([[m handlerV] Hval%of_to_val]
             <-%to_base_val'%ground_lang.of_to_val
             <-%to_base_val'%ground_lang.of_to_val
          ).
  iIntros "#Hcl". iIntros (Ξ) "!# (Hl & Hacc & HΦ) HΞ".
  change l with ([] ++ l) at 1 4.
  generalize (@nil A) at 1 3 4 as lproc => lproc.
  inversion Hval; simplify_eq.
  iInduction l as [|x l] "IHl" forall (Ξ lproc acc lv) "Hacc Hl HΞ".
  - iDestruct "Hl" as %?; simpl in *; simplify_eq.
    repeat wp_rec.
    wp_match. iApply "HΞ".
    rewrite app_nil_r; iFrame.
  - iDestruct "Hl" as %[lw [? Hlw]]; subst.
    iDestruct "HΦ" as "[Hx HΦ]".
    repeat wp_rec. wp_match.
    wp_proj. wp_let. wp_proj. wp_let.
    wp_apply ("Hcl" with "[$Hacc $Hx] [-]"); auto.
    iNext. iIntros (w) "[Hacc HΨ]"; simpl.
    wp_let.
    iApply ("IHl" with "[] [$HΦ] [$Hacc] [] [HΨ HΞ]"); [|auto|].
    { rewrite -app_assoc; auto. }
    iNext. iIntros (v) "[HP HΨs]".
    rewrite -app_assoc.
    iApply "HΞ"; iFrame.
Qed.

Lemma list_fold_spec'_generalized {A} n handler (l lp : list A) e1 e2 acc lv P Φ Ψ
      (toval : A -> ground_lang.val) :
  AsVal ⟨n;handler⟩ →
  IntoVal ⟨n;e1⟩ 〈n;acc〉 →
  IntoVal ⟨n;e2⟩ 〈n;lv〉 →
  □ (∀ (a : A) acc lacc lrem, (P lacc acc None (a::lrem) -∗ P lacc acc (Some a) lrem))%I -∗
  (∀ (a : A) acc lacc lrem,
  {{{ ⌜lp ++ l = lacc ++ a :: lrem⌝ ∗ P lacc acc (Some a) lrem ∗ Φ a }}}
     ⟨n;handler acc (toval a)⟩
  {{{v, RET 〈n;v〉; P (lacc ++ [a]) v None lrem ∗ Ψ a }}}) -∗
  {{{ ⌜list_coh (map (λ a, toval a) l) lv⌝ ∗ P lp acc None l ∗ [∗ list] a∈l, Φ a }}}
    ⟨n; list_fold handler acc lv⟩
  {{{v, RET 〈n;v〉; P (lp ++ l) v None [] ∗ [∗ list] a∈l, Ψ a }}}.
Proof.
  iIntros ([[m handlerV] Hval%of_to_val]
             <-%to_base_val'%ground_lang.of_to_val
             <-%to_base_val'%ground_lang.of_to_val
          ).
  iIntros "#Hvs #Hcl". iIntros (Ξ) "!# (Hl & Hacc & HΦ) HΞ".
  (* change l with ([] ++ l) at 1. *)
  (* generalize (@nil A) at 1 as lproc => lproc. *)
  inversion Hval; simplify_eq.
  iInduction l as [|x l] "IHl" forall (Ξ lp acc lv) "Hacc Hl HΞ".
  - iDestruct "Hl" as %?; simpl in *; simplify_eq.
    repeat wp_rec.
    wp_match. iApply "HΞ".
    rewrite app_nil_r; iFrame.
  - iDestruct "Hl" as %[lw [? Hlw]]; subst.
    iDestruct "HΦ" as "[Hx HΦ]".
    repeat wp_rec. wp_match.
    wp_proj. wp_let. wp_proj. wp_let.
    iPoseProof ("Hvs" with "Hacc") as "Hacc".
    wp_apply ("Hcl" with "[$Hacc $Hx] [-]"); auto.
    iNext. iIntros (w) "[Hacc HΨ]"; simpl.
    wp_let.
    iApply ("IHl" with "[] [$HΦ] [$Hacc] [] [HΨ HΞ]"); [|auto|].
    { rewrite -app_assoc; auto. }
    iNext. iIntros (v) "[HP HΨs]".
    rewrite -app_assoc.
    iApply "HΞ"; iFrame.
Qed.

Lemma list_fold_spec' {A} n handler (l : list A) e1 e2 acc lv P Φ Ψ
      (toval : A -> ground_lang.val) :
  AsVal ⟨n;handler⟩ →
  IntoVal ⟨n;e1⟩ 〈n;acc〉 →
  IntoVal ⟨n;e2⟩ 〈n;lv〉 →
  □ (∀ (a : A) acc lacc lrem, (P lacc acc None (a::lrem) -∗ P lacc acc (Some a) lrem))%I -∗
  (∀ (a : A) acc lacc lrem,
  {{{ ⌜l = lacc ++ a :: lrem⌝ ∗ P lacc acc (Some a) lrem ∗ Φ a }}}
     ⟨n;handler acc (toval a)⟩
  {{{v, RET 〈n;v〉; P (lacc ++ [a]) v None lrem ∗ Ψ a }}}) -∗
  {{{ ⌜list_coh (map (λ a, toval a) l) lv⌝ ∗ P [] acc None l ∗ [∗ list] a∈l, Φ a }}}
    ⟨n; list_fold handler acc lv⟩
  {{{v, RET 〈n;v〉; P l v None [] ∗ [∗ list] a∈l, Ψ a }}}.
Proof.
  iIntros (? ? ?) "#Hvs #Hcl".
  iApply (list_fold_spec'_generalized _ handler l [] with "[-]"); eauto.
Qed.

End library.

