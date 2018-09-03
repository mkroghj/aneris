From iris.algebra Require Import frac_auth.
From iris.base_logic.lib Require Export own.
From iris.proofmode Require Import tactics.

Section frac_auth_mnat.
  Context `{inG Σ (frac_authR mnatUR)}.
  
  Lemma frac_auth_mnat_valid (m n : mnat) (q : frac): ✓ (●! m ⋅ ◯!{q} n) → (n ≤ m)%nat.
  Proof.
     intros ?. by apply mnat_included, (frac_auth_included_total (A:=mnatUR) q).
  Qed.

  Lemma frac_auth_mnat_local_update (m n : mnat) (q : frac) :
    (●! m ⋅ ◯!{q} n) ~~> (●! (S m) ⋅ ◯!{q} (S m)).
  Proof.
    apply (frac_auth_update (A:=mnatUR)), (mnat_local_update m n (S m)). lia.
  Qed.

  Lemma frac_auth_mnat_own_update γ (m n : mnat) (q : frac) :
    own (A:=frac_authR mnatUR) γ (●! m) -∗
    own (A:=frac_authR mnatUR) γ (◯!{q} n) -∗
    |==> own (A:=frac_authR mnatUR) γ (●! (S m : mnat)) ∗
         own (A:=frac_authR mnatUR) γ (◯!{q} (S m : mnat)).
  Proof.
    iIntros "Ha Hc". iCombine "Ha" "Hc" as "H".
    rewrite -own_op.
    iApply (own_update with "H").
    apply frac_auth_mnat_local_update.
  Qed.
  
End frac_auth_mnat.

Section frac_auth_nat.
  Context `{inG Σ (frac_authR natUR)}.
  
  Lemma frac_auth_nat_valid (m n : nat) (q : frac): ✓ (●! m ⋅ ◯!{q} n) → (n ≤ m)%nat.
  Proof.
     intros ?. by apply nat_included, (frac_auth_included_total (A:=natUR) q).
  Qed.

  Lemma frac_auth_nat_local_update (m n o : nat) (q : frac) :
    (●! m ⋅ ◯!{q} n) ~~> (●! (m + o) ⋅ ◯!{q} (n + o)).
  Proof.
    apply (frac_auth_update (A:=natUR)), (nat_local_update m n (m + o) (n + o)). lia.
  Qed.

  Lemma frac_auth_nat_own_update γ (m n o : nat) (q : frac) :
    own (A:=frac_authR natUR) γ (●! m) -∗
    own (A:=frac_authR natUR) γ (◯!{q} n) -∗
    |==> own (A:=frac_authR natUR) γ (●! (m + o : nat)) ∗
         own (A:=frac_authR natUR) γ (◯!{q} (n + o : nat)).
  Proof.
    iIntros "Ha Hc". iCombine "Ha" "Hc" as "H".
    rewrite -own_op.
    iApply (own_update with "H").
    apply frac_auth_nat_local_update.
  Qed.
  
End frac_auth_nat.
