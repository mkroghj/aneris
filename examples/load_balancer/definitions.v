From distris Require Import tactics proofmode notation adequacy network.

Import Network.

Section relay.
  Context `{X : Type, distG Σ}.

  Definition relay_resp_si (P : X -> iProp Σ) Pin Pout :
    socket_interp Σ :=
    (λ msg, ∃ φ (v : X), ms_sender msg ⤇ φ ∗
           Pin (ms_body msg) v ∗ P v ∗
           (∀ m', P v ∗ Pout (ms_body m') v -∗ φ m'))%I.
  
End relay.
