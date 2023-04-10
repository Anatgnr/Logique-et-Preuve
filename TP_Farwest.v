Ltac forall_e H t := (generalize (H t); intro).

Require Import Setoid.

Section Farwest.
  Variable personnage: Type.
  Variables humain animal bandit cowboy: personnage -> Prop.
  Variables Averell Rantanplan Luke: personnage.
  Variable idiot: personnage -> Prop.

  Hypothesis Hh_ou_a: forall p:personnage, animal p \/ humain p.
  Hypothesis Hhna: forall p:personnage, ~(humain p /\ animal p).
  Hypothesis Hbnc: forall p:personnage, ~(cowboy p /\ bandit p).
  Hypothesis Hb: forall p:personnage, bandit p -> humain p.
  Hypothesis Hc: forall p:personnage, cowboy p -> humain p.
  Hypothesis Hhum: forall p:personnage, humain p -> cowboy p \/ bandit p.

  Hypothesis Hbni: exists p:personnage, bandit p /\ ~ idiot p.
  
  Hypothesis Hav: bandit Averell.
  Hypothesis Hlu: cowboy Luke.
  Hypothesis Hra: animal Rantanplan.
  Hypothesis Hid: idiot Rantanplan /\ idiot Averell.

  Theorem Exemple: Averell <> Luke.
  Proof.
    intro Hal.
    rewrite Hal in Hav.
    forall_e Hbnc Luke.
    apply H.
    split.
    - assumption.
    - assumption.
  Qed.

  Theorem Exercice1: ~ cowboy Rantanplan.
  Proof.
    intro.
    forall_e Hhna Rantanplan.
    forall_e Hc Rantanplan.
    apply H0.
    split.
    - apply H1.
      assumption.
    - assumption.
  Qed.

  Theorem Exercice2: forall p:personnage, ~(bandit p /\ animal p).
  Proof.
    intro.
    intro.
    forall_e Hhna p.
    forall_e Hbnc p.
    destruct H.
    apply H0.
    split.
    - forall_e Hb p.
      apply H3; assumption.
    - assumption. 
  Qed.

  Theorem Exercice3: forall p:personnage, cowboy p \/ bandit p <-> humain p.
  Proof.
    intro.
    split.
    - intro.
      destruct H.
      + forall_e Hc p; apply H0; assumption.
      + forall_e Hb p; apply H0; assumption.
    - intro.
      forall_e Hhum p; apply H0; assumption.  
  Qed.

  Theorem Exercice4: forall p:personnage, animal p \/ cowboy p \/ bandit p.
  Proof.
    intro.
    forall_e Hhum p.
    forall_e Hh_ou_a p.
    destruct H0.
    left; assumption.
    right.
    apply H.
    assumption.
  Qed.

  Theorem Exercice5: exists p:personnage, bandit p /\ p<>Averell.
  Proof.
    destruct Hid.
    destruct Hbni.
    exists x.
    destruct H1.
    split.
    assumption.
    unfold not.
    intro.
    apply H2.
    symmetry in H3.
    rewrite H3 in H0.
    assumption.
  Qed.

End Farwest.
;