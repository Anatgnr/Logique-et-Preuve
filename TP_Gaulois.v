Ltac forall_e H t := (generalize (H t); intro).

Require Import Setoid.


Section Gaulois.
  Variable personnage: Set.
  Variables humain gaulois romain animal: personnage -> Prop.
  Variables Idefix Panoramix: personnage.

  Hypothesis Hngr: forall p:personnage, ~(gaulois p /\ romain p).
  Hypothesis Hpers: forall p:personnage, animal p \/ gaulois p \/ romain p.
  Hypothesis Hhum: forall p:personnage, humain p <-> (gaulois p \/ romain p).
  Hypothesis Hnon_humain_animal:
    forall p:personnage, ~(humain p /\ animal p).

  Hypothesis Hidef: animal Idefix.
  Hypothesis Hpano: gaulois Panoramix.
  Hypothesis Hrom: exists p:personnage, romain p.

  Theorem Exemple: exists x:personnage, humain x /\ ~gaulois x.
  Proof.
    destruct Hrom as [y Hy].
    exists y.
    split.
    - rewrite Hhum.
      right.
      assumption.
    - forall_e Hngr y.
      intro Hgy.
      apply H.
      split.
      + assumption.
      + assumption.
  Qed.

(* Dans les 5 théorèmes ci-dessous, remplacez "Admitted." par un 
   script de preuve complet, que vous terminerez par "Qed."

   Barème indicatif: pour chaque théorème, 3.5 points pour un
   script qui prouve le théorème sans rien admetter; 0.5 point 
   supplémentaire si la preuve est structurée de manière à 
   permettre de la suivre sans interagir avec Coq (prendre exemple
   sur la preuve précédente).

   *)
  
  Theorem Exercice1: ~ gaulois Idefix.
  Proof.
    intro.
    destruct Hrom.
    forall_e Hnon_humain_animal Idefix.
    apply H1.
    split.
    - forall_e Hhum Idefix.
      destruct H2.
      apply H3.
      left; assumption.  
    - assumption.
  Qed.

  Theorem Exercice2:
    forall p:personnage, humain p -> ~romain p -> gaulois p.
  Proof.
  intros.
  (* forall_e Hngr p.
  destruct H1. *)
  forall_e Hhum p.
  destruct H1.
  destruct H1.
  - assumption.
  - assumption.
  - exfalso; apply H0; assumption. 
  Qed.

  Theorem Exercice3:
    exists p:personnage, humain p /\ ~gaulois p.
  Proof.
    destruct Hrom.
    exists x.
    split.
    - forall_e Hhum x.
      destruct H0.
      apply H1.
      right; assumption.
    - intro.
      forall_e Hngr x.
      apply H1.
      split.
      + assumption.
      + assumption.
  Qed.

  Theorem Exercice4:
    forall p, ~animal p -> gaulois p \/ romain p.
  Proof.
  intros.
  forall_e Hpers p.
  destruct H0.
  exfalso; apply H; assumption.
  assumption.
  Qed.

  Theorem Exercice5: Idefix <> Panoramix.
  Proof.
    intro.
    forall_e Hpers Idefix.
    forall_e Hnon_humain_animal Idefix.
    apply H1.
    split.
    forall_e Hhum Idefix.
    destruct H2.
    apply H3.
    symmetry in H.
    rewrite H in Hpano.
    left.
    assumption.
    assumption.
    (* Indication: on peut utiliser n'importe quel théorème, 
       y compris un qui a été prouvé comme exercice *)
  Admitted.

End Gaulois.