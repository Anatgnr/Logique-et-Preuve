Require Import Setoid.
(*  Logique intuitionniste *)

Section LJ.
 Variables P Q R S T : Prop.
 (*  Tactiques pour la conjonction 
__________________________________________________________________________________________
__________________________________________________________________________________________

    Introduction : pour prouver A /\ B : split (il faudra prouver A, puis B)
    Elimination : destruct H, si H : A /\ B 
                  variante : destruct H as [H1 H2].
        Dans les deux cas, on récupère deux hypothèses pour A et B (et on 
        choisit leurs noms, pour la variante "as..")
__________________________________________________________________________________________
__________________________________________________________________________________________

  *)
 Lemma and_comm : P /\ Q -> Q /\ P.
 Proof.
   intro H.
   destruct H as [H0 H1].
   split; assumption. (* "assumption" résout les deux sous-buts *)
 Qed.

 (* 
__________________________________________________________________________________________
__________________________________________________________________________________________

 tactiques pour la disjonction 
    Introduction:
     pour prouver A \/ B a partir de A : left
     pour prouver A \/ B a partir de B : right

    Elimination:
     preuve par cas : destruct H, si H: A \/ B
                      variante : destruct H as [H1 | H2]
        On aura a faire deux preuves, une pour chaque cas (cas A, cas B)
__________________________________________________________________________________________
__________________________________________________________________________________________
  *)

  Lemma or_not : P \/ Q -> ~P -> Q.
  Proof.
   intros H H0.     
   destruct H.
   - exfalso.
     apply H0; assumption.
     (* alternative: 
     assert (f:False).    
     {
       apply H0; trivial.
     }
     destruct f. *)
     (* "destruct f" sur f:False résoud n'importe quel but *)
   - assumption.
   Qed.

  (* Structuration de la preuve: +,*,+
     utiles quand on a plusieurs sous-preuves non triviales;
     améliorent la lisibilité du script *)
  
   (* 
__________________________________________________________________________________________
__________________________________________________________________________________________
 
   equivalence logique (<->, iff):
       unfold iff transforme A <-> B en
                             (A -> B) /\ (B -> A).
       donc split, destruct, etc, marchent
__________________________________________________________________________________________
__________________________________________________________________________________________

       (iff pour "if and only if", le "si et seulement si" en anglais)
    *)

  Lemma iff_comm : (P <-> Q) -> (Q <-> P).
  Proof.
    intro H.
    destruct H.
    split.
    - assumption.
    - assumption.
    (* "assumption" résoud les deux sous-buts engendrés par "split"
    donc on peut remplacer les trois dernières lignes par
    split; assumption.
    *)
  Qed.

  (* la regle de remplacement est implantée en Coq *)
  (* "rewrite H" fait un remplacement uniforme quand H est une
     équivalence *)
  (* "rewrite H" réécrit le but courant avec H *)
  (* "rewrite H in H'" fait la réécriture de H dans une autre hypothèse H' *)
  (* "rewrite <- H" réécrit dans l'autre sens, le membre droit par le gauche *)
  Lemma L1 : (P <-> Q) -> ~(Q <-> ~P).
  Proof.  
     intro H.
     rewrite H.
     intro H0.
     destruct H0.
     assert (~Q).
     { intro H2.
       apply H0; assumption.
     }
     apply H2. apply H1. assumption. 
  Qed.

  (* Fin des exemples, début des exercices *)

  (* Exercice : remplacer tauto par des vraies preuves 
     interactives *)
  (*  Exercices de la feuille 4 *)

  Lemma and_false : P /\ False -> False.
  Proof. 
    intro.
    destruct H.
    assumption.
  Qed.

  Lemma and_assoc : (P /\ Q) /\ R <-> P /\ (Q /\ R).
  Proof.
    split.
    intro.
    destruct H.
    split.
    - destruct H.
      assumption.
    -destruct H.
      split; assumption.
    -intro.
      split.
      destruct H.
      destruct H0.
      split; assumption.
      destruct H.
      destruct H0.
      assumption.
  Qed.

  (* Ex. 2 *)
  Lemma or_to_imp: ~ P \/ Q -> P -> Q.
  Proof.
    intros.
    destruct H.
    exfalso.
    apply H.
    assumption.
    assumption.
  Qed.   

  Lemma not_or_and_not: ~(P\/Q) -> ~P /\ ~Q.
  Proof.
    intro.
    split.
    unfold not in H.
    - unfold not.
      intro.
      apply H.
      left.
      assumption.
    -unfold not.
      intro.
      apply H.
      right.
      assumption. 
  Qed.

  (* Exercice 4 *)

  Lemma absorption_or: P \/ False <-> P.
  Proof.
    split.
    -intro.
      destruct H.
      assumption.
      exfalso.
      assumption.
    - intro.
      left.
      assumption. 
  Qed.

  Lemma and_or_dist : P /\ (Q \/ R) <-> P /\ Q \/ P /\ R.
  Proof.
    unfold iff.
    split.
    intro.
    destruct H.
    destruct H0.
    -left.
      split.
      assumption. assumption.
    - right.
      split.
      assumption. assumption.
    - intro.
    destruct H.
    destruct H.
    split.
    assumption.
    left.
    assumption.
    split.
    destruct H.
    assumption.
    destruct H.
    right.
    assumption.
  Qed.

  Lemma or_and_dist : P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
  Proof.
    split.
    - intro.
      destruct H.
      split.
      left. assumption.
      left. assumption.
      destruct H.
      split.
      right. assumption.
      right. assumption.
    - intro.
      destruct H.
      destruct H.
      destruct H0.
      left. assumption.
      left. assumption.
      destruct H0.
      left. assumption.
      right.
      split. assumption. assumption.
  Qed.

  Lemma and_not_not_impl: P /\ ~ Q -> ~(P -> Q).
  Proof.
    intro.
    destruct H.
    unfold not.
    intro.
    apply H0.
    apply H1.
    assumption.
  Qed.

  Lemma de_morgan1 : ~ (P \/ Q) <-> ~P /\ ~Q.
  Proof.
    unfold iff.
    split.
    intro.
    split.
    intro.
    apply H.
    left.
    assumption.
    intro.
    apply H.
    right.
    assumption.
    intro.
    destruct H.
    unfold not.
    intro.
    destruct H1.
    apply H.
    assumption.
    apply H0.
    assumption.
  Qed.

  Lemma reductio_ad_absurdum: (P -> ~P) -> ~P.
  Proof.
    intro.
    intro.
    apply H.
    apply H0.
    assumption.
  Qed.

  Lemma np_p_nnp: (~P -> P) -> ~~P.
  Proof.
    intro.
    intro; apply H0. apply H; assumption.
  Qed.

  (* Exercice: reprendre toutes les preuves précédentes, 
     en simplifiant et clarifiant les scripts:
     - structurer les sous-preuves avec +/-/*
     - inversement, quand c'est possible, factoriser avec 
       l'enchainement de tactiques (par ";")

     Le but est de faire que le script soit plus facile à lire
     par un humain, pas pour la machine.
   *)
  
End LJ.