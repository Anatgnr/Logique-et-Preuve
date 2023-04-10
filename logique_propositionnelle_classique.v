Require Import Setoid Classical.

(*  Logique classique
    On peut sauter les 2 commandes suivantes 
 *)

(* un peu de magie noire *)
Definition EXM :=   forall A:Prop, A \/ ~A.

Ltac add_exm  A :=
  let hname := fresh "exm" in
  assert(hname : A \/ ~A);[classical_right; assumption|].


Section LK.
  (* 
   Pour ajouter une instance du tiers-exclu de la forme  A \/ ~A 
   il suffit d'exécuter la tactique "add_exm A"
   *)

  Variables P Q R S T : Prop.

  Lemma double_neg : ~~ P -> P.
  Proof.
    intro H.
    add_exm  P. (* "je fais un tiers exclus sur P " *)
    destruct exm. (* Presque toujours, destruct suit add_exm *)
    - assumption.
    - assert (f:False).
      {
        apply H. assumption.
      }
      destruct f. (* ou: exfalso, etc. *)
   Qed.

  (* Variantes: tactiques classical_left et classical_right.
     Pour prouver A \/ B:
     - classical_left demande de prouver A, avec ~B comme hypothèse en plus.
     - classigal_right demande de prouver B, avec ~A comme hypothèse en plus.
  *)

  Lemma weak_exm: P \/ (P->Q).
  Proof.
  classical_right.
  intro p; exfalso; apply H; assumption.
  Qed.

  (* Exercice: completer toutes les preuves, en remplaçant les
     "Admitted" par des preuves terminées par "Qed."; et 
     sans utiliser ni auto, ni tauto.  *)

  Lemma de_morgan : ~ ( P /\ Q) <-> ~P \/ ~Q.
  Proof.
    split.
    add_exm Q.
    add_exm P.
    destruct exm.
    destruct exm0.
    - intro.
      destruct H1.
      split.
      assumption. assumption.
    - intro.
      left.
      assumption.
    - intro.
      right.
      assumption.
    -intro.
      intro.
      destruct H.
      destruct H0.
      apply H; assumption.
      destruct H0.
      apply H; assumption.
  Qed.

  Lemma not_impl_and : ~(P -> Q) <-> P /\ ~ Q.
  Proof.
    split; intro.
    - add_exm Q; destruct exm; add_exm P; destruct exm.
      + split.
        * assumption.
        * intro; apply H; intro; assumption.
      + split.
        * exfalso; apply H; intro; assumption.
        * intro; apply H; intro; assumption.
      + split.
        * assumption.
        * assumption.
      + split.
        * exfalso; apply H; intro.
          exfalso; apply H1; assumption.
        * assumption.
    - intro.
      destruct H.
      apply H1; apply H0; assumption.
  Qed.

  Lemma contraposee: (P -> Q) <-> (~Q -> ~P).
  Proof.
    split.
    - intro.
      intro.
      intro.
      apply H0.
      apply H.
      assumption.
    - intro.
      intro.
      add_exm Q; destruct exm.
      assumption.
      exfalso; apply H; assumption; assumption.
  Qed.

  Lemma exm_e : (P -> Q) -> (~P -> Q) -> Q.
  Proof.
    intros.
    add_exm P; destruct exm.
    apply H; assumption.
    apply H0; assumption.
  Qed.

  Lemma exo_16 : (~ P -> P) -> P.
  Proof.
    intros.
    add_exm P; destruct exm.
    assumption.
    apply H; assumption.
  Qed.

  Lemma double_impl : (P -> Q) \/ (Q -> P).
  Proof.
    add_exm P.
    add_exm Q.
    destruct exm.
    destruct exm0.
    left.
    intros.
    assumption.
    right.
    intros.
    assumption.
    destruct exm0.
    left.
    intros.
    assumption.
    left.
    intros.
    exfalso.
    apply H.
    assumption.
  Qed.

  Lemma imp_translation : (P -> Q) <-> ~P \/ Q.
  Proof.
    split.
    - intros.
      add_exm P; destruct exm.
      + right; apply H; assumption.
      + left; assumption.
    - intros.
      destruct H.
      + exfalso; apply H; assumption.
      + assumption.
  Qed.

  Lemma Peirce : (( P -> Q) -> P) -> P.
  Proof.
    intro.
    add_exm P; destruct exm.
    assumption.
    apply H; intro.
    exfalso; apply H0; assumption.
  Qed.

  (* Quelques exercices d'anciens tests *) 
  Lemma test_1: (P->Q)->(~P->R)->(R->Q)->Q.
  Proof.
    intros.
    add_exm P; destruct exm.
    - apply H; assumption.
    - apply H1; apply H0; assumption. 
  Qed.

  Lemma test__2: (P \/ (Q\/R))-> (~P) -> (~R) -> (P\/Q).
  Proof.
    intros.
    destruct H.
    - left; assumption. 
    - destruct H.
      + right; assumption.
      + add_exm P; destruct exm. add_exm Q; destruct exm.
        * left; assumption.
        * left; assumption.
        * exfalso; apply H1; assumption. 
  Qed.

  Lemma test_3: (~P-> Q/\R)->(Q->~R)->P.
  Proof.
    intros.
    add_exm P; destruct exm.
    assumption.
    exfalso; apply H0.
    apply H.
    assumption.
    apply H.
    assumption.
  Qed.

  Lemma test_4: (~P->Q)->(~Q\/R)->(P->R)->R.
  Proof.
    intros.
    add_exm P; destruct exm; add_exm Q; destruct exm.
    - apply H1; assumption.
    - apply H1; assumption.
    - destruct H0.
      + exfalso; apply H0; assumption.
      + assumption.
    - destruct H0.
      + exfalso; apply H0; apply H; assumption.
      + assumption. 
  Qed.

  Lemma test_5: (P->Q)->(~P->~Q)->((P/\Q) \/ ~(P\/Q)).
  Proof.
    intros.
    add_exm P; destruct exm; add_exm Q; destruct exm.
    - left; split; assumption; assumption.
    - right.
      intro. 
      apply H2; apply H; assumption.
    - right.
      intro.
      apply H0.
      assumption.
      assumption. 
    - right.
      intro.
      destruct H3.
      + apply H1; assumption.
      + apply H2; assumption.
  Qed.

  Lemma test_6: (P->Q)->(~P->Q)->(Q->R)->R.
  Proof.
    intros.
    add_exm P; destruct exm; add_exm Q; destruct exm.
    - apply H1; assumption.
    - apply H1; apply H; assumption.
    - apply H1; assumption. 
    - apply H1; apply H0; assumption.
  Qed.

End LK.

Section Club_Ecossais. (* version propositionnelle *)
  Variables E R D M K: Prop.
  (* Ecossais, chaussettes Rouges, sort le Dimanche, Marié, Kilt *)

  Hypothesis h1: ~E -> R.
  (* Tout membre non ecossais porte des chaussettes rouges *)
  Hypothesis h2: M -> ~D.
  (* Les membres maries ne sortent pas le dimanche *)
  Hypothesis h3: D <-> E.
  (* Un membre sort le dimanche si et seulement si il est ecossais *)
  Hypothesis h4: K -> E /\ M.
  (* Tout membre qui porte un kilt est ecossais et est marie *)
  Hypothesis h5: R -> K.
  (* Tout membre qui porte des chaussettes rouges porte un kilt *)
  Hypothesis h6: E -> K.
  (* Tout membre ecossais porte un kilt. *)

  Lemma personne: False. (* Le club est vide! *)
  Proof.
    add_exm K; destruct exm; add_exm D; destruct exm.
    - apply h2.
      + apply h4; assumption.
      + assumption.
    - apply h2.
      + apply h4; assumption.
      + apply h3.
        apply h4.
        assumption. 
    - apply H; apply h6; apply h3; assumption.
    - add_exm E; destruct exm.
      + apply H0; apply h3; assumption.
      + apply H; apply h5; apply h1; assumption.
  Qed.

End Club_Ecossais.  
  
(** On peut sauter cette section *)

(* Au sens strict, cette partie est hors programme; il s'agit de voir que 
   diverses hypothèses (toutes formulées "au second ordre": avec des 
   quantificateurs universels sur des propositions)
   sont équivalentes, et correspondent à la logique classique *)
(* ATTENTION: pour que ces exercices aient un sens, il faut les faire SANS
   utiliser les tactiques réservées à la logique classique (add_exm, ou
   classical_left, ou classical_right *)
Section Second_ordre. 
  Definition PEIRCE := forall A B:Prop, ((A -> B) -> A) -> A.
  Definition DNEG := forall A, ~~A <-> A.
  Definition IMP2OR := forall A B:Prop, (A->B) <-> ~A \/ B.

  Lemma L2 : IMP2OR -> EXM.
  Proof.
    unfold IMP2OR, EXM.
    intros.
    assert (~ A \/ A).
    rewrite <- H. (* Coq "voit" qu'il suffit de prendre B=A; il va falloir prouver A->A *)
  Admitted.
  

  Lemma L3 : EXM -> DNEG.
  Proof.
    unfold DNEG , EXM.
    intros.
    (* H permet de faire un tiers exclus sur A *)
    assert (H0: A \/ ~A).
    {
      admit.
    }
  Admitted.

  Lemma L4 : PEIRCE -> DNEG.
  Proof.
    unfold DNEG , PEIRCE.
  Admitted.
  
  Lemma L5 : EXM -> PEIRCE.
  Proof.
  Admitted.

End Second_ordre.


  