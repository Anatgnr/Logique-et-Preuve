Section RichMen.
  Variable P: Type. (* personnes *)
  Variable f: P->P. (* père *)
  Variable r: P->Prop. (* être riche *)

  (* toute personne est riche ou n'est pas riche 
     (ou alors on peut faire l'exercice en logique classique) *)
  Hypothesis rich_not_rich: forall x:P, r(x) \/ ~r(x).

  (* On nous donne un exemple de personne *)
  Variable s: P.

  (* personne riche dont le grand-père est riche *)
  Definition ploutocrate x := r x /\ r (f (f x)).

  (* On suppose que tout non-riche a un père riche *)
  Hypothesis rich_father: forall x:P, ~r x -> r (f x).

(* Le but est de montrer l'existence d'un riche dont le grand-père est riche
   (un ploutocrate) *)

(* On commence par montrer une propriété intermédiaire: si une personne
   est riche, cette personne est un ploutocrate, OU son père est un
   ploutocrate *)

  Lemma richman: forall x:P, r x -> ploutocrate x \/ ploutocrate (f x).
  Proof.
  Admitted.

(* On va se servir du lemme richman pour montrer l'existence
   d'un ploutocrate *)

  Theorem plouto: exists x:P, ploutocrate x.
  Proof.
  Admitted.

End RichMen.