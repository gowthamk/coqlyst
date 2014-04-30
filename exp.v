

Require Import Coq.Sets.Constructive_sets.
Require Import Arith.
Require Import Omega. 

(** ---- Case Tactic ---- **)
Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.
(* --- End Case Tactic -- *)

Module mylist1.
  Inductive list (X:Type) : Type :=
    | Nil : list X
    | Cons : X -> list X -> list X.

  Check Cons nat 0 (Cons nat 1 (Nil nat)).

End mylist1.
(*
 * Removing nat from above expression will not work
 * If we Set Implicit Arguments, then we *must*
 * remove nat from arguments of cons for the above 
 * expr to work.
 *)
Module mylist2.
  Set Implicit Arguments.
  Inductive list (X:Type) : Type :=
    | Nil : list X
    | Cons : X -> list X -> list X.
  
  Tactic Notation "list_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "Nil" | Case_aux c "Cons" ].
  
  Check Cons 0 (Cons 1 (Nil _)).
  
  Implicit Arguments Nil [X].

  Check Cons 0 Nil.
  Print list.

  Notation "x :: l" := (Cons x l) (at level 60, right associativity).
  Notation "[ ]" := (Nil) (at level 60).
  Notation "[ x , .. , y ]" := (Cons x .. (Cons y Nil) ..).

  Check [1,2,3].

  Fixpoint length (X:Type) (l : list X) : nat :=
    match l with 
    | [] => 0
    | x::xs => 1 + length xs
    end.

  Fixpoint concat (X:Type)(l1 l2: list X) : list _ :=
    match l1 with | [] => l2 | x::xs => x::(concat xs l2) end.

  Theorem concat_length : forall X:Type, forall (l1 l2 : list X), 
    length (concat l1 l2) = length l1 + length l2.
  Proof.
    intros. list_cases(induction l1 as [| x1 xs1]) Case.  
      Case "Nil"; trivial. 
      Case "Cons". simpl. rewrite <- IHxs1. trivial. 
  Qed.
  
  Hint Resolve concat_length.

  Notation "x ++ y" := (concat x y) (at level 60, right associativity).

  Fixpoint rev (X:Type) (l:list X) : list X :=
    match l with [] => [] | x::xs => (rev xs)++[x] end.

  Theorem rev_len_inv : forall X:Type, forall l:list X, 
    length l = length (rev l).
  Proof.
    intros; list_cases (induction l as [| x xs]) Case.
      Case "Nil"; trivial.
      Case "Cons"; simpl. rewrite -> concat_length. simpl. rewrite <- IHxs.
        (* Three ways to prove *)
        (* method 1 *)
        omega.
        (* method 2 *)
        (* rewrite plus_comm. trivial. *)
        (* method 3 *)
        (*
        assert (forall x:nat, S x = x+1).
          SCase "proof of assert". intros. 
        apply H with (x := length xs). 
        *)
  Qed.
  
  Inductive CrossPrd (A B : Type) (s1 : Ensemble A) (s2 : Ensemble B) 
      : Ensemble (A * B) :=
    CrossPrdIntro : forall x:A, forall y:B, In A s1 x -> In B s2 y -> 
                                            In (A*B) (CrossPrd s1 s2) (x,y).
  Fixpoint elts (A : Type)(l : list A) : Ensemble _:=
    match l with [] => Empty_set _ | x::xs => Union _ (Singleton _ x) (elts xs) end.

  Theorem empty_set_is_ident : forall A : Type, forall s : Ensemble A, 
                                 s = Union A (Empty_set A) s.

  Proof.
    intros; eapply Extensionality_Ensembles. unfold Same_set.
    split. 
      unfold Included. intros. apply Union_intror. assumption.
      unfold Included. intros. destruct H. destruct H. assumption.
  Qed.

  Theorem union_is_associative : forall A : Type, forall s1 s2 s3 : Ensemble A,
                                   Union _ (Union _ s1 s2) s3 = Union _ s1 (Union _ s2 s3).
  Proof.
    intros; eapply Extensionality_Ensembles. unfold Same_set.
    unfold Included. split.
      intros; inversion H.
          inversion H0. Check Union_introl. apply Union_introl. assumption.
          apply Union_intror. apply Union_introl. assumption.
          apply Union_intror. apply Union_intror. assumption.
      intros. inversion H.
          apply Union_introl. apply Union_introl. assumption.
          inversion H0. 
            apply Union_introl. apply Union_intror; assumption. 
            apply Union_intror. assumption.
  Qed.

  Theorem union_is_associative2 : forall A : Type, forall s1 s2 s3 : Ensemble A,
                                   Union _ (Union _ s1 s2) s3 = Union _ s1 (Union _ s2 s3).
  Proof.
    intros. apply Extensionality_Ensembles. unfold Same_set.
    unfold Included. split; intros ? H; inversion H; subst;
      try (inversion H0); auto with sets.
  Qed.

  Hint Resolve empty_set_is_ident.
  Hint Resolve union_is_associative.

  Theorem union_is_commutative : forall A : Type, forall s1 s2 : Ensemble A,
                                   Union _ s1 s2 = Union _ s2 s1.
  Proof.
    intros. apply Extensionality_Ensembles. unfold Same_set. 
      split; unfold Included; intros ? H; inversion H; subst; 
      try(inversion H0); auto with sets.
  Qed.
    
  Hint Resolve union_is_commutative.

  Theorem concat_preserves_elts : forall A : Type, forall l1 l2 : list A,
                                    elts (l1 ++ l2) = Union _ (elts l1) (elts l2).
  Proof.
    intros; list_cases(induction l1 as [| x1 xs1]) Case.
      Case "Nil"; simpl; auto.
      Case "Cons"; simpl; rewrite -> IHxs1; auto. 
  Qed.
  
  Theorem rev_preserves_elts : forall A : Type, forall l : list A, 
                                 elts l = elts (rev l ).
  Proof.
    intros; list_cases(induction l as [| x xs]) Case; trivial.
    Case "Cons"; simpl. rewrite concat_preserves_elts. simpl. rewrite <- IHxs.
      assert (forall s : Ensemble A, Union _ s (Empty_set _) = s).
        intros. rewrite -> empty_set_is_ident. auto.
      rewrite -> H. auto.
  Qed.

  Require Import CpdtTactics.

    Theorem rev_preserves_elts2 : forall A : Type, forall l : list A, 
                                 elts l = elts (rev l ).
  Proof.
    intros; list_cases(induction l as [| x xs]) Case; trivial.
    Case "Cons"; simpl. rewrite concat_preserves_elts. simpl. rewrite <- IHxs.
      assert (forall s : Ensemble A, Union _ s (Empty_set _) = s).
        intros. rewrite -> empty_set_is_ident. auto.
      crush.
  Qed.


End mylist2.

  


