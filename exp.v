

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
    CrossPrd_intro : forall x:A, forall y:B, In A s1 x -> In B s2 y -> 
                                            In (A*B) (CrossPrd s1 s2) (x,y).
  
  Hint Constructors CrossPrd.

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

  Notation "{( x )}" := (Singleton _ x) (at level 60).
  Notation "x ** y" := (CrossPrd x y) (at level 65).
  Fixpoint Robs (A : Type) (l : list A) : Ensemble (A*A) := 
    match l with [] => Empty_set _ 
     | x::xs => Union _ (CrossPrd ({(x)}) (elts xs)) (Robs xs) end.

  Eval simpl in Robs ([1,2,3]).

  Fixpoint Roas (A : Type) (l : list A) : Ensemble (A*A) := 
    match l with [] => Empty_set _ 
     | x::xs => Union _ (CrossPrd (elts xs) ({(x)})) (Roas xs) end.

  Eval simpl in Roas ([1,2,3]).
  
  Check CrossPrd.
  Check Robs.
  Theorem empty_set_cross_prd : forall A B : Type, forall s : Ensemble A,
                                  CrossPrd s (Empty_set B) = Empty_set (A*B) /\
                                  CrossPrd (Empty_set B) s = Empty_set (B*A).
  Proof.
    intros. split; apply Extensionality_Ensembles; unfold Same_set; 
    unfold Included; split; intros ? H; inversion H; try (inversion H1); 
    try (inversion H0).
  Qed.

  Hint Resolve empty_set_cross_prd.
  
  Theorem cross_prd_distributes : forall A B : Type, forall s1 : Ensemble A,
    forall s2 s3 : Ensemble B, 
      s1 ** (Union _ s2 s3) = Union _ (s1 ** s2) (s1 ** s3) /\
      (Union _ s2 s3) ** s1 = Union _ (s2 ** s1) (s3 ** s1).
  Proof.
    intros. split; apply Extensionality_Ensembles; unfold Same_set; 
      split; unfold Included; intros ? H; inversion H; subst;
      try(inversion H1); try (inversion H0); auto with *.
  Qed.

  Theorem cross_prd_distributesr : forall A B : Type, forall s1 : Ensemble A,
    forall s2 s3 : Ensemble B, 
      s1 ** (Union _ s2 s3) = Union _ (s1 ** s2) (s1 ** s3).
  Proof. intros; apply cross_prd_distributes. Qed.

  Theorem cross_prd_distributesl : forall A B : Type, forall s1 : Ensemble A,
    forall s2 s3 : Ensemble B, 
      (Union _ s2 s3) ** s1 = Union _ (s2 ** s1) (s3 ** s1).
  Proof. intros; apply cross_prd_distributes. Qed.
 
  Hint Resolve cross_prd_distributesl.
  Hint Resolve cross_prd_distributesr.
  Hint Rewrite cross_prd_distributesl.
  Hint Rewrite cross_prd_distributesr.
  Hint Rewrite union_is_associative.
  Hint Rewrite union_is_commutative.

 
  Notation "x @ y" := (Union _ x y) (at level 69, left associativity).

  Require Import LibTactics.
  Theorem concat_robs : forall A : Type, forall l1 l2 : list A, 
    Robs (l1 ++ l2) = ((Robs(l1)) @ (Robs(l2))) @
                           ((elts l1) ** (elts l2)).
  Proof.
    intros; list_cases(induction l1 as [|x1 xs1]) Case; simpl.
    Case "Nil".
      assert (CrossPrd (Empty_set A) (elts l2) = Empty_set (A*A)).
        apply empty_set_cross_prd.
      rewrite H. rewrite union_is_commutative. 
      repeat (rewrite <- empty_set_is_ident); trivial.
    Case "Cons".
      rewrite concat_preserves_elts. 
      rewrite IHxs1.
      assert ( ({(x1)} @ (elts xs1)) ** elts l2 = 
              ({(x1)} ** (elts l2)) @ ((elts xs1) ** (elts l2))).
        auto.
      rewrite H.
      assert ({(x1)} ** (elts xs1 @ elts l2) = 
              {(x1)} ** (elts xs1) @ {(x1)} ** (elts l2)).
        auto.
      rewrite H0. repeat (rewrite <- union_is_associative).
      assert ({(x1)} ** elts xs1 @ {(x1)} ** elts l2 @ Robs xs1 = 
              {(x1)} ** elts xs1 @ ({(x1)} ** elts l2 @ Robs xs1)).
        auto.
      rewrite H1.
      assert ({(x1)} ** elts l2 @ Robs xs1 = Robs xs1 @ {(x1)} ** elts l2).
        auto.
      rewrite H2.
      assert ({(x1)} ** elts xs1 @ (Robs xs1 @ {(x1)} ** elts l2) = 
              {(x1)} ** elts xs1 @ Robs xs1 @ {(x1)} ** elts l2).
        auto.
      rewrite H3.
      assert ({(x1)} ** elts xs1 @ Robs xs1 @ {(x1)} ** elts l2 @ Robs l2 = 
              {(x1)} ** elts xs1 @ Robs xs1 @ ({(x1)} ** elts l2 @ Robs l2)).
        auto.
      rewrite H4.
      assert (({(x1)} ** elts l2 @ Robs l2) = (Robs l2 @ {(x1)} ** elts l2)).
        auto.
      rewrite H5.
      assert ({(x1)} ** elts xs1 @ Robs xs1 @ (Robs l2 @ {(x1)} ** elts l2) =
              {(x1)} ** elts xs1 @ Robs xs1 @ Robs l2 @ {(x1)} ** elts l2).
        auto.
      rewrite H6. reflexivity.
  Qed.

End mylist2.

  


