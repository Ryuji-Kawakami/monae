(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
Ltac typeof X := type of X.

Require Import ssrmatching Reals JMeq.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require boolp.
From mathcomp Require Import mathcomp_extra Rstruct reals.
From infotheo Require Import Reals_ext.
From infotheo Require Import realType_ext.
Require Import monae_lib.
From HB Require Import structures.
Require Import hierarchy monad_lib fail_lib state_lib trace_lib.
Require Import monad_transformer.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Module Delay.
Section def.
CoInductive Delay (A : UU0) : Type :=
  DNow : A -> Delay A | DLater : Delay A -> Delay A.

Definition ret : idfun ~~> Delay := fun (A : UU0) x => DNow x.

CoFixpoint bind (A B : UU0) (m : Delay A) (f : A -> Delay B) :=
  match m with
  | DNow x => f x
  | DLater m' => DLater (bind m' f)
  end.

Lemma DelayE (A : UU0) (m : Delay A) :
  m = match m with
      | DNow x => DNow x
      | DLater m' => DLater m'
      end.
Proof. by case: m. Qed.

Lemma left_neutral : BindLaws.left_neutral bind ret.
Proof. by move=> A B a f; rewrite [LHS]DelayE [RHS]DelayE. Qed.

CoInductive Bisim (A : UU0) : Delay A -> Delay A -> Type :=
| BRefl (m : Delay A) : @Bisim A m m
| BLater (m m' : Delay A) :
  @Bisim A m m' -> @Bisim A (DLater m) (DLater m').
Arguments Bisim [A].
Arguments BLater [A].

Axiom Bisim_eq : forall A (m m' : Delay A), Bisim m m' -> m = m'.

CoFixpoint right_neutral_bisim A (m : Delay A) : Bisim (bind m (@ret A)) m.
case: m=> [a|m].
  rewrite [X in Bisim X]DelayE /=.
  exact: BRefl.
rewrite [X in Bisim X]DelayE /=.
apply: BLater.
exact: right_neutral_bisim.
Qed.

Lemma right_neutral : BindLaws.right_neutral bind ret.
Proof. by move=> *; exact/Bisim_eq/right_neutral_bisim. Qed.

CoFixpoint associative_bisim A B C (m : Delay A) (f : A -> Delay B)
                             (g : B -> Delay C) :
  Bisim (bind (bind m f) g) (bind m (fun x => bind (f x) g)).
Proof.
case: m=> [a|m].
  rewrite [X in Bisim _ X]DelayE.
  rewrite [X in Bisim X]DelayE.
  simpl.
  exact: BRefl.
rewrite [X in Bisim _ X]DelayE.
rewrite [X in Bisim X]DelayE.
simpl.
apply: BLater.
exact: associative_bisim.
Qed.

Lemma associative : BindLaws.associative bind.
Proof. move=> *; exact/Bisim_eq/associative_bisim. Qed.

HB.instance Definition _ := isMonad_ret_bind.Build
                              Delay left_neutral right_neutral associative.

End def.
End Delay.
