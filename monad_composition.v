Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq path div choice fintype tuple.
From mathcomp Require Import finfun bigop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* jones and duponcheel, composing monads, sect 2, 3 *)

Require Import monad.

Module Comp.
Section comp.
Variables (M N : monad).
Definition F : functor (*(M \o N)*) := FComp M N.
Definition ret A : A -> FComp M N A := Ret \o Ret.
Lemma fmap_ret (A B : Type) (h : A -> B) : (F # h) \o (@ret _) = (@ret _) \o h.
Proof.
rewrite /ret.
rewrite -[in RHS]compA.
rewrite -(ret_naturality N h).
rewrite [in RHS]compA.
rewrite [in LHS]compA.
by rewrite ret_naturality.
Qed.
End comp.
End Comp.
Arguments Comp.ret {M} {N} {A}.

Module Prod.
Section prod.
Variables M N(* NB: actually, premonad is enough for N*) : monad.
Variable prod : forall A, N (M (N A)) -> M (N A).
Arguments prod {A}.

Definition JOIN A : Comp.F M N (Comp.F M N A) -> Comp.F M N A := Join \o M # prod.
Arguments JOIN {A}.

Definition prod1 := forall A B (f : A -> B), prod \o _ # (Comp.F M N # f) = Comp.F M N # f \o prod.
Definition prod2 := forall A, prod \o Ret = id :> (_ -> M (N A)).
Definition prod3 := forall A, prod \o _ # Comp.ret = Ret :> (_ -> M (N A)).
Definition prod4 := forall A, prod \o _ # JOIN = JOIN \o prod :> (_ -> M (N A)).
Hypothesis Hprod1 : prod1.
Hypothesis Hprod2 : prod2.
Hypothesis Hprod3 : prod3.
Hypothesis Hprod4 : prod4.

Lemma JOIN_naturality : JoinLaws.join_naturality (@JOIN).
Proof.
move=> A B g; apply/esym; rewrite {1}/JOIN -[in LHS]compA -functor_o Hprod1.
by rewrite functor_o compA /JOIN FCompE -(FCompE M M) -(@join_naturality M _ _ (N # g)) -compA.
Qed.

Lemma JOIN_ret : JoinLaws.left_unit (@Comp.ret _ _) (@JOIN).
Proof.
move=> A; rewrite /JOIN /Comp.ret compA.
rewrite -(compA Join (M # prod) Ret) (ret_naturality M prod).
by rewrite compA (compA Join) joinretM compidf Hprod2.
Qed.

Lemma JOIN_fmap_ret : JoinLaws.right_unit (@Comp.ret _ _) (@JOIN).
Proof.
move=> A.
by rewrite /JOIN /Comp.ret -compA -functor_o Hprod3 joinMret.
Qed.

Lemma JOIN_fmap_JOIN : JoinLaws.associativity (@JOIN).
Proof.
move=> A; rewrite {1 2}/JOIN -[in LHS]compA.
rewrite -functor_o.
rewrite Hprod4.
rewrite {1}/JOIN.
rewrite -(compA Join (M # prod) prod).
rewrite functor_o.
rewrite compA.
rewrite joinA.
rewrite -compA.
rewrite functor_o.
rewrite (compA Join (_ # (_ # prod)) (_ # prod)).
by rewrite -join_naturality.
Qed.

End prod.
End Prod.

Module Dorp.
Section dorp.
Variables M  (* actually, premonad is enough for M *) N : monad.
Variable dorp : forall A, M (N (M A)) -> M (N A).
Arguments dorp {A}.

Definition JOIN A : FComp M N (FComp M N A) -> FComp M N A := _ # Join \o dorp.
Arguments JOIN {A}.

Definition dorp1 := forall A B (f : A -> B), dorp \o Comp.F M N # (_ # f) = Comp.F M N # f \o dorp.
Definition dorp2 := forall A, (@dorp A) \o Comp.ret = _ # Ret.
Definition dorp3 := forall A, (@dorp A) \o Comp.F M N # Ret = id.
Definition dorp4 := forall A, (@dorp A) \o JOIN = JOIN \o Comp.F M N # dorp.
Hypothesis Hdorp1 : dorp1.
Hypothesis Hdorp2 : dorp2.
Hypothesis Hdorp3 : dorp3.
Hypothesis Hdorp4 : dorp4.

Lemma join_naturality : JoinLaws.join_naturality (@JOIN).
Proof.
move=> A B g; apply/esym; rewrite {1}/JOIN -compA Hdorp1.
rewrite compA.
rewrite (FCompE M N (N # g)).
rewrite -(functor_o M).
rewrite -join_naturality.
by rewrite functor_o.
Qed.

Lemma JOIN_ret : JoinLaws.left_unit (@Comp.ret _ _) (@JOIN).
Proof.
move=> A; rewrite /JOIN -compA Hdorp2.
rewrite -(functor_o M).
by rewrite joinretM functor_id.
Qed.

Lemma JOIN_fmap_ret : JoinLaws.right_unit (@Comp.ret _ _) (@JOIN).
Proof.
move=> A; rewrite /JOIN /Comp.ret.
rewrite -(compA (M # Join) dorp).
rewrite (functor_o (FComp M N)).
rewrite (compA dorp) Hdorp3.
rewrite compidf -functor_o.
by rewrite joinMret functor_id.
Qed.

Lemma JOIN_fmap_JOIN : JoinLaws.associativity (@JOIN).
Proof.
move=> A; rewrite {1 2}/JOIN.
rewrite FCompE.
rewrite (functor_o N).
rewrite -compA.
rewrite functor_o.
rewrite (compA dorp).
rewrite Hdorp1.
rewrite -(compA _ dorp).
rewrite (compA (M # Join)) -functor_o.
rewrite joinA.
rewrite functor_o.
rewrite -compA (compA (_ # Join) dorp).
rewrite -/JOIN.
rewrite -Hdorp4.
by rewrite compA.
Qed.

End dorp.
End Dorp.

Module Swap.
Section swap.
Variables M N : monad.
Variable swap : forall A, N (M A) -> M (N A).
Arguments swap {A}.

Definition JOIN A : FComp M N (FComp M N A) -> FComp M N A := _ # Join \o Join \o _ # (@swap (N A)).

Lemma JOINE A : @JOIN A = Join \o _ # (_ # Join \o swap).
Proof.
rewrite /JOIN join_naturality.
by rewrite -(compA Join) FCompE -functor_o.
Qed.

Let prod A := _ # (@Join _ A) \o (@swap _).
Arguments prod {A}.
Let dorp A := Join \o _ # (@swap A).
Arguments dorp {A}.

Fact JOIN_prod A : @JOIN A = Join \o _ # prod.
Proof. by rewrite JOINE. Qed.

Fact JOIN_dorp A : @JOIN A = _ # Join \o dorp.
Proof. by rewrite /dorp compA. Qed.

Definition swap1 := forall A B (f : A -> B), swap \o _ # (_ # f) = _ # (_ # f) \o swap .
Definition swap2 := forall A, @swap A \o Ret = _ # Ret :> (M A -> M (N A)).
Definition swap3 := forall A, @swap A \o _ # Ret = Ret :> (N A -> M (N A)).
Definition swap4 := forall A, (@prod A) \o _ # (@dorp _) = (@dorp _) \o (@prod _).
Hypothesis Hswap1 : swap1.
Hypothesis Hswap2 : swap2.
Hypothesis Hswap3 : swap3.
Hypothesis Hswap4 : swap4.

Lemma prod1 : Prod.prod1 (@prod).
Proof.
move=> A B f; rewrite {1}/prod.
rewrite -compA Hswap1 (compA (M # Join)) -functor_o.
by rewrite -join_naturality functor_o -compA.
Qed.

Lemma prod2 : Prod.prod2 (@prod).
Proof. by move=> A; rewrite /prod -compA Hswap2 -functor_o joinretM functor_id. Qed.

Lemma prod3 : Prod.prod3 (@prod).
Proof.
move=> A; rewrite /prod /Comp.ret.
rewrite (functor_o N) (compA (M # Join \o swap)) -(compA (_ # Join)) Hswap3.
by rewrite ret_naturality -compA joinMret compfid.
Qed.

Lemma prod4 : Prod.prod4 (@prod).
Proof.
move=> A; rewrite {1}/Prod.JOIN -JOIN_prod JOIN_dorp {1}/prod (functor_o N).
rewrite (compA (M # Join \o swap)) -(compA (_ # Join)) Hswap1.
rewrite (compA (M # Join)) -functor_o joinA functor_o.
rewrite -compA -(compA (_ # Join)) (compA (_ # Join) swap) -/prod Hswap4.
by rewrite compA /Prod.JOIN -JOIN_prod JOIN_dorp.
Qed.

Lemma dorp1 : Dorp.dorp1 (@dorp).
Proof.
move=> A B g; rewrite {1}/dorp -compA -functor_o.
by rewrite Hswap1 functor_o (compA Join) -join_naturality -compA.
Qed.

Lemma dorp2 : Dorp.dorp2 (@dorp).
Proof.
move=> A; rewrite /dorp /Comp.ret (compA (Join \o M # swap)) -(compA Join).
by rewrite ret_naturality (compA Join) joinretM compidf Hswap2.
Qed.

Lemma dorp3 : Dorp.dorp3 (@dorp).
Proof.
by move=> A; rewrite /dorp -compA -functor_o Hswap3 joinMret.
Qed.

Lemma dorp4 : Dorp.dorp4 (@dorp).
Proof.
move=> A; rewrite {1}/dorp {1}/Dorp.JOIN -JOIN_dorp JOIN_prod.
rewrite (compA (Join \o M # swap)) -(compA Join) join_naturality.
rewrite (compA Join Join) -joinA -2!compA FCompE -functor_o -(functor_o M).
by rewrite compA -/dorp -Hswap4 functor_o compA -JOINE JOIN_dorp.
Qed.

Lemma JOIN_naturality : JoinLaws.join_naturality (@JOIN).
Proof. by move=> ?? g; rewrite JOINE -/prod (Prod.JOIN_naturality prod1 g) JOINE. Qed.

Lemma JOIN_ret : JoinLaws.left_unit (@Comp.ret _ _) (@JOIN).
Proof. by move=> A; rewrite JOINE -/prod (Prod.JOIN_ret prod2). Qed.

Lemma JOIN_fmap_ret : JoinLaws.right_unit (@Comp.ret _ _) (@JOIN).
Proof. by move=> A; rewrite JOINE -/prod (Prod.JOIN_fmap_ret prod3). Qed.

Lemma JOIN_fmap_JOIN : JoinLaws.associativity (@JOIN).
Proof. by move=> A; rewrite !JOINE -!/prod (Prod.JOIN_fmap_JOIN prod4). Qed.

End swap.
End Swap.

(* monad morphism, Jaskelioff ESOP 2009 *)

From mathcomp Require Import boolp.

Module monadM.
Section monad_morphism.
Variables M N : monad.
Record t := mk {
  e : forall A (m : M A), N A ;
  ret : forall {A} (a : A), Ret a = e (Ret a) ;
  bind : forall {A B} (m : M A) (f : A -> M B),
    e (m >>= f) = e m >>= (fun a => e (f a))
}.
End monad_morphism.
Module Exports.
Notation monadM := t.
Definition coercion := e.
Coercion coercion : monadM >-> Funclass.
End Exports.
End monadM.
Export monadM.Exports.

Section monadM_lemmas.
Variables M N : monad.
Lemma monadMret (f : monadM M N) : forall {A} (a : A), Ret a = f _ (Ret a).
Proof. by case: f. Qed.
Lemma monadMbind (f : monadM M N) : forall {A B} (m : M A) (h : A -> M B),
  f _ (m >>= h) = f _ m >>= (fun a => f _ (h a)).
Proof. by case: f. Qed.
End monadM_lemmas.

Section monad_morphism.
Variables M N : monad.

Lemma natural_monad_morphism (f : monadM M N) : naturalP M N f.
Proof.
move=> A B h; rewrite funeqE => m /=.
have <- : Join ((M # (Ret \o h)) m) = (M # h) m.
  by rewrite functor_o [LHS](_ : _ = (Join \o M # Ret) ((M # h) m)) // joinMret.
move: (@monadMbind M N f A B m (Ret \o h)); rewrite 2!bindE => ->.
rewrite (_ : (fun a => f _ ((Ret \o h) a)) = Ret \o h); last first.
  by rewrite funeqE => y; rewrite -monadMret.
rewrite [RHS](_ : _ = (Join \o (N # Ret \o N # h)) (f _ m)); last first.
  by rewrite compE functor_o.
by rewrite compA joinMret.
Qed.

End monad_morphism.

Module MonadT.
Section monad_transformer.
Record t := mk {
  T : monad -> monad ;
  retT : forall (M : monad) A, A -> (T M) A ;
  bindT : forall (M : monad) A B (m : (T M) A) (f : A -> (T M) B), (T M) B ;
  liftT :> forall (M : monad), monadM M (T M)
}.
End monad_transformer.
Module Exports.
Notation monadT := t.
End Exports.
End MonadT.
Export MonadT.Exports.

From mathcomp Require Import boolp.

Section state_monad_transformer.

Local Obligation Tactic := idtac.

Variable S : Type.

Definition M0 (M : monad) := fun A => S -> M (A * S)%type.

Definition retS (M : monad) A (a : A) : M0 M A :=
  fun (s : S) => Ret (a, s) : M (A * S)%type.

Definition bindS (M : monad) A B (m : (M0 M) A) f :=
  (fun s => m s >>= uncurry f) : M0 M B.

Program Definition estateMonadM (M : monad) : monad :=
  @Monad_of_bind_ret (M0 M) (@bindS M) (retS M) _ _ _.
Next Obligation.
move=> M A B a f; rewrite /bindS funeqE => s.
by rewrite bindretf.
Qed.
Next Obligation.
move=> M A m; rewrite /bindS funeqE => s.
rewrite -[in RHS](bindmret (m s)); by bind_ext; case.
Qed.
Next Obligation.
move=> M A B C m f g; rewrite /bindS funeqE => s.
by rewrite bindA; bind_ext; case.
Qed.

Definition liftS (M : monad) A (m : M A) : (estateMonadM M) A :=
  fun s => @Bind M _ _ m (fun x => @Ret M _ (x, s)).

Program Definition stateMonadM (M : monad) : monadM M (estateMonadM M) :=
  @monadM.mk _ _ (@liftS M) _ _.
Next Obligation.
move=> M A a; rewrite /liftS funeqE => s.
by rewrite bindretf.
Qed.
Next Obligation.
move=> M A B m f; rewrite /liftS funeqE => s.
rewrite [in RHS]/Bind.
rewrite [in RHS]/Join /=.
rewrite /Monad_of_bind_ret.join /=.
rewrite /bindS.
rewrite !bindA.
bind_ext => a.
by rewrite !bindretf.
Qed.

Definition statemonad_transformer : monadT :=
  @MonadT.mk estateMonadM retS bindS stateMonadM.

End state_monad_transformer.
