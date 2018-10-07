Require Import FunctionalExtensionality Coq.Program.Tactics ProofIrrelevance.
Require Import Coq.Logic.IndefiniteDescription.
Require Classical.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple.
Require Import ZArith ssrZ.
Require Import monad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Contents:
- Module MonadState.
    n-queens example
- Module MonadStateRun.
- Module MonadNondetState.
    state + nondeterminism
    eight queens puzzle
- Module MonadFresh.
- Module MonadFailFresh.
    example of tree relabeling
- n-queens puzzle by Mu
  sections 4-5
*)

Module MonadState.
Record mixin_of S (M : monad) : Type := Mixin {
  get : M S ;
  put : S -> M unit ;
  _ : forall s s', put s >> put s' = put s' ;
  _ : forall s, put s >> get = put s >> Ret s ;
  _ : get >>= put = skip ;
  _ : forall k : S -> S -> M S,
    get >>= (fun s => get >>= k s) = get >>= fun s => k s s
}.
Record class_of S (m : Type -> Type) := Class {
  base : Monad.class_of m ; mixin : mixin_of S (Monad.Pack base) }.
Structure t S : Type := Pack { m : Type -> Type ; class : class_of S m }.
Definition op_get S (M : t S) : m M S :=
  let: Pack _ (Class _ (Mixin x _ _ _ _ _)) := M return m M S in x.
Arguments op_get {S M} : simpl never.
Definition op_put S (M : t S) : S -> m M unit :=
  let: Pack _ (Class _ (Mixin _ x _ _ _ _)) := M return S -> m M unit in x.
Arguments op_put {S M} : simpl never.
(* inheritance *)
Definition baseType S (M : t S) := Monad.Pack (base (class M)).
Module Exports.
Notation Get := op_get.
Notation Put := op_put.
Notation stateMonad := t.
Coercion baseType : stateMonad >-> monad.
Canonical baseType.
End Exports.
End MonadState.
Export MonadState.Exports.

Section state_lemmas.
Variables (S : Type) (M : stateMonad S).
Lemma putget s : Put s >> Get = Put s >> Ret s :> M _.
Proof. by case: M => m [[? ? ? ? ? []] ]. Qed.
Lemma getputskip : Get >>= Put = skip :> M _.
Proof. by case: M => m [[? ? ? ? ? []] ]. Qed.
Lemma putput s s' : Put s >> Put s' = Put s' :> M _.
Proof. by case: M => m [[? ? ? ? ? []] ]. Qed.
Lemma getget (k : S -> S -> M S ) :
 (Get >>= (fun s => Get >>= k s)) = (Get >>= fun s => k s s).
Proof. by case: M k => m [[? ? ? ? ? []] ]. Qed.
End state_lemmas.

Lemma putgetput S {M : stateMonad S} x {B} (k : _ -> M B) :
  Put x >> Get >>= (fun x' => k x') = Put x >> k x :> M _.
Proof. by rewrite putget bindA bindretf. Qed.

Definition overwrite {A S} {M : stateMonad S} s a : M A :=
  Put s >> Ret a.

Definition place n {B} (rs : seq B) := zip (map Z_of_nat (iota 0 n)) rs.

Definition empty {B} : (seq B * seq B):= ([::] , [::]).

Section nqueens.

(* input: queen position, already threatened up/down diagonals
   output: safe or not, update up/down diagonals *)
Definition test : Z`2 -> (seq Z)`2 -> bool * (seq Z)`2 :=
  fun '(c, r) '(upds, downs) =>
    let (u, d) := (r - c, r + c)%Z in
    ((u \notin upds) && (d \notin downs), (u :: upds, d :: downs)).

Section purely_functional.

Definition start1 : (seq Z)`2 -> bool * (seq Z)`2 :=
  fun updowns => (true, updowns).

Definition step1 : Z`2 -> (bool * (seq Z)`2) -> bool * (seq Z)`2 :=
  fun cr '(restOK, updowns) =>
    let (thisOK, updowns') := test cr updowns in
    (thisOK && restOK, updowns').

(* over the list of column-row pairs
   bool * (seq Z)`2: queens to the right safe or not,
                       up/down diagonals under threat from the queens so far *)
Definition safe1 : (seq Z)`2 -> seq Z`2 -> bool * (seq Z)`2 :=
  foldr step1 \o start1.

Definition queens {M : nondetMonad} n : M (seq Z) :=
  do rs <- perms (map Z_of_nat (iota 0 n)) ;
     (guard (safe1 empty (place n rs)).1 >> Ret rs).

End purely_functional.

Section statefully.
(* statefully constructing the sets of up/down diagonals threatened by the queens so far *)

Variable M : stateMonad (seq Z)`2.

Definition start2 : M bool := Ret true.

Definition step2 (cr : Z`2) (k : M bool) : M bool :=
  do b' <- k ;
  do uds <- Get;
  let (b, uds') := test cr uds in
  Put uds' >> Ret (b && b').

Definition safe2 : seq Z`2 -> M bool :=
  foldr step2 start2.

Lemma safe2E crs :
  safe2 crs = do uds <- Get; let (ok, uds') := safe1 uds crs in
                             (Put uds' >> Ret ok).
Proof.
(* TODO(rei): how to write this proof w.o. the "set" and "transitivity"'s? *)
apply/esym; rewrite /safe2.
set f := fun x => do uds <- Get; let (ok, uds') := safe1 uds x in Put uds' >> Ret ok : M _.
rewrite -(@foldr_universal_ext _ _ _ _ f) //;
  [apply/esym|move=> cr {crs}crs; apply/esym].
  by rewrite /start2 /f /= -bindA getputskip bindskipf.
(* definition of safe1 *)
transitivity
  (do uds <- Get;
  let (ok, uds') := step1 cr (safe1  uds crs) in Put uds'>> Ret ok : M _); last first.
  by [].
(* introduce a let *)
transitivity
  (do uds <- Get;
  let (b', uds'') := safe1 uds crs in
  let (ok, uds') := step1 cr (b', uds'') in Put uds' >> Ret ok : M _); last first.
  bind_ext => x.
  by case: safe1.
(* definition of step1 *)
transitivity
  (do uds <- Get;
  let (b', uds'') := safe1 uds crs in
  let (b, uds''') := test cr uds'' in
  let (ok, uds') := (b && b', uds''') in Put uds' >> Ret ok : M _); last first.
  bind_ext => x.
  case: safe1 => // h t.
  rewrite /step1 /=.
  by case: test.
transitivity
  (do uds <- Get;
  let (b', uds'') := safe1 uds crs in
  let (b, uds''') := test cr uds'' in
  let (ok, uds') := (b && b', uds''') in (Put uds'' >> Put uds' >> Ret ok) : M _); last first.
  bind_ext => x.
  case: safe1 => // h t.
  case: test => // a b.
  by rewrite putput.
(* move two of the lets *)
transitivity
  (do uds <- Get;
  let (b', uds'') := safe1 uds crs in
  Put uds'' >>
  let (b, uds''') := test cr uds'' in
  let (ok, uds') := (b && b', uds''') in Put uds' >> Ret ok : M _); last first.
  bind_ext => x.
  case: safe1 => // h t.
  case: test => // a b.
  by rewrite bindA.
transitivity
  (do uds <- Get;
  let (b', uds'') := safe1 uds crs in
  Put uds'' >>
  do uds'''' <- Get ;
  let (b, uds''') := test cr uds'''' in
  let (ok, uds') := (b && b', uds''') in Put uds' >> Ret ok : M _); last first.
  bind_ext => x.
  case: safe1 => // h t.
  by rewrite -bindA putgetput.
transitivity
  (do
   b' <- (do uds <- Get ; let (ok, uds'') := safe1 uds crs in Put uds'' >> Ret ok) ;
   (do uds'''' <- Get;
   let (b, uds''') := test cr uds'''' in
   let (ok, uds') := (b && b', uds''') in Put uds' >> Ret ok) : M _); last first.
  rewrite bindA; bind_ext => x.
  case: safe1 => // h t.
  by rewrite bindA; rewrite_ bindretf.
by [].
Qed.

End statefully.

End nqueens.
Arguments step2 {M}.
Arguments safe2 {M}.
Arguments start2 {M}.

Definition test_nonce0 (M : stateMonad nat) : M nat :=
  Get >>= (fun s => Put s.+1 >> Ret s).
Reset test_nonce0.
Fail Check test_nonce0.

Module MonadRun.
Record mixin_of S (M : monad) : Type := Mixin {
  run : forall A, M A -> S -> A * S ;
  _ : forall A (a : A) s, run (Ret a) s = (a, s) ;
  _ : forall A B (m : M A) (f : A -> M B) s,
      run (do a <- m ; f a) s =
      let: (a', s') := run m s in run (f a') s'
}.
Record class_of S (m : Type -> Type) := Class {
  base : Monad.class_of m ;
  mixin : mixin_of S (Monad.Pack base)
}.
Structure t S : Type := Pack { m : Type -> Type ;
  class : class_of S m }.
Definition op_run S (M : t S) : forall A, m M A -> S -> A * S :=
  let: Pack _ (Class _ (Mixin x _ _)) := M
  return forall A, m M A -> S -> A * S in x.
Arguments op_run {S M A} : simpl never.
Definition baseType S (M : t S) := Monad.Pack (base (class M)).
Module Exports.
Notation runMonad := t.
Notation Run := op_run.
Coercion baseType : runMonad >-> monad.
Canonical baseType.
End Exports.
End MonadRun.
Export MonadRun.Exports.

Section run_lemmas.
Variables (S : Type) (M : runMonad S).
Lemma runret : forall A (a : A) s, Run (Ret a : M _) s = (a, s).
Proof. by case: M => m [? []]. Qed.
Lemma runbind : forall A B (ma : M A) (f : A -> M B) s,
  Run (do a <- ma ; f a) s = let: (a', s') := Run ma s in Run (f a') s'.
Proof. by case: M => m [? []]. Qed.
End run_lemmas.

Module MonadStateRun.
Record mixin_of S (M : runMonad S) (get : M S) (put : S -> M unit) : Type := Mixin {
  _ : forall s, Run get s = (s, s) ;
  _ : forall s s', Run (put s') s = (tt, s') ;
}.
Record class_of S (m : Type -> Type) := Class {
  base : MonadState.class_of S m ;
  base2 : MonadRun.mixin_of S (Monad.Pack (MonadState.base base)) ;
  mixin : @mixin_of S (MonadRun.Pack (MonadRun.Class base2)) (@MonadState.op_get _ (MonadState.Pack base)) (@MonadState.op_put _ (MonadState.Pack base)) ;
}.
Structure t S : Type := Pack { m : Type -> Type ;
  class : class_of S m }.
Definition baseType S (M : t S) := MonadState.Pack (base (class M)).
Module Exports.
Notation stateRunMonad := t.
Coercion baseType : stateRunMonad >-> stateMonad.
Canonical baseType.
Definition state_of_run S (M : stateRunMonad S) : runMonad S :=
  MonadRun.Pack (MonadRun.Class (base2 (class M))).
Canonical state_of_run.
End Exports.
End MonadStateRun.
Export MonadStateRun.Exports.

Section staterun_lemmas.
Variables (S : Type) (M : stateRunMonad S).
Lemma runget : forall s, Run (Get : M _) s = (s, s).
Proof. by case: M => m [? ? []]. Qed.
Lemma runput : forall s s', Run (Put s' : M _) s = (tt, s').
Proof. by case: M => m [? ? []]. Qed.
End staterun_lemmas.

Section safe_reification.

Variable M : stateRunMonad (seq Z)`2.

Lemma run_safe2 crs updowns : Run (safe2 crs : M _) updowns = safe1 updowns crs.
Proof.
rewrite safe2E runbind runget; case: safe1 => a b.
by rewrite runbind runput runret.
Qed.

End safe_reification.

Module MonadNondetState.
Record mixin_of (M : nondetMonad) : Type := Mixin {
  (* backtrackable state *)
  _ : Laws.right_zero (@Bind M) (@Fail _) ;
  (* composition distributes rightwards over choice *)
  _ : Laws.bind_right_distributive (@Bind M) [~p]
}.
Record class_of S (m : Type -> Type) : Type := Class {
  base : MonadNondet.class_of m ;
  base2 : MonadState.mixin_of S (MonadFail.baseType (MonadNondet.baseType (MonadNondet.Pack base))) ;
  mixin : mixin_of (MonadNondet.Pack base)
}.
Structure t S : Type := Pack { m : Type -> Type ; class : class_of S m }.
Definition baseType S (M : t S) := MonadNondet.Pack (base (class M)).
Module Exports.
Notation nondetStateMonad := t.
Coercion baseType : nondetStateMonad >-> nondetMonad.
Canonical baseType.
Definition state_of_nondetstate S (M : nondetStateMonad S) :=
  MonadState.Pack (MonadState.Class (base2 (class M))).
Canonical state_of_nondetstate.
End Exports.
End MonadNondetState.
Export MonadNondetState.Exports.

Section nondetstate_lemmas.
Variables (S : Type) (M : nondetStateMonad S).
Lemma bindmfail : Laws.right_zero (@Bind M) (@Fail _).
Proof. by case: M => m [? ? [? ?]]. Qed.
Lemma alt_bindDr : Laws.bind_right_distributive (@Bind M) [~p].
Proof. by case: M => m [? ? []]. Qed.
End nondetstate_lemmas.

Lemma getput_prepend S (M : nondetStateMonad S) A (m : M A) :
  m = do x <- Get; (Put x >> m).
Proof. by rewrite -{2}(bindskipf m) -bindA getputskip 2!bindskipf. Qed.

Section state_commute.

Variables (S : Type) (M : nondetStateMonad S).

Lemma puttselectC (x : S) A (s : seq A) B (f : _ -> M B) :
  Put x >> (do rs <- tselect s; f rs) =
  do rs <- tselect s; Put x >> f rs.
Proof.
elim: s f => [|h t IH] f.
  by rewrite tselect_nil 2!bindfailf bindmfail.
  case: t IH f => [|h' t] IH f.
  by rewrite tselect1 !bindretf.
rewrite tselect_cons // => H.
rewrite [in LHS]alt_bindDl [in RHS]alt_bindDl alt_bindDr.
congr (_ [~i] _); first by rewrite 2!bindretf.
rewrite 2!bindA IH; bind_ext => y; by rewrite !bindretf.
Qed.

Lemma putselectC (x : S) A (s : seq A) (B : Type) (f : A * (seq A) -> M B) :
  Put x >> (do rs <- select s; f rs) = do rs <- select s; Put x >> f rs.
Proof.
rewrite selectE {1}/fmap.
rewrite_ bindA.
rewrite puttselectC /fmap bindA.
bind_ext => x0; by rewrite 2!bindretf.
Qed.

Lemma gettselectC A (s : seq A) B (f : _ -> _ -> M B) :
  do ini <- Get; do rs <- tselect s; f rs ini =
  do rs <- tselect s; do ini <- Get; f rs ini.
Proof.
elim: s f => [|h t IH] f.
  rewrite tselect_nil bindfailf; rewrite_ bindfailf; by rewrite bindmfail.
case: t IH f => [|h' t] IH f.
  rewrite tselect1 bindretf; by rewrite_ bindretf.
rewrite tselect_cons // => H.
rewrite [tselect _]lock.
rewrite_ alt_bindDl.
rewrite [in RHS]alt_bindDl alt_bindDr.
congr (_ [~i] _).
  rewrite bindretf; bind_ext => ?; by rewrite bindretf.
rewrite -lock.
transitivity (
  do x0 <- tselect (h' :: t);
  do x <- Get; f (x0.1, Tuple (monad.tselect_cons_statement_obligation_2 h H x0)) x).
 rewrite -IH; bind_ext => x.
 rewrite bindA;by rewrite_ bindretf.
rewrite bindA; bind_ext => y; by rewrite bindretf.
Qed.

(* perms is independent of the state and so commutes with put *)
Lemma putpermsC (x : S) A (s : seq A) B (f : _ -> M B) :
  Put x >> (do rs <- perms s; f rs) =
  do rs <- perms s; Put x >> f rs.
Proof.
move Hn : (size s) => n.
elim: n s Hn x f => [|n IH] s Hn x f.
  by case: s Hn => // _; rewrite permsE 2!bindretf.
case: s Hn => // h t [Hn].
rewrite tpermsE 2!bindA puttselectC; bind_ext; case=> a b.
rewrite 2!bindA.
have bn : size b = n by rewrite size_tuple.
rewrite IH //.
by do 2! rewrite_ bindretf.
Qed.

Lemma getpermsC A (s : seq A) B (f : _ -> _ -> M B) :
  do ini <- Get; (do rs <- perms s; f rs ini) =
  do rs <- perms s; do ini <- Get; f rs ini.
Proof.
move Hn : (size s) => n.
elim: n s Hn f => [|n IH] s Hn f.
  case: s Hn => // _; rewrite permsE.
  by rewrite bindretf; rewrite_ bindretf.
case: s Hn => // h t [Hn].
rewrite tpermsE bindA.
transitivity (do x <- tselect (h :: t); do ini <- Get; do rs <- perms x.2;
  f (x.1 :: rs) ini); last first.
  bind_ext => x.
  rewrite IH ?size_tuple // bindA.
  by rewrite_ bindretf.
rewrite -gettselectC.
bind_ext => x.
rewrite bindA; bind_ext => rs.
rewrite bindA.
by rewrite_ bindretf.
Qed.

End state_commute.

Definition nondetState_sub {S} {M : nondetStateMonad S} {A} (n : M A) : Type :=
  {m | ndDenote m = n}.

Lemma select_is_nondetState S (M : nondetStateMonad S) A (s : seq A) :
  nondetState_sub (select s : M _).
Proof.
elim: s => [/= | u v [x /= <-]]; first by exists (@ndFail _).
by exists (ndAlt (ndRet (u, v)) (ndBind x (fun x => ndRet (x.1, u :: x.2)))).
Qed.

Lemma unfoldM_is_nondetState S (M : nondetStateMonad S) A B
  (f : seq B -> M (A * seq B)%type) :
  (forall s, nondetState_sub (f s)) -> bassert_size f ->
  forall s, nondetState_sub (unfoldM (@well_founded_size B) (@nilp _) f s).
Proof.
move=> Hf size_f s.
apply/constructive_indefinite_description.
move: s; apply: (well_founded_induction (@well_founded_size _)) => s IH.
have {IH}IH : forall x, size x < size s ->
  { m | ndDenote m = unfoldM (@well_founded_size B) (@nilp _) f x}.
  move=> x xs; exact/constructive_indefinite_description/IH.
case: s IH => [|h t] IH.
  rewrite unfoldME //=; by exists (ndRet [::]).
rewrite unfoldME //=.
case: (Hf (h :: t)) => x Hx.
rewrite -Hx /fmap.
set g := fun y => match Bool.bool_dec (size y < size (h :: t)) true with
               | left H => let: exist x _ := IH _ H in x
               | _ => ndRet [::]
               end.
refine (ex_intro _ (ndBind x (fun x => ndBind (g x.2) (@ndRet _ \o cons x.1 ))) _) => /=.
rewrite Hx size_f /bassert !bindA.
bind_ext => -[x1 x2].
rewrite /assert /guard /= ltnS.
case: ifPn => b1b2; last by rewrite !bindfailf.
rewrite !bindskipf !bindretf /= /g.
case: Bool.bool_dec => //= x2t.
by case: (IH x2) => // x0 <-.
Qed.

(* theorem 5.2, mu2017 *)
Lemma commute_nondetState {S} {M : nondetStateMonad S}
  A (m : M A) B (n : M B) C (f : A -> B -> M C) :
  nondetState_sub m -> commute m n f.
Proof.
case => x.
elim: x m n f => [{A}A a m n f <-| B0 {A}A n0 H0 n1 H1 m n2 f <- |
  A0 m n f <- | A0 n0 H0 n1 H1 m n2 f <-].
- rewrite /commute bindretf.
  by rewrite_ bindretf.
- rewrite /commute /= !bindA.
  transitivity (do x <- ndDenote n0; do y <- n2 : M _; do x0 <- ndDenote (n1 x);
    f x0 y).
    bind_ext => s.
    by rewrite (H1 s).
  rewrite H0 //.
  bind_ext => b.
  by rewrite bindA.
- rewrite /commute /= bindfailf.
  transitivity (do y <- n; Fail : M C); first by rewrite bindmfail.
  bind_ext => b.
  by rewrite bindfailf.
- rewrite /commute /= alt_bindDl.
  transitivity (do y <- n2; (do x <- ndDenote n0 ; f x y) [~i] do x <- ndDenote n1; f x y); last first.
    bind_ext => a.
    by rewrite alt_bindDl.
  by rewrite alt_bindDr H0 // H1.
Qed.

Section queens_statefully_nondeterministically.

Variable M : nondetStateMonad (seq Z)`2.

Definition queens_state_nondeter n : M (seq Z) :=
  do s <- Get ;
    do rs <- perms (map Z_of_nat (iota 0 n));
      Put empty >>
        (do ok <- safe2 (place n rs) ;
             (Put s >> guard ok)) >> Ret rs.

Lemma queensE n : queens n = queens_state_nondeter n.
Proof.
rewrite (getput_prepend (queens n)) /queens_state_nondeter; bind_ext => x.
rewrite {1}/queens putpermsC; bind_ext => y.
rewrite safe2E.
set f := (do ok <- (do _ <- _; _); _ >> guard ok in RHS).
rewrite (_ : f =
  do uds <- Get; Put (safe1 uds (place n y)).2 >> Ret (safe1 uds (place n y)).1 >>
      Put x >> guard (safe1 uds (place n y)).1); last first.
  rewrite {}/f bindA; bind_ext => u.
  case: (safe1 _ _) => a b.
  rewrite 2!bindA bindretf bindA.
  by rewrite_ bindretf.
rewrite -bindA; congr (_ >> _).
rewrite -bindA.
rewrite putgetput.
rewrite 2!bindA.
rewrite bindretf.
rewrite -2!bindA.
by rewrite 2!putput.
Qed.

End queens_statefully_nondeterministically.
Arguments queens_state_nondeter {M}.

Section queens_exploratively.

Variable M : nondetStateMonad (seq Z)`2.

Definition queens_explor n : M _ :=
  do s <- Get;
    do rs <- perms (map Z_of_nat (iota 0 n));
      Put empty >>
        (do ok <- safe2 (place n rs) ;
             (guard ok >> Put s)) >> Ret rs.

Lemma queens_explorE n : queens_explor n = queens_state_nondeter n.
Proof.
rewrite /queens_explor /queens_state_nondeter.
bind_ext => x.
bind_ext => y.
rewrite 2!bindA.
bind_ext => z.
rewrite 2!bindA.
bind_ext => u.
rewrite guardsC; last exact: bindmfail.
rewrite 2!bindA.
rewrite_ bindA.
by rewrite_ bindretf.
Qed.

Definition safe3 crs : M _ := safe2 crs >>= fun b => guard b.

Definition queens_safe3 n : M _ :=
  do s <- Get;
    (do rs <- perms (map Z_of_nat (iota 0 n)) ;
      Put empty >> safe3 (place n rs) >> Put s >> Ret rs).

Lemma queens_safe3E n : queens_safe3 n = queens_explor n :> M _.
Proof.
rewrite /queens_safe3 /queens_explor; bind_ext => x.
bind_ext => y.
rewrite 3!bindA.
bind_ext; case.
rewrite !bindA.
by rewrite_ bindA.
Qed.

Definition step3 B cr (m : M B) := m >>
  do uds <- Get ; let (b, uds') := test cr uds in Put uds' >> guard b.

Lemma safe3E crs :
  safe3 crs = foldr (@step3 unit) skip crs :> M _.
Proof.
(* TODO(rei): how to write this proof w.o. the "set" and "transitivity"'s? *)
transitivity (((fun x => x >>= (guard : _ -> M _)) \o
               (foldr step2 start2))
              crs).
  by [].
apply foldr_fusion_ext => [|cr {crs}k].
  by rewrite /= /safe3 /= /start2 /= bindretf.
transitivity ((do b' <- k ;
               do uds <- Get ;
               let (b, uds') := test cr uds in
               Put uds' >> Ret (b && b')) >>= guard).
  by rewrite /step2.
transitivity (do b' <- k ;
              do uds <- Get ;
              let (b, uds') := test cr uds in
              Put uds' >> guard (b && b')).
  (* by "do-notation" *)
  rewrite bindA; bind_ext => x.
  rewrite bindA; bind_ext => y.
  case: (test cr y) => a b.
  by rewrite bindA bindretf.
transitivity (do b' <- k ;
              do uds <- Get ;
              let (b, uds') := test cr uds in
              Put uds' >> guard b >> guard b').
  bind_ext => x.
  bind_ext => y.
  case: (test cr y) => a b.
  by rewrite bindA guard_and.
transitivity (do b' <- k ;
              guard b' >> (do uds <- Get ;
                           let (b, uds') := test cr uds in
                           Put uds' >> guard b)).
  bind_ext => b'.
  rewrite guardsC; last exact: bindmfail.
  rewrite bindA.
  bind_ext => x.
  case: test => h t.
  rewrite 2!bindA.
  bind_ext; case.
  rewrite -guard_and andbC guard_and guardsC //.
  exact: bindmfail.
transitivity ((k >>= guard) >>
               do uds <- Get ;
                 let (b, uds') := test cr uds in
                 Put uds' >> guard b).
  by rewrite bindA.
by [].
Qed.

End queens_exploratively.

(* tree-relabelling example *)

Definition intersect {A : eqType} (s t : seq A) : seq A := filter (mem s) t.

Lemma nilp_intersect (A : eqType) (s t : seq A) :
  nilp (intersect s t) = ~~ has (mem s) t.
Proof. by rewrite /intersect /nilp size_filter has_count lt0n negbK. Qed.

Definition seq_disjoint {A : eqType} : pred [eqType of (seq A)`2] :=
  (@nilp _) \o uncurry intersect.

Lemma intersect0s (A : eqType) (s : seq A) : intersect [::] s = [::].
Proof. by elim: s. Qed.

Module MonadFresh.
Record mixin_of (S : eqType) (m : Type -> Type) : Type := Mixin {
  fresh : m S }.
Record class_of S (m : Type -> Type) : Type := Class {
  base : Monad.class_of m ;
  mixin : mixin_of S m }.
Structure t S := Pack { m : Type -> Type ; class : class_of S m }.
Definition op_fresh S (M : t S) : m M S :=
  let: Pack _ (Class _ (Mixin x)) := M return m M S in x.
Arguments op_fresh {S M} : simpl never.
Definition baseType S (M : t S) := Monad.Pack (base (class M)).
Module Exports.
Notation Fresh := op_fresh.
Notation freshMonad := t.
Coercion baseType : freshMonad >-> monad.
Canonical baseType.
End Exports.
End MonadFresh.
Export MonadFresh.Exports.

Definition promotable A (p : pred (seq A)) (q : pred (seq A * seq A)) :=
  forall s t, p s -> p t -> p (s ++ t) = q (s, t).

Module segment_closed.
Record t A := mk {
  p : pred (seq A) ;
  H : forall a b, p (a ++ b) -> p a /\ p b }.
End segment_closed.
Definition segment_closed_p A := @segment_closed.p A.
Coercion segment_closed_p : segment_closed.t >-> pred.

Lemma segment_closed_suffix A (p : segment_closed.t A) s :
  ~~ p s -> forall t, ~~ p (s ++ t).
Proof. move=> ps t; apply: contra ps; by case/segment_closed.H. Qed.

Lemma segment_closed_prefix A (p : segment_closed.t A) s :
  ~~ p s -> forall t, ~~ p (t ++ s).
Proof. move=> ps t; apply: contra ps; by case/segment_closed.H. Qed.

(* assert p distributes over concatenation *)
Definition promote_assert (M : failMonad) A
  (p : pred (seq A)) (q : pred (seq A * seq A)) :=
  (bassert p) \o (fmap ucat) \o pair =
  (fmap ucat) \o (bassert q) \o pair \o (bassert p)`^2 :> (_ -> M _).

Lemma promote_assert_sufficient_condition (M : failMonad) A :
  Laws.right_zero (@Bind M) (@Fail _) ->
  forall (p : segment_closed.t A) q, promotable p q ->
  promote_assert M p q.
Proof.
move=> right_z p q promotable_pq.
rewrite /promote_assert.
rewrite [fmap]lock; apply functional_extensionality => -[x1 x2] /=; rewrite -lock.
rewrite {1}/bassert [in RHS]/fmap !bindA.
bind_ext => s.
rewrite 2!bindA bindretf 2!bindA.
rewrite {1}[in RHS]/guard.
case: ifPn => ps; last first.
  rewrite bindfailf.
  Inf (rewrite 2!bindretf).
  With (idtac) Open (X in _ >>= X).
    rewrite /assert /guard /= (negbTE (segment_closed_suffix ps x)) bindfailf.
    reflexivity.
  by rewrite right_z.
rewrite bindskipf; bind_ext => t.
rewrite 2![in LHS]bindretf.
rewrite bindA {1}[in RHS]/guard.
case: ifPn => pt; last first.
  by rewrite bindfailf /assert /guard /= (negbTE (segment_closed_prefix pt s)) bindfailf.
by rewrite bindskipf 2!bindretf bindA bindretf /assert promotable_pq.
Qed.

Section examples_promotable_segment_closed.

Lemma promotable_uniq_seq_disjoint A : promotable (@uniq A) seq_disjoint.
Proof.
move=> s t ps pt.
by rewrite cat_uniq ps pt /= andbT -nilp_intersect.
Qed.

Local Obligation Tactic := idtac.
Program Definition uniq_is_segment_closed (A : eqType) : segment_closed.t A :=
  @segment_closed.mk _ (@uniq A) _.
Next Obligation. by move=> A a b; rewrite cat_uniq => /and3P[]. Qed.

(* is a contiguous segment of the enumeration *)
(* TODO(rei): generalize to any enumeration *)
Definition is_iota : pred (seq nat) := [pred x | x == iota (head O x) (size x) ].

Lemma is_iota_head_last s : is_iota s -> 0 < size s -> head 0 s + size s = (last 0 s).+1.
elim: s => //= a [_ /=|c d IH].
  by rewrite addn1.
rewrite /is_iota /= => /eqP[] ?; subst c => Hd _.
rewrite /= in IH.
by rewrite -IH // -?addSnnS // /is_iota /= -Hd.
Qed.

(* predicate "are adjacent segments" *)
Definition are_adjacent : pred (seq nat * seq nat)%type :=
  [pred xy | [|| xy.1 == [::] , xy.2 == [::] | (last O xy.1).+1 == head O xy.2]].

Lemma promotable_enum : promotable is_iota are_adjacent.
Proof.
move=> s t Hs Ht.
rewrite /is_iota /= size_cat iota_add.
case/boolP : (nilp s) => [/nilP ->{Hs s} /=|s0]; first by rewrite addn0 /are_adjacent.
rewrite /nilp -lt0n in s0.
have -> : head 0 (s ++ t) = head 0 s by rewrite -nth0 nth_cat sub0n s0.
rewrite -(eqP Hs) /are_adjacent /= -size_eq0 -(negbK (size s == _)) -lt0n s0 /=.
rewrite eqseq_cat // eqxx /=.
case/boolP : (nilp t) => [/nilP {Ht} ->{t} //|t0].
rewrite /nilp -lt0n in t0.
rewrite -(size_eq0 t) -(negbK (size t == _)) -lt0n t0 /=.
case: t Ht t0 => // a b Hab _.
rewrite [head _ (_ :: _)]/=.
rewrite is_iota_head_last //= eqseq_cons eq_sym andb_idr // => /eqP Ha.
move: Hab.
by rewrite /is_iota /= => /eqP[] {1}->; rewrite -Ha.
Qed.

Program Definition is_iota_is_segment_closed : segment_closed.t nat :=
  @segment_closed.mk _ is_iota _.
Next Obligation.
move=> a b.
rewrite /is_iota /= /= size_cat => /eqP Hab.
apply/andP; rewrite -eqseq_cat ?size_iota //; apply/eqP.
case/boolP : (nilp a) => [/nilP a0|a0]; first by move: Hab; rewrite a0.
case/boolP : (nilp b) => [/nilP b0|b0].
  by move: Hab; rewrite b0 /= !cats0 addn0.
have -> : head 0 b = head 0 a + size a.
  move/(congr1 (fun x => nth 0 x (size a))) : Hab.
  rewrite nth_cat ltnn subnn nth0 => ->; rewrite -nth0 nth_cat lt0n.
  by rewrite a0 nth0 nth_iota // -{1}(addn0 (size a)) ltn_add2l lt0n.
suff <- : head 0 (a ++ b) = head 0 a by rewrite -iota_add.
by rewrite -nth0 nth_cat lt0n a0.
Qed.

End examples_promotable_segment_closed.

Module MonadFailFresh.
Record mixin_of S (M : failMonad) (fresh : M S) : Type := Mixin {
  symbols := fun n => sequence (nseq n fresh);
  (* generated symbols are indeed fresh (specification of fresh) *)
  distinct : segment_closed.t S ;
  _ : bassert distinct \o symbols = symbols ;
  (* failure is a right zero of composition (backtracking interpretation) *)
  _ : Laws.right_zero (@Bind M) (@Fail _)
}.
Record class_of S (m : Type -> Type) := Class {
  base : MonadFail.class_of m ;
  mixin : MonadFresh.mixin_of S m ;
  ext : @mixin_of S (MonadFail.Pack base) (MonadFresh.fresh mixin)
}.
Structure t S : Type := Pack { m : Type -> Type ; class : class_of S m }.
Definition op_symbols S (M : t S) :=
  let: Pack _ (Class _ _ (Mixin x _ _ _)) := M return nat -> m M (seq S) in x.
Arguments op_symbols {S M} : simpl never.
Definition op_distinct S (M : t S) :=
  let: Pack _ (Class _ _ (Mixin _ x _ _)) := M return segment_closed.t S in x.
Arguments op_distinct {S} M : simpl never.
Definition baseType S (M : t S) := MonadFail.Pack (base (class M)).
Module Exports.
Notation Symbols := op_symbols.
Notation distinct := op_distinct.
Notation failFreshMonad := t.
Coercion baseType : failFreshMonad >-> failMonad.
Canonical baseType.
Definition fresh_of_failfresh S (M : failFreshMonad S) : MonadFresh.t S :=
  @MonadFresh.Pack _ (MonadFailFresh.m M)
  (MonadFresh.Class (Monad.class (MonadFail.baseType (baseType M)))
                    (mixin (class M))).
Canonical fresh_of_failfresh.
End Exports.
End MonadFailFresh.
Export MonadFailFresh.Exports.

Section failfresh_lemmas.
Variables (S : eqType) (M : failFreshMonad S).
Lemma failfresh_bindmfail : Laws.right_zero (@Bind M) (@Fail _).
Proof. by case: M => m [? ? []]. Qed.
Lemma bassert_symbols : bassert (distinct M) \o Symbols = Symbols :> (nat -> M _).
Proof. by case: M => m [? ? []]. Qed.
End failfresh_lemmas.

Section properties_of_Symbols.
Variables (A : eqType) (M : failFreshMonad A).

Lemma SymbolsE : Symbols = (fun n => sequence (nseq n Fresh)) :> (_ -> M _).
Proof. by case: M => m [? ? [? ? ? ?]]. Qed.

Lemma Symbols0 : Symbols 0 = Ret [::] :> M _.
Proof. by rewrite SymbolsE. Qed.

Lemma SymbolsS n : Symbols n.+1 =
  do x <- Fresh ; do xs <- Symbols n : M _; Ret (x :: xs).
Proof. by rewrite SymbolsE. Qed.

Lemma Symbols_prop1 :
  Symbols \o const 1 = fmap wrap \o const Fresh :> (A -> M _).
Proof.
apply functional_extensionality => n.
transitivity (@Symbols _ M 1) => //.
rewrite SymbolsE sequence_cons sequence_nil.
by rewrite_ bindretf.
Qed.

Lemma Symbols_prop2 :
  Symbols \o uaddn = fmap ucat \o pair \o (Symbols : _ -> M _)`^2.
Proof.
apply functional_extensionality => -[n1 n2].
elim: n1 => /= [|n1 IH].
  rewrite add0n Symbols0 bindretf fmap_bind.
  Open (X in _ >>= X).
    rewrite fcomp_ext fmap_ret /=; reflexivity.
  by rewrite bindmret.
rewrite addSn SymbolsS {}IH SymbolsS.
rewrite [in RHS]fmap_bind bindA; bind_ext => a.
rewrite fmap_bind 2!bindA.
(* TODO(rei): use bind_ext *)
congr Monad.bind; apply functional_extensionality => s.
rewrite bindretf.
rewrite 2!fcomp_ext.
rewrite bind_fmap fmap_bind bindA.
rewrite_ bindretf.
rewrite_ fcomp_ext.
by rewrite_ fmap_ret.
Qed.

End properties_of_Symbols.

Section Tree.
Variable A : Type.

Inductive Tree := Tip (a : A) | Bin of Tree & Tree.

Fixpoint foldt B (f : A -> B) (g : B * B -> B) (t : Tree) : B :=
  match t with
  | Tip a => f a
  | Bin t u => g (foldt f g t, foldt f g u)
  end.

Section foldt_universal.
Variables B : Type.
Variables (h : Tree -> B) (f : A -> B) (g : B * B -> B).
Hypothesis H1 : h \o Tip = f.
Hypothesis H2 : h \o uncurry Bin = g \o (fun x => (h x.1, h x.2)).
Lemma foldt_universal : h = foldt f g.
Proof.
apply functional_extensionality; elim => [a|]; first by rewrite -H1.
move=> t1 IH1 t2 IH2 /=;
rewrite -IH1 -IH2.
transitivity ((h \o uncurry Bin) (t1, t2)); first by [].
by rewrite H2.
Qed.
End foldt_universal.

Definition size_Tree (t : Tree) := foldt (const 1) uaddn t.

Lemma size_Tree_Bin :
  size_Tree \o uncurry Bin = uncurry addn \o size_Tree`^2.
Proof. by apply functional_extensionality => -[x1 x2]. Qed.

Fixpoint labels (t : Tree) : seq A :=
  match t with
  | Tip a => [:: a]
  | Bin t u => labels t ++ labels u
  end.

End Tree.
Arguments Tip {A}.
Arguments Bin {A}.

Section tree_relabelling.

Variable Symbol : eqType. (* TODO: ideally, we would like a generic type here with a succ function *)
Variable M : failFreshMonad Symbol.
Variable q : pred (seq Symbol * seq Symbol).
Hypothesis promotable_q : promotable (distinct M) q.

Definition relabel : Tree Symbol -> M (Tree Symbol) :=
  foldt (fmap Tip \o const Fresh) (fmap (uncurry Bin) \o pair).

Let drTip {A} : A -> M _ :=
  fmap wrap \o const Fresh.
Let drBin {N : failMonad} : (N _ * N _ -> N _) :=
  fmap ucat \o bassert q \o pair.

(* extracting the distinct symbol list *)
Definition dlabels {N : failMonad} : Tree Symbol -> N (seq Symbol) :=
  foldt (Ret \o wrap) drBin.

Lemma dlabelsC t u (m : _ -> _ -> M (seq Symbol * seq Symbol)%type) :
  do x <- dlabels t; do x0 <- relabel u; m x0 x =
  do x0 <- relabel u; do x <- dlabels t; m x0 x.
Proof.
elim: t u m => [a u /= m|t1 H1 t2 H2 u m].
  rewrite /dlabels /= bindretf.
  bind_ext => u'.
  by rewrite bindretf.
rewrite (_ : dlabels _ = drBin (dlabels t1, dlabels t2)) //.
rewrite {2}/drBin.
rewrite {1}/fmap /=.
rewrite {1}/bassert /=.
rewrite ![in RHS]bindA.
transitivity (do x0 <- relabel u;
    (do x <- dlabels t1;
     do x <-
     (do x1 <- (do y <- dlabels t2; Ret (x, y)); (do x <- guard (q x1) >> Ret x1; (Ret \o ucat) x));
  m x0 x)); last first.
  bind_ext => u'.
  by rewrite !bindA.
rewrite -H1 {1}/drBin {1}/fmap /= {1}/bassert /= !bindA.
bind_ext => s.
rewrite !bindA.
transitivity (do x0 <- relabel u;
  (do x <- dlabels t2; (do x <-
    (do x1 <- Ret (s, x); (do x3 <- guard (q x1) >> Ret x1; Ret (ucat x3)));
    m x0 x))); last first.
  bind_ext => y2; by rewrite bindA.
rewrite -H2.
bind_ext => s'.
rewrite !bindretf.
rewrite !bindA.
transitivity (guard (q (s, s')) >>
  (do x1 <- (Ret \o ucat) (s, s'); do x3 <- relabel u; m x3 x1)).
  bind_ext => tt_unit; by rewrite bindretf.
rewrite guardsC; last exact: failfresh_bindmfail.
rewrite !bindA.
rewrite !bindretf.
rewrite !bindA.
bind_ext => u'.
rewrite bindA.
rewrite guardsC; last exact: failfresh_bindmfail.
by rewrite bindA bindretf.
Qed.

(* see gibbons2011icfp Sect. 9.3 *)
Lemma join_and_pairs :
  (join \o fmap pair \o pair) \o (fmap dlabels \o relabel)`^2 =
  (pair \o join`^2) \o           (fmap dlabels \o relabel)`^2 :> (_ -> M _).
Proof.
apply functional_extensionality => -[x1 x2].
rewrite /join /=. (* TODO *)
rewrite 5!bindA.
bind_ext => {x1}x1.
rewrite 2!bindretf.
rewrite 2!bindA.
do 3  rewrite_ bindretf.
rewrite -dlabelsC.
rewrite_ bindA.
by rewrite_ (@bind_fmap M).
Qed.

(* first property of Sect. 9.3 *)
Lemma dlabels_relabel_is_fold :
  dlabels >=> relabel = foldt drTip drBin.
Proof.
apply foldt_universal.
  (* dlabels >=> relabel \o Tip = drTip *)
  rewrite /kleisli -2!compA (_ : _ \o Tip = fmap Tip \o const Fresh) //.
  rewrite (compA (fmap dlabels)) -fmap_o (_ : dlabels \o _ = Ret \o wrap) //.
  by rewrite fmap_o 2!compA join_fmap_ret.
(* dlabels >=> relabel \o Bin = drBin \o _ *)
rewrite /kleisli -2![in LHS]compA.
rewrite (_ : _ \o _ Bin = fmap (uncurry Bin) \o (pair \o relabel`^2)); last first.
  by apply functional_extensionality; case.
rewrite (compA (fmap dlabels)) -fmap_o.
rewrite (_ : _ \o _ Bin = fmap ucat \o bassert q \o pair \o dlabels`^2); last first.
  by apply functional_extensionality; case.
transitivity (fmap ucat \o join \o fmap (bassert q \o pair) \o pair \o
    (fmap dlabels \o relabel)`^2).
  rewrite -2![in LHS](compA (fmap ucat)) [in LHS]fmap_o.
  rewrite -[in LHS](compA (fmap _)) [in LHS](compA _ (fmap _)).
  rewrite -join_naturality -2![in RHS]compA; congr (_ \o _).
  by rewrite fmap_o -[in LHS]compA naturality_pair.
rewrite fmap_o (compA _ (fmap (bassert q))) -(compA _ _ (fmap (bassert q))).
rewrite commutativity_of_assertions. (* first non-trivial step *)
rewrite (compA _ (bassert q)) -(compA _ _ (fmap pair)) -(compA _ _ pair) -(compA _ _ (_`^2)).
by rewrite join_and_pairs. (* second non-trivial step *)
Qed.

(* second property of Sect. 9.3 *)
Lemma symbols_size_is_fold :
  Symbols \o (@size_Tree Symbol) = foldt drTip drBin.
Proof.
apply foldt_universal.
  rewrite -compA.
  rewrite (_ : @size_Tree Symbol \o _ = const 1) //.
  by rewrite Symbols_prop1.
pose p := distinct M.
transitivity (bassert p \o Symbols \o @size_Tree Symbol \o uncurry Bin
  : (_ -> M _)).
  by rewrite bassert_symbols.
transitivity ((bassert p) \o Symbols \o uaddn \o (@size_Tree Symbol)`^2
  : (_ -> M _)).
  rewrite -[in LHS]compA -[in RHS]compA; congr (_ \o _).
  by rewrite size_Tree_Bin.
transitivity (bassert p \o fmap ucat \o pair \o (Symbols \o (@size_Tree Symbol))`^2
  : (_ -> M _)).
  rewrite -2!compA (compA Symbols) Symbols_prop2.
  by rewrite -(compA (_ \o pair)) (compA (bassert p)).
transitivity (fmap ucat \o (bassert q) \o pair \o (bassert p \o Symbols \o (@size_Tree Symbol))`^2
  : (_ -> M _)).
  (* assert p distributes over concatenation *)
  by rewrite (@promote_assert_sufficient_condition _ _ (@failfresh_bindmfail _ M) p q).
transitivity (fmap ucat \o bassert q \o pair \o (Symbols \o (@size_Tree Symbol))`^2
  : (_ -> M _)).
  by rewrite bassert_symbols.
by [].
Qed.

(* main claim *)
Lemma dlabels_relabel_never_fails :
  dlabels >=> relabel = Symbols \o @size_Tree Symbol.
Proof. by rewrite dlabels_relabel_is_fold symbols_size_is_fold. Qed.

End tree_relabelling.

Section mu2017.

(* TODO: move *)
Definition zipWith {A B C} (op : A -> B -> C) a b : seq C :=
  map (fun xy => op xy.1 xy.2) (zip a b).

Section queens_definition.

Local Open Scope mu_scope.

Definition ups s i := zipWith Zplus (map Z_of_nat (iota i (size s))) s.
Definition downs s i := zipWith Zminus (map Z_of_nat (iota i (size s))) s.
Definition safe s := uniq (ups s 0) && uniq (downs s 0).

Definition queens_example := [:: 3; 5; 7; 1; 6; 0; 2; 4]%Z.
Eval compute in safe queens_example.

Definition mu_queens {M : nondetMonad} n : M (seq Z) :=
  perms (map Z_of_nat (iota 0 n)) >>= assert safe.

Definition safeAcc i (us ds : seq Z) (xs : seq Z) :=
  let us' := ups xs i in let ds' := downs xs i in
  uniq us' && uniq ds' && all (fun x => x \notin us) us' && all (fun x => x \notin ds) ds'.

Lemma safeE : safe =1 safeAcc 0 [::] [::].
Proof.
move=> s; rewrite /safe /safeAcc.
by rewrite (sub_all _ (@all_predT _ _)) // (sub_all _ (@all_predT _ _)) // !andbT.
Qed.

Definition queens_ok (i_xus_yds : Z * seq Z * seq Z) :=
  let: (_, xus, yds) := i_xus_yds in
  match xus, yds with
  | x :: us, y :: ds => (x \notin us) && (y \notin ds)
  | _, _ => false
  end.

Definition queens_next i_us_ds x :=
  let: (i, us, ds) := i_us_ds in (i + 1, (i + x) :: us, (i - x) :: ds)%Z.

Definition safeAcc_scanl i (us ds : seq Z) :=
  let ok i_xus_yds := queens_ok i_xus_yds in
  let op i_us_ds x := queens_next i_us_ds x in
  all ok \o scanl op (i, us, ds).

Lemma safeAccE i a b : safeAcc i a b =1 safeAcc_scanl (Z_of_nat i) a b.
Proof.
move=> s; elim: s i a b => // h t IH i a b.
rewrite /safeAcc_scanl /=.
move: (IH i.+1 ((Z.of_nat i + h) :: a) ((Z.of_nat i - h) :: b))%Z.
rewrite (_ : Z.of_nat i.+1 = (Z.of_nat i) + 1)%Z; last by rewrite -addn1 Nat2Z.inj_add.
rewrite /safeAcc_scanl => /= <-.
rewrite /safeAcc /= !andbA /zipWith /=.
set A := uniq _. set B := uniq _. set sa := map _ _. set sb := map _ _.
rewrite -![in LHS]andbA [in LHS]andbC.
do 2 rewrite -![in RHS]andbA [in RHS]andbC.
rewrite -!andbA; congr andb.
rewrite -[in LHS]andbC -!andbA; congr andb.
do 2 rewrite ![in RHS]andbA [in RHS]andbC.
congr andb.
rewrite [in LHS]andbCA -![in RHS]andbA; congr andb.
have H : forall (op : Z -> Z -> Z) y s, all (fun x : Z => x \notin op (Z_of_nat i) h :: y) s =
  all (fun x : Z => x \notin y) s && (op (Z_of_nat i) h \notin s).
  move=> op y; elim => //= s1 s2 ih /=; rewrite ih !inE !negb_or.
  rewrite -andbA andbCA !andbA; congr (_ && _); rewrite -!andbA; congr(_ && _).
  by rewrite andbC eq_sym.
by rewrite andbA andbCA -!andbA andbCA !andbA -H -andbA -H.
Qed.

Lemma mu_queensE {M : nondetMonad} n : mu_queens n =
  perms (map Z_of_nat (iota 0 n)) >>= assert (safeAcc_scanl 0 [::] [::]) :> M _.
Proof.
rewrite /mu_queens; bind_ext => s; by rewrite /assert (safeE s) safeAccE.
Qed.

End queens_definition.

(* from section 4.2 ("safety check as a stateful foldr") *)
Section loop.

Variables (A S : Type) (M : stateMonad S) (op : S -> A -> S).

Local Open Scope mu_scope.

Definition opmul x m : M _ :=
  Get >>= fun st => let st' := op st x in cons st' ($) (Put st' >> m).

Definition loopp (s : S) (xs : seq A) : M (seq S) :=
  let mul x m := opmul x m in Put s >> foldr mul (Ret [::]) xs.

Lemma loopp_nil (s : S) : loopp s [::] = Put s >> Ret [::].
Proof. by []. Qed.

Lemma loopp_of_scanl_helper (s : S) (ms : M S) (mu mu' : M unit) (m : M (seq S)) (f : S -> M unit) :
  do x <- ms; mu >> (do xs <- cons s ($) (mu' >> m); f x >> Ret xs) =
  cons s ($) (do x <- ms; mu >> mu' >> (do xs <- m; f x >> Ret xs)).
Proof.
rewrite /fmap !bindA.
rewrite_ bindA.
bind_ext => x.
rewrite !bindA; bind_ext; case.
bind_ext; case.
rewrite_ bindretf.
rewrite_ bindA.
With (rewrite_ bindretf) Open (X in _ = _ >>= X).
  reflexivity.
by [].
Qed.

(* theorem 4.1 *)
Lemma loopp_of_scanl (s : S) (xs : seq A) :
  Ret (scanl op s xs) = do ini <- Get; loopp s xs >>= overwrite ini.
Proof.
elim: xs s => [/=|x xs IH] s.
  rewrite loopp_nil.
  rewrite_ bindA.
  rewrite_ bindretf.
  rewrite /overwrite.
  Inf rewrite -bindA.
  rewrite_ putput.
  by rewrite -bindA getputskip bindskipf.
rewrite /loopp /overwrite [in RHS]/=.
set mul := fun (a : A) m => _.
Inf rewrite !bindA.
(* TODO(rei): tactic for nested function bodies? *)
transitivity (do y <- Get; (Put s >> Get) >>= fun z =>
  do a <- cons (op z x) ($) (Put (op z x) >> foldr mul (Ret [::]) xs);
  Put y >> Ret a); last by Inf rewrite !bindA.
rewrite_ putget.
rewrite_ bindA.
rewrite_ bindretf.
rewrite loopp_of_scanl_helper.
transitivity (cons (op s x) ($) do y <- Get; Put (op s x) >>
  (do a <- foldr mul (Ret [::]) xs; Put y >> Ret a)); last first.
  congr (_ ($) _); by rewrite_ putput.
transitivity (cons (op s x) ($)
  (do y <- Get; loopp (op s x) xs >>= overwrite y)); last first.
  congr (_ ($) _); by Inf rewrite -bindA.
by rewrite -IH fmap_ret.
Qed.

End loop.

Section section_51.

Variables (S : Type) (M : nondetStateMonad S).
Variables (A : Type) (op : S -> A -> S) (ok : pred S).

Lemma assert_all_scanl (st : S) (xs : seq A) :
  assert (all ok \o scanl op st) xs =
  Get >>= (fun ini => loopp _ op st xs >>=
    (fun ys => guard (all ok ys) >> Ret xs >>= overwrite ini)) :> M _.
Proof.
rewrite /assert.
rewrite guardsC; last exact: bindmfail.
transitivity (Get >>= (fun ini => loopp _ op st xs >>= overwrite ini >>=
    (fun ys => guard (all ok ys) >> Ret xs) : M _)).
  by rewrite -!bindA -loopp_of_scanl bindA !bindretf.
bind_ext => st'.
rewrite bindA; bind_ext => xs'.
rewrite /overwrite !bindA guardsC; last exact: bindmfail.
rewrite !bindA !bindretf.
(* TODO: lemma? relation with guardsC? *)
rewrite bindA; bind_ext; case; by rewrite bindretf.
Qed.

Local Open Scope mu_scope.

Lemma put_foldr st x xs :
  Put (op st x) >>
  (do x1 <- foldr (opmul op) (Ret [::]) xs; guard (all ok x1) >> guard (ok (op st x))) =
  guard (ok (op st x)) >>
  (Put (op st x) >> (do ys <- foldr (opmul op) (Ret [::]) xs; guard (all ok ys))) :> M _.
Proof.
elim: xs x => [x|h t _ x].
  rewrite /=.
  rewrite bindretf /=.
  rewrite bindskipf /= .
  rewrite (_ : do ys <- Ret [::]; guard (all ok ys) = skip); last first.
    by rewrite bindretf.
  rewrite bindmskip.
  rewrite /guard.
  case: ifPn => H.
    by rewrite bindskipf bindmskip.
  by rewrite bindmfail bindfailf.
rewrite /= !bindA.
transitivity (Put (op st x) >>
  (do x0 <- Get;
   do x1 <- let st' := op x0 h in cons st' ($) (Put st' >> foldr (opmul op) (Ret [::]) t);
   guard (ok (op st x)) >> guard (all ok x1)) : M _).
  bind_ext; case.
  bind_ext => st'.
  bind_ext => s.
  by rewrite -guard_and andbC guard_and.
rewrite guardsC; last exact: bindmfail.
rewrite !bindA.
bind_ext; case.
bind_ext => st'.
rewrite !bindA.
bind_ext; case.
bind_ext => s /=.
bind_ext => s'.
rewrite guardsC //.
exact: bindmfail.
Qed.

Let B := A.
Let res := @cons A.

Definition opdot (x : A) (m : M (seq B)) : M (seq B) :=
  Get >>= (fun st => guard (ok (op st x)) >> Put (op st x) >> (res x ($) m)).

Lemma theorem_53 (xs : seq A) :
  foldr (opmul op) (Ret [::]) xs >>=
    (fun ys => guard (all ok ys) >> Ret xs) = foldr opdot (Ret [::]) xs.
Proof.
elim: xs => [|x xs IH]; first by rewrite /= bindretf /= bindskipf.
rewrite [in LHS]/=.
rewrite {1}/opmul.
rewrite {1}bindA.
transitivity (do x0 <- Get;
  Put (op x0 x) >> foldr (opmul op) (Ret [::]) xs >>= (fun ys =>
  guard (all ok (op x0 x :: ys))) >> Ret (x :: xs) : M _).
  bind_ext => st.
  by rewrite bind_fmap !bindA.
transitivity (do x0 <- Get;
  Put (op x0 x) >> foldr (opmul op) (Ret [::]) xs >>= (fun ys =>
  guard (all ok ys) >> guard (ok (op x0 x))) >> Ret (x :: xs) : M _).
  bind_ext => st.
  rewrite !bindA.
  bind_ext; case.
  bind_ext => ys.
  rewrite -guard_and.
  congr (guard _ >> _).
  by rewrite -cat1s all_cat andbC all_seq1.
transitivity (do st <- Get; guard (ok (op st x)) >>
  Put (op st x) >> foldr (opmul op) (Ret [::]) xs >>= (fun ys =>
   guard (all ok ys)) >> Ret (x :: xs) : M _).
  bind_ext => st.
  rewrite -!bindA.
  congr (_ >> _).
  rewrite !bindA.
  by rewrite put_foldr.
transitivity (do st <- Get; guard (ok (op st x)) >>
  Put (op st x) >>
    (cons x) ($) (foldr (opmul op) (Ret [::]) xs >>= (fun ys =>
   guard (all ok ys)) >> Ret xs) : M _).
  bind_ext => st.
  rewrite !bindA.
  bind_ext; case.
  bind_ext; case.
  rewrite !fmap_bind.
  bind_ext => s.
  rewrite fcomp_ext fmap_bind /=.
  bind_ext; case.
  by rewrite fcomp_ext fmap_ret.
by rewrite /= -IH /opdot !bindA.
Qed.

End section_51.

Section section_52.

Variable M : nondetStateMonad (Z * seq Z * seq Z).

Definition opdot_queens : Z -> M (seq Z) -> M (seq Z) := opdot queens_next queens_ok.

Local Open Scope mu_scope.

Definition queensBody (xs : seq Z) : M (seq Z) :=
  perms xs >>= foldr opdot_queens (Ret [::]).

Lemma mu_queens_state_nondeter n : mu_queens n = Get >>=
  (fun ini => Put (0, [::], [::])%Z >> queensBody (map Z_of_nat (iota 0 n)) >>= overwrite ini).
Proof.
rewrite mu_queensE.
transitivity (perms (map Z.of_nat (iota 0 n)) >>= (fun xs => Get >>=
  (fun ini => Put (0, [::], [::])%Z >> foldr opdot_queens (Ret [::]) xs >>= overwrite ini))).
  bind_ext => s /=.
  rewrite assert_all_scanl. (* NB: uses theorem 4.1 *)
  bind_ext => st.
  rewrite 2!bindA.
  bind_ext; case.
  by rewrite -theorem_53 bindA.
transitivity (Get >>= (fun ini => Put (0, [::], [::])%Z >>
  perms (map Z.of_nat (iota 0 n)) >>= (fun xs => (foldr opdot_queens (Ret [::]) xs >>= overwrite ini)))).
  rewrite -getpermsC.
  bind_ext => s.
  rewrite !bindA putpermsC.
  by rewrite_ bindA.
bind_ext => st.
by rewrite !bindA.
Qed.

End section_52.

Definition seed_select {M : nondetStateMonad (Z * seq Z * seq Z)%type} :=
  fun (p : pred (seq Z)) (f : seq Z -> M (Z * seq Z)%type)
  (a b : seq Z) => size a < size b.

(* direct proof of theorem 4.2 *)
Section theorem_42.
Variables (M : nondetStateMonad (Z * seq Z * seq Z)%type).

Local Open Scope mu_scope.

Notation unfoldM := (unfoldM (@well_founded_size _)).

Let op := @opdot_queens M.
Let p := @nilp Z.

Lemma base_case y : p y -> (foldr op (Ret [::]) >=> unfoldM p select) y = Ret [::].
Proof.
move=> py.
transitivity (foldr op (Ret [::]) =<< Ret [::]).
  rewrite /kleisli /rbind bindretf /= join_fmap unfoldME; last exact: decr_size_select.
  by rewrite py bindretf.
by rewrite /rbind bindretf.
Qed.

Lemma theorem_42 :
  (foldr op (Ret [::]) >=> unfoldM p select) =1
  @hyloM _ _ _ _ op [::] p select seed_select (@well_founded_size _).
Proof.
apply: (well_founded_induction (@well_founded_size _)) => y IH.
rewrite hyloME; last exact: decr_size_select.
case/boolP : (p y) => py.
  by rewrite base_case.
rewrite /rkleisli /kleisli /= join_fmap.
rewrite unfoldME; last exact: decr_size_select.
rewrite (negbTE py) bindA.
rewrite(@decr_size_select _ _) /bassert !bindA; bind_ext => -[b a] /=.
rewrite /assert /guard /=.
case: ifPn => ay; last by rewrite !bindfailf.
rewrite bindskipf !bindretf /= -IH // bind_fmap /kleisli /= join_fmap.
suff : do x <- unfoldM p select a; op b (foldr op (Ret [::]) x) =
  op b (do x <- unfoldM p select a; foldr op (Ret [::]) x) by done.
rewrite {ay}.
move: a b.
apply: (well_founded_induction (@well_founded_size _)) => a IH' b.
destruct a as [|u v] => //.
  rewrite unfoldME /=; last exact: decr_size_select.
  by rewrite !bindretf /=.
rewrite unfoldME /=; last exact: decr_size_select.
rewrite !bindA.
transitivity (do x <- Ret (u, v) [~i] (do y_ys <- select v; Ret (y_ys.1, u :: y_ys.2));
  op b (do x0 <- cons x.1 ($) unfoldM p select x.2; foldr op (Ret [::]) x0)); last first.
  apply/esym.
  rewrite {1}/op /opdot_queens /opdot fmap_bind.
  transitivity (do st <- Get;
  (guard (queens_ok (queens_next st b)) >> do x <- Ret (u, v) [~i] (do y_ys <- select v; Ret (y_ys.1, u :: y_ys.2));
   (Put (queens_next st b)) >>
  ((cons b
    (o) (fun x : Z * seq Z => do x0 <- cons x.1 ($) unfoldM p select x.2; foldr op (Ret [::]) x0)) x))).
    bind_ext => st.
    rewrite !bindA.
    bind_ext; case.
    rewrite -commute_nondetState //.
    case: (@select_is_nondetState _ M _ v) => x <-.
    by exists (ndAlt (ndRet (u, v)) (ndBind x (fun y => ndRet (y.1, u :: y.2)))).
  transitivity (do st <- Get;
  (do x <- Ret (u, v) [~i] (do y_ys <- select v; Ret (y_ys.1, u :: y_ys.2)) : M _;
  guard (queens_ok (queens_next st b)) >>
   Put (queens_next st b) >>
   (cons b
    (o) (fun x0 : Z * seq Z => do x1 <- cons x0.1 ($) unfoldM p select x0.2; foldr op (Ret [::]) x1))
     x)).
    bind_ext => st.
    rewrite -bindA guardsC; last exact: bindmfail.
    rewrite !bindA.
    bind_ext => x.
    rewrite !bindA.
    bind_ext; case.
    by rewrite bindretf.
  rewrite -commute_nondetState //.
  case: (@select_is_nondetState _ M _ v) => x <-.
  by exists (ndAlt (ndRet (u, v)) (ndBind x (fun y => ndRet (y.1, u :: y.2)))).
bind_ext => x.
rewrite {1}/op /opdot_queens /opdot.
rewrite commute_nondetState; last first.
  rewrite /fmap.
  case: (unfoldM_is_nondetState (@select_is_nondetState _ M Z) (@decr_size_select M _) x.2).
  move=> m <-.
  by exists (ndBind m (fun y => ndRet (x.1 :: y))).
rewrite {2}/op /opdot_queens /opdot.
bind_ext => st.
rewrite commute_nondetState //; last first.
   case: (unfoldM_is_nondetState (@select_is_nondetState _ M Z) (@decr_size_select _ _) x.2).
   move=> m <-.
   by exists (ndBind m (fun y => ndRet (x.1 :: y))).
bind_ext; case.
rewrite !bind_fmap !fmap_bind.
by bind_ext.
Qed.

End theorem_42.

Section section_52_contd.

Variables (M : nondetStateMonad (Z * seq Z * seq Z)%type).

Local Open Scope mu_scope.

Lemma queensBodyE : queensBody M =
  hyloM (@opdot_queens M) [::] (@nilp _) select seed_select (@well_founded_size _).
Proof.
rewrite /queensBody; apply functional_extensionality.
case => [|h t].
  rewrite /= permsE /= hyloME; last 2 first.
    by rewrite bindretf.
    exact: decr_size_select.
rewrite [h :: t]lock -theorem_42.
by rewrite /kleisli /= join_fmap perms_mu_perm.
Qed.

Lemma queensBodyE' xs : queensBody M xs = if xs is [::] then Ret [::] else
  select xs >>= (fun xys =>
  Get >>= (fun st => guard (queens_ok (queens_next st xys.1)) >>
  Put (queens_next st xys.1) >> (cons xys.1 ($) queensBody M xys.2))).
Proof.
case: xs => [|h t].
  rewrite queensBodyE // hyloME //; exact: decr_size_select.
rewrite {1}queensBodyE hyloME; last exact: decr_size_select.
rewrite {-1}[h :: t]lock /= decr_size_select /bassert 2!bindA.
bind_ext => -[x ys] /=.
rewrite /assert /guard /=.
case: ifPn => ysht; last by rewrite !bindfailf.
rewrite bindskipf !bindretf /opdot_queens /opdot.
bind_ext => st.
rewrite !bindA; bind_ext; case.
bind_ext; case => /=.
by rewrite queensBodyE.
Qed.

End section_52_contd.

End mu2017.
