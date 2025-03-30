From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
From HB Require Import structures.
From Paco Require Import paco.
Require Import hierarchy monad_lib Morphisms.
Import Setoid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Module DelayMonad.
Section delaymonad.

CoInductive Delay (A : UU0) : Type := DNow : A -> Delay A | DLater : Delay A -> Delay A.
Local Notation M := Delay.
Let ret : idfun ~~> M := @DNow.
Let bind := fun A B (m : M A) (f: A -> M B) =>
              (cofix bind_ u := match u with
                                | DNow x => f x
                                | DLater m' => DLater (bind_ m')
                                end) m.
Lemma DelayE (A : UU0) (m : M A) :
  m = match m with
      | DNow x => DNow x
      | DLater m' => DLater m'
      end.
Proof. by case: m. Qed.
Lemma left_neutral : BindLaws.left_neutral bind ret.
Proof. by move=> A B a f; rewrite [LHS]DelayE [RHS]DelayE. Qed.
Inductive strongBisim_gen (A : UU0) (sB : _ -> _ -> Prop) : M A -> M A -> Prop :=
| sBRefl (m : M A) : strongBisim_gen sB m m
| sBLater (m m' : M A) :
  sB m m' -> strongBisim_gen sB (DLater m) (DLater m').
Arguments strongBisim_gen [A].
Definition strongBisim (A : UU0) d1 d2 := paco2 (@strongBisim_gen A) bot2 d1 d2.
Hint Unfold strongBisim.
Lemma strongBisim_gen_mon A : monotone2 (@strongBisim_gen A).
Proof.
move => d1 d2 r1 r2 Hr1 Hr12.
case: Hr1 => [m|m1 m2].
  exact: sBRefl.
move/Hr12 => Hr2.
exact: (sBLater Hr2).
Qed.
Arguments strongBisim [A].
Arguments sBLater [A].

#[deprecated(since = "0.7.3", note = "non standard axiom for strong bisimilarity")]
Axiom strongBisim_eq : forall A (m m' : M A), strongBisim m m' -> m = m'.

Theorem right_neutral_bisim A : forall (m : M A), strongBisim (bind m (@ret A)) m.
pcofix CIH => m.
pfold.
case: m=> [a|m].
  rewrite (DelayE (bind _ _)) /=.
  exact: sBRefl.
rewrite (DelayE (bind _ _)) /=.
apply: sBLater.
right.
exact: (CIH m).
Qed.
Lemma right_neutral : BindLaws.right_neutral bind ret.
Proof. by move=> *; exact/strongBisim_eq/right_neutral_bisim. Qed.
Lemma associative_bisim A B C : forall (m : M A) (f : A -> M B) (g : B -> M C),
  strongBisim (bind (bind m f) g) (bind m (fun x => bind (f x) g)).
Proof.
pcofix CIH => m.
pfold.
case: m=> [a|m] f g.
  rewrite (DelayE (bind (DNow a) (fun x => bind _ _))).
  rewrite (DelayE (bind _ g)) /=.
  apply: sBRefl.
rewrite (DelayE (bind (DLater m) _)).
rewrite (DelayE (bind (DLater m) (fun x => bind _ _))) /=.
rewrite (DelayE (bind (DLater _) g))/=.
apply: sBLater.
right.
apply: CIH.
Qed.
Lemma associative : BindLaws.associative bind.
Proof. move=> *; exact/strongBisim_eq/associative_bisim. Qed.
HB.instance Definition _ := isMonad_ret_bind.Build
                              Delay left_neutral right_neutral associative.
End delaymonad.
End DelayMonad.
HB.export DelayMonad.

Module DelayOps.
Section delayops.
Import boolp.
Local Notation M := Delay.
Fixpoint steps A n (x : M A) : M A :=
  if n is m.+1 then
    match x with
    | DNow a => DNow a
    | DLater da => steps m da
    end
  else x.
Lemma stepsD A n m (x : M A) : steps (m + n) x = steps n (steps m x).
Proof.
elim: m x => //= m IH [a|x].
  by elim: n {IH}.
by apply: IH.
Qed.
Lemma steps_Dnow A n (a : A) : steps n (DNow a) = DNow a.
Proof. by elim: n => //=. Qed.
Lemma monotonicity_steps' A n (a : A) : forall (x : M A), steps n (DLater x) = DNow a -> steps n x = DNow a.
Proof.
elim: n => //= n IH [a'|x'] Ha.
  by rewrite -(steps_Dnow n a').
by apply: (IH x').
Qed.
Lemma monotonicity_steps A (x : M A) (a : A) (n : nat) :  steps n x = DNow a -> forall m, n <= m -> steps m x = DNow a.
Proof.
move => Hn m.
elim: m => //= [|m IH].
  rewrite leqn0.
  move => /eqP Hnm.
  by rewrite -Hn Hnm.
case: x Hn IH => [a'|x'] Ha' IH.
  by rewrite -Ha' -{1}(steps_Dnow n a').
rewrite leq_eqVlt => /orP [/eqP H| H].
  by rewrite -Ha' H.
apply: monotonicity_steps'.
by apply: IH.
Qed.
CoFixpoint spin A : M A  := DLater (spin A).
Lemma spinE A : DLater (@spin A) = (@spin A).
Proof. by rewrite {2}(DelayE (@spin A))/=. Qed.
Inductive Terminates A : M A -> A -> Prop :=
  | TDNow a : Terminates (DNow a) a
  | TDLater d a : Terminates d a -> Terminates (DLater d) a.
Lemma Terminates_steps A (d : M A) (a : A) : Terminates d a <-> (exists n, steps n d = DNow a).
Proof.
split => [Ht|Hda].
  elim: Ht => [a'|d' a' IH1 IH2] /=.
    by exists 0.
  case: IH2 => x IH2.
  by exists x.+1.
inversion Hda.
move: d Hda H.
elim: x => [d Hda /= Hs|n IH d' Hs Hd].
  rewrite Hs.
  by apply (TDNow a).
case:d' Hs Hd => [a'|d'] Hs.
  rewrite steps_Dnow => Haa'.
  rewrite Haa'.
  by apply: (TDNow a).
move => /= Hd.
apply: TDLater.
inversion Hs.
apply IH => //.
case: x H => [|m] H //.
exists m.
by rewrite -H.
Qed.
Lemma Terminates_func A (d : M A) (a b : A) : Terminates d a -> Terminates d b -> a = b.
Proof.
case/Terminates_steps => n Ha.
case/Terminates_steps => m Hb.
wlog:n m a b Ha Hb/ n <= m.
  case/orP: (leqVgt n m) => nm H.
    by apply: (H _ _ _ _ Ha Hb).
  symmetry.
  apply: (H _ _ _ _ Hb Ha).
  exact:ltnW.
move => nm.
rewrite (monotonicity_steps Ha nm) in Hb .
by case: Hb.
Qed.
Definition Diverges A (d : M A) : Prop := ~ (exists a, Terminates d a).
Lemma TerminatesP A (d : M A) : decidable (exists a, Terminates d a).
Proof.
case/boolP: `[< exists a, Terminates d a >].
  move/asboolP; by left.
move/asboolP; by right.
Qed.
Lemma iff_not_Diverges_Terminates A (d : M A) : ~ Diverges d <-> (exists a, Terminates d a).
Proof. by split => [| ? ? //]; rewrite notE. Qed.
Lemma Diverges_spinP A (d : M A) : Diverges d <-> d = @spin A.
Proof.
split.
  case: (TerminatesP d) => //= HD _.
  apply strongBisim_eq.
  move: d HD.
  pcofix CIH => d HD.
  case: d HD => [a|d'] HD.
    contradict HD.
    exists a.
    by apply TDNow.
  rewrite -spinE.
  pfold.
  apply: sBLater.
  right.
  apply: CIH.
  move => [a Hd'].
  apply HD.
  exists a.
  by apply (TDLater Hd').
move => HD.
rewrite/Diverges HD/not;clear.
move => [a /Terminates_steps [n Hs]].
contradict Hs.
elim: n => //=.
by rewrite -spinE.
Qed.
Inductive wBisim_gen (A : UU0) (wBisim : _ -> _ -> Prop) : M A -> M A -> Prop :=
  | wBTerminate d1 d2 a : Terminates d1 a -> Terminates d2 a -> wBisim_gen wBisim d1 d2
  | wBLater d1 d2 : wBisim d1 d2 -> wBisim_gen wBisim (DLater d1) (DLater d2).
Lemma wBisim_gen_mon A : monotone2 (@wBisim_gen A).
Proof.
move => d1 d2 r1 r2 H Hr12.
case: d1 H => [a1|d1].
  case: d2 => [a2|d2] H; inversion H; apply: (wBTerminate _ H0 H1).
case: d2 => [a2|d2] H.
  inversion H.
  apply: (wBTerminate _ H0 H1).
inversion H.
  apply: (wBTerminate _ H0 H1).
apply: wBLater.
exact: (Hr12 _ _ H2).
Qed.
Hint Resolve wBisim_gen_mon : paco.
Definition wBisim A d1 d2 := paco2 (@wBisim_gen A) bot2 d1 d2.
Notation "a '≈' b" := (wBisim a b).
Lemma wBisim_refl A : forall (d : M A), d ≈ d.
Proof.
pcofix CIH => d.
pfold.
case: d => [a|d].
by apply: wBTerminate; apply: TDNow.
apply: wBLater.
by right.
Qed.
Lemma wBisim_sym A : forall (d1 d2 : M A), d1 ≈ d2 -> d2 ≈ d1.
Proof.
pcofix CIH.
move => d1 d2 H12.
pfold.
case: d1 H12 => [a1|d1].
  case: d2 => [a2|d2] H12; pinversion H12; exact: (wBTerminate _ H0 H).
case: d2 => [a2|d2] H12.
  pinversion H12.
  exact: (wBTerminate _ H0 H).
pinversion H12.
  exact: (wBTerminate _ H0 H).
apply: wBLater.
right.
exact: CIH.
Qed.
Lemma Terminates_wBisim A (d1 d2 : M A) (a : A) : Terminates d1 a -> d1 ≈ d2 -> Terminates d2 a.
Proof.
move => Ha.
elim: Ha d2 => [a' d2 Ho|d a' Ha IH d2 Ho].
  pinversion Ho.
  inversion H.
  by subst.
pinversion Ho.
  inversion H.
  subst.
  by rewrite (Terminates_func Ha H4).
apply: TDLater.
by apply IH.
Qed.
Lemma Diverges_wBisim A (d1 d2 : M A) : Diverges d1 -> d1 ≈ d2 -> Diverges d2.
Proof.
move => Hd1 /wBisim_sym Ho [a Ht].
apply: Hd1.
exists a.
exact: (Terminates_wBisim Ht Ho).
Qed.
Lemma  wBisim_trans A :forall (d1 d2 d3 : M A), d1 ≈ d2 -> d2 ≈ d3 -> d1 ≈ d3.
Proof.
pcofix CIH => d1 d2 d3.
pfold.
case: d1 => [a|d1].
  move => Ht1 Ht2.
  apply: (wBTerminate _ (TDNow a)).
  apply: (Terminates_wBisim _ Ht2).
  apply: (Terminates_wBisim _ Ht1).
  exact: TDNow.
case: d2 => [a|d2] Hd1 Hd2.
  pinversion Hd2.
  inversion H; subst.
  have Hda: Terminates (DLater d1) a0.
    apply wBisim_sym in Hd1.
    exact: (Terminates_wBisim (TDNow a0) Hd1).
  exact: (wBTerminate _ Hda H0).
case: d3 Hd2 => [a|d3] Hd2.
  pinversion Hd2.
  inversion H0; subst.
  subst.
  have Hda: Terminates (DLater d1) a0.
    apply wBisim_sym in Hd1.
    exact: (Terminates_wBisim H Hd1).
  exact: (wBTerminate _ Hda).
apply: wBLater.
right.
apply (CIH d1 d2 d3).
  pinversion Hd1; subst.
    inversion H;subst.
    inversion H0; subst.
    pfold.
    exact: (wBTerminate _ H2 H3).
  exact: H1.
pinversion Hd2; subst.
  inversion H;subst.
  inversion H0; subst.
  pfold.
  exact: (wBTerminate _ H2 H3).
exact: H1.
Qed.
Add Parametric Relation A : (M A) (@wBisim A)
  reflexivity proved by (@wBisim_refl A)
  symmetry proved by (@wBisim_sym A)
  transitivity proved by (@wBisim_trans A)
  as wBisim_rel.
Hint Extern 0 (wBisim _ _) => setoid_reflexivity.
Lemma wBisim_DLater A : forall (d : M A), DLater d ≈ d.
Proof.
pcofix CIH => d.
case: d => [a|d'].
  pfold.
  apply: wBTerminate.
    by apply/TDLater/TDNow.
  exact: TDNow.
pfold.
apply: wBLater.
right.
apply: CIH.
Qed.
Lemma wBisim_steps A (d : M A) (n : nat) : steps n d ≈ d .
Proof.
elim: n d => [|n IH] d //.
case: d IH => //.
move => d IH //=.
by rewrite IH wBisim_DLater.
Qed.

Definition wBisims (A : UU0) (d1 d2 : M A) : Prop :=
  exists n, steps n d1 = steps n d2.
Lemma wBisims_refl A (a : M A) : wBisims a a.
Proof. rewrite/wBisims. by exists 0. Qed.
Lemma wBisims_sym A (d1 d2 : M A) : wBisims d1 d2 -> wBisims d2 d1.
Proof. move => [n Hs]. by exists n. Qed.
Lemma wBisims_trans A (d1 d2 d3 : M A): wBisims d1 d2 -> wBisims d2 d3 -> wBisims d1 d3.
Proof.
move => [n Hs1] [m Hs2].
exists (n + m).
by rewrite stepsD Hs1 addnC stepsD -Hs2 -stepsD -stepsD addnC.
Qed.
Add Parametric Relation A : (M A) (@wBisims A)
  reflexivity proved by (@wBisims_refl A)
  symmetry proved by (@wBisims_sym A)
  transitivity proved by (@wBisims_trans A)
  as wBisims_rel.
Notation "a '≈s' b" := (wBisims a b) (at level 70).
Hint Extern 0 (wBisims _ _) => setoid_reflexivity.
Lemma terminatesP A (a : M A) : decidable (exists c, exists m, steps m a = DNow c ).
Proof.
case/boolP: `[< exists c, exists m, steps m a = DNow c >].
  move/asboolP; by left.
move/asboolP; by right.
Qed.
Lemma wBisims_DLater A (d : M A) : (DLater d) ≈s d.
Proof.
case: (TerminatesP d).
  move => [a /Terminates_steps [n Hs]].
  exists (n.+1).
  by rewrite (monotonicity_steps Hs (leqnSn n)).
move => /Diverges_spinP Hs.
by rewrite! Hs spinE.
Qed.
Lemma wBisims_steps A (d : M A) (n : nat) : steps n d ≈s d .
Proof.
elim: n d => [|n IH] d //.
case: d IH => // d IH /=.
by rewrite IH wBisims_DLater.
Qed.
Lemma Terminates_wBisims A (d1 d2 : M A) (a : A) : Terminates d1 a -> d1 ≈s d2 -> Terminates d2 a.
Proof.
move => Ht1.
elim: Ht1 => [b|d b].
  move=> [n Hd].
  rewrite steps_Dnow in Hd.
  apply Terminates_steps.
  exists n.
  by symmetry.
move => Ht1 IH.
by rewrite wBisims_DLater.
Qed.
Corollary iff_Terminates_steps {A} (d : M A) (n : nat) (a : A) : Terminates d a <-> Terminates (steps n d) a.
Proof.
split => Ht.
  exact: (Terminates_wBisims Ht (wBisims_sym (wBisims_steps d n))).
exact: (Terminates_wBisims Ht (wBisims_steps d n)).
Qed.
Lemma iff_Terminates_wBsret {A} (d : M A) (a : A) : Terminates d a <-> (d ≈s Ret a).
Proof.
split.
  move => H.
  elim: H => //= d' a' _ H.
  by rewrite (wBisims_DLater d') H.
move => [m H].
apply (iff_Terminates_steps d m a).
rewrite H steps_Dnow.
by apply TDNow.
Qed.
Corollary iff_Diverges_steps {A} (d : M A) (n : nat) : Diverges d <-> Diverges (steps n d).
Proof.
apply iff_not2.
split.
  move => [a Ht].
  exists a.
  by apply iff_Terminates_steps.
move => [a Ht].
exists a.
by apply/(iff_Terminates_steps _ n _).
Qed.
Lemma iff_Diverges_wBisimspin {A} (d : M A) : Diverges d <-> wBisim d (@spin A).
Proof.
split.
  move => /Diverges_spinP HD.
  by rewrite HD.
move => Ho [a Ht].
have H : Diverges (@spin A).
  by apply/Diverges_spinP.
apply H.
exists a.
by apply (Terminates_wBisim Ht Ho).
Qed.
Lemma iff_Diverges_wBisimsspin {A} (d : M A) : Diverges d <-> d ≈s (@spin A).
Proof.
split.
- move => /Diverges_spinP HD.
  by rewrite HD.
move => [n Hs].
apply/(iff_Diverges_steps d n).
rewrite Hs.
by apply/(iff_Diverges_steps (@spin A) n)/(Diverges_spinP).
Qed.
Theorem iff_wBisims_wBisim A (d1 d2 : M A) : d1 ≈s d2 <-> wBisim d1 d2.
Proof.
split.
  case: (TerminatesP d1) => [[a Ht] Hd|/Diverges_spinP Hs].
    pfold.
    exact : (wBTerminate _ Ht (Terminates_wBisims Ht Hd)).
  rewrite Hs; clear Hs.
  move => /wBisims_sym/iff_Diverges_wBisimsspin/Diverges_spinP Hs.
  by rewrite Hs.
case: (TerminatesP d1) => [[a Ht]|/Diverges_spinP Hs].
  move/(Terminates_wBisim Ht).
  move: Ht => /Terminates_steps [n Ht1] /Terminates_steps [m Ht2].
  by rewrite -(wBisims_steps d1 n) -(wBisims_steps d2 m) Ht1 Ht2.
rewrite Hs;clear Hs.
move/wBisim_sym/iff_Diverges_wBisimspin/Diverges_spinP.
move => Hs.
by rewrite Hs.
Qed.
Lemma iff_Terminates_wBret {A} (d : M A) (a : A) : Terminates d a <-> (d ≈ Ret a).
Proof.
split.
  move/ iff_Terminates_wBsret.
  by apply iff_wBisims_wBisim.
move/iff_wBisims_wBisim.
by apply iff_Terminates_wBsret.
Qed.
(*
Lemma steps_bind {A B} (n : nat) (m : M A) (f : A -> M B) : steps n (m >>= f) ≈s  m >>= ((steps n) \o f).
Abort.
Lemma steps_ret {A} (n:nat) (a : A) : steps n (@ret M A a) ≈s @ret M A a.
Abort.
Lemma steps_monotonisity {A} (n : nat) (d : Delay A) : steps n d  ≈s d.
Abort.
*)
CoFixpoint while {A B} (body : A -> M (B + A)) : A -> M B :=
      fun a => body a >>= (fun ab => match ab with
                                      |inr a => DLater (while body a)
                                      |inl b => DNow b end).
Lemma whileE A B (f : A -> M (B + A)) (a : A) : while f a =  f a >>= (fun ab => match ab with
                                      |inr a => DLater (while f a)
                                      |inl b => DNow b end).
Proof.
rewrite [LHS](DelayE) //=.
by case: (f a) => [[b'|a'] | d]; rewrite [RHS](DelayE).
Qed.
Lemma bindDmf A B (m : M A) (f : A -> M B) : (DLater m) >>= f = DLater (m >>= f).
Proof. by rewrite [LHS]DelayE. Qed.
Lemma Diverges_bindspinf A B (f : A -> M B) : Diverges ((@spin A) >>= f).
Proof.
apply/Diverges_spinP/strongBisim_eq.
pcofix CIH.
pfold.
rewrite -spinE -(spinE B) bindDmf.
apply: sBLater.
by right.
Qed.
Lemma Terminates_bindmf A B (d : M A) (a : A) (f : A -> M B) : Terminates d a -> d >>= f ≈s f a.
Proof.
move => Ht.
elim: Ht => [a'|d' a' Ht Hd'].
  by rewrite bindretf.
by rewrite -Hd' bindDmf wBisims_DLater.
Qed.
Lemma bindmwBs {A B} (f : A -> M B) (d1 d2 : M A) : d1 ≈s d2 -> d1 >>= f ≈s d2 >>= f.
Proof.
case: (TerminatesP d1) => [[a Ht1] /(Terminates_wBisims Ht1) Ht2|/Diverges_spinP HD].
  by rewrite (Terminates_bindmf f Ht1) (Terminates_bindmf f Ht2).
rewrite HD.
by move => /wBisims_sym/iff_Diverges_wBisimsspin/Diverges_spinP Hd2; subst.
Qed.
Lemma bindmwB {A B} (f : A -> M B) (d1 d2 : M A) : d1 ≈ d2 -> d1 >>= f ≈ d2 >>= f.
Proof.
move => /iff_wBisims_wBisim H.
apply iff_wBisims_wBisim.
exact: (bindmwBs _ H).
Qed.
Lemma bindfwB {A B} (f g : A -> M B) (d : M A) : (forall a, f a ≈ g a) -> d >>= f ≈ d >>= g.
Proof.
move => H.
move: d.
pcofix CIH => d.
case: d => [a|d].
  rewrite !bindretf.
  exact: (paco2_mon_bot _ _ (H a)).
rewrite !bindDmf.
pfold.
apply wBLater.
by right.
Qed.
Lemma bindfwBs {A B} (f g : A -> M B) (d : M A) : (forall a, f a ≈s g a) -> d >>= f ≈s d >>= g.
Proof.
move => H.
apply iff_wBisims_wBisim.
apply bindfwB => a.
by apply/iff_wBisims_wBisim/(H a).
Qed.

Add Parametric Morphism A B : bind
  with signature (@wBisims A) ==> (pointwise_relation A (@wBisims B)) ==> (@wBisims B) as bindmors.
Proof.
move => x y Hxy f g Hfg.
apply: wBisims_trans.
- apply: (bindmwBs _ Hxy).
- apply: (bindfwBs y Hfg).
Qed.

Add Parametric Morphism A B : bind
  with signature (@wBisim A) ==> (pointwise_relation A (@wBisim B)) ==> (@wBisim B) as bindmor.
Proof.
move => x y Hxy f g Hfg.
apply: wBisim_trans.
- apply: (bindmwB _ Hxy).
- apply: (bindfwB y Hfg).
Qed.

(* the next four laws derived from Complete Elgot monads *)
Lemma fixpointEs {A B} (f : A -> M (B + A)) : forall (a : A), while f a ≈s (f a) >>= (sum_rect (fun => M B ) (@ret M B ) (while f)).
Proof.
move => a.
rewrite whileE.
apply: bindfwBs => ba.
case: ba => [b'|a'] //=.
by apply wBisims_DLater.
Qed.
Lemma fixpointE {A B} (f : A -> M (B + A)) : forall (a : A), while f a ≈ (f a) >>= (sum_rect (fun => M B ) (@ret M B ) (while f)).
Proof. by move => a; apply iff_wBisims_wBisim; apply fixpointEs. Qed.

Lemma naturalityE' {A B C} (f : A -> M (B + A))(g : B -> M C)(d : M (B + A)) :
d >>= (fun ab : B + A => match ab with
                                   | inl b => DNow b
                                   | inr a => DLater (while f a)
                                   end) >>= g ≈
    d >>= sum_rect (fun=> M (C + A)) (M # inl \o g) (M # inr \o (@ret M A)) >>=
     (fun ab : C + A => match ab with
                        | inl b => DNow b
                        | inr a => DLater (while (fun y : A => f y >>= sum_rect (fun=> M (C + A)) (M # inl \o g) (M # inr \o (@ret M A))) a)
                        end).
Proof.
move: d.
pcofix CIH => d.
case: d => [[b|a]|d].
- apply (@paco2_mon_bot _ _ (@wBisim_gen C)) => //.
  rewrite! bindretf /= fmapE bindA.
  case: (TerminatesP (g b)) => [[c /iff_Terminates_wBret Ht]|/Diverges_spinP HD].
    rewrite Ht !bindretf.
    exact: wBisim_refl.
  rewrite HD.
  apply: wBisim_sym.
  apply iff_Diverges_wBisimspin.
  exact: Diverges_bindspinf.
- rewrite! bindretf /= fmapE bindA bindretf /= bindretf /= bindDmf.
  pfold.
  apply wBLater.
  rewrite whileE whileE.
  right.
  exact: CIH.
- rewrite! bindDmf.
  pfold.
  apply wBLater.
  right.
  exact: CIH.
Qed.
Lemma naturalityE {A B C} (f : A -> M (B + A)) (g : B -> M C) (a : A) :
   (while f a) >>= g ≈ while (fun y => (f y) >>= (sum_rect (fun => M (C + A)) (M # inl \o g) (M # inr \o (@ret M A )))) a.
Proof. by rewrite whileE whileE; apply naturalityE'. Qed.
Lemma codiagonalE' {A B} (f: A -> M ((B + A) + A))(d: M ((B + A) + A)) :
  d >>= (Ret \o sum_rect (fun=> (B + A)%type) idfun inr) >>=
  (fun ab : B + A => match ab with
                     | inl b => DNow b
                     | inr a => DLater (while (M # sum_rect (fun=> (B + A)%type) idfun inr \o f) a)
                     end) ≈
  d >>= (fun ab : B + A + A => match ab with
                                    | inl b => DNow b
                                    | inr a => DLater (while f a)
                                    end) >>= (fun ab : B + A => match ab with
                                                                 | inl b => DNow b
                                                                 | inr a => DLater (while (while f) a)
                                                                 end).
Proof.
move: d.
pcofix CIH => d.
case: d => [ [[b|a]|a]|d'].
- apply (@paco2_mon_bot _ _ (@wBisim_gen B)) => //.
  rewrite bindretf bindretf bindretf //= bindretf.
  by apply wBisim_refl.
- rewrite bindretf bindretf bindretf //= bindretf whileE whileE whileE //= fmapE.
  pfold.
  apply wBLater.
  right.
  exact: CIH.
- rewrite bindretf bindretf bindretf //= bindDmf whileE whileE //= fmapE.
  pfold.
  apply wBLater.
  right.
  exact: CIH.
- rewrite! bindDmf.
  pfold.
  apply wBLater.
  right.
  exact: CIH.
Qed.
Lemma codiagonalE {A B} (f : A -> M ((B + A) + A)) (a : A) : while ((Delay # ((sum_rect (fun => (B + A)%type) idfun inr)))  \o f ) a ≈ while (while f) a.
Proof. by rewrite whileE whileE whileE //= fmapE; apply codiagonalE'. Qed.

Lemma whilewBs1 {X A} (f g : X -> M(A + X)) :
  (forall x, wBisims (f x) (g x)) ->
  forall d1 d2: M (A + X),
    d1 ≈s d2 ->
    d1 >>= (fun ax : A + X => match ax with
                               | inl a => DNow a
                               | inr x => DLater (while f x)
                               end) = @spin A ->
    strongBisim (d2 >>= (fun ax : A + X => match ax with
                                     | inl a => DNow a
                                    | inr x => DLater (while g x) end))
          (@spin A).
Proof.
move => Hfg.
pcofix CIH => d1 d2 Hd.
case: d1 Hd => [[b|a]|d1'].
- move => _ contr.
  contradict contr.
  rewrite bindretf.
  by rewrite -spinE.
- case: d2 => [ba|d2'].
    move => [n Hd].
    rewrite steps_Dnow steps_Dnow in Hd.
    rewrite -Hd bindretf bindretf -spinE => Hf.
    case: Hf.
    rewrite whileE whileE => Hf.
    pfold.
    apply sBLater.
    right.
    exact: (CIH _ _ (Hfg a) Hf).
  move => Hd Hf.
  rewrite -spinE bindDmf.
  pfold.
  apply sBLater.
  have Had: DNow (inr a) ≈s d2'.
    by rewrite Hd wBisims_DLater.
  right.
  exact: (CIH _ _ Had Hf).
case: d2 =>[[b|a]|d2'] Hd.
- move/Diverges_spinP/iff_Diverges_wBisimsspin.
  rewrite (bindmwBs _ Hd) bindretf => /iff_Diverges_wBisimsspin/Diverges_spinP contr.
  contradict contr.
  by rewrite -spinE.
- set x := (x in DLater d1' >>= x).
  move => Hf.
  have: (DLater d1' >>= x) ≈s (DNow (inr a) >>= x).
    by rewrite (bindmwBs _ Hd).
  subst x.
  rewrite Hf bindretf.
  move => Hs.
  rewrite bindretf -spinE whileE.
  pfold.
  apply sBLater.
  right.
  apply: (CIH _ _ (Hfg a)).
  rewrite -whileE.
  apply/Diverges_spinP/iff_Diverges_wBisimsspin.
  by rewrite Hs wBisims_DLater.
- move => Hf.
  rewrite -spinE bindDmf.
  pfold.
  apply sBLater.
  right.
  have Hd2 : DLater d1' ≈s d2'.
    by rewrite Hd wBisims_DLater.
  apply: (CIH _ _ Hd2 Hf).
Qed.
Lemma whilewBs2 {A B} (d1 d2 : M (B + A)) (f g : A -> M (B + A)) (b : B) : (forall a, wBisims (f a) (g a)) -> wBisims d1 d2 -> wBisims (d1 >>= (fun ab : B + A => match ab with
                                   | inl b => DNow b
                                   | inr a => DLater (while f a)
                                   end)) (@ret M B b) -> wBisims (d2 >>= (fun ab : B + A => match ab with
                                   | inl b => DNow b
                                   | inr a => DLater (while g a)
                                   end)) (@ret M B b).
Proof.
move => Hfg Hd [n Hf].
move : d1 d2 Hd Hf.
rewrite steps_Dnow.
elim: n => [d1 d2|n IH d1 d2].
  case: d1 => [[b'|a']|d1'].
    rewrite bindretf => /wBisims_sym Hd //= Hf.
    by rewrite (bindmwBs _ Hd) bindretf Hf.
  by rewrite bindretf /= => _ Hf.
  by rewrite bindDmf /= => _ Hf.
case: d1 => [[b'|a']|d1'] H.
  - rewrite bindretf steps_Dnow -(bindmwBs _ H) bindretf => Hb.
    by rewrite Hb.
  - rewrite bindretf /= -(bindmwBs _ H) bindretf wBisims_DLater whileE whileE.
    by apply: (IH (f a') (g a') (Hfg a')).
  - move: H.
    rewrite bindDmf /= wBisims_DLater.
    by apply: IH.
Qed.
Lemma whilewBs {A B} (f g : A -> M (B + A)) (a : A) : (forall a, (f a) ≈s (g a)) -> while f a ≈s while g a.
Proof.
move => Hfg.
case: (TerminatesP (while f a)) => [[b /iff_Terminates_wBsret HT]| /Diverges_spinP HD].
  rewrite HT.
  setoid_symmetry.
  move: HT.
  rewrite! whileE.
  exact: (whilewBs2 Hfg (Hfg a)).
- rewrite HD.
  setoid_symmetry.
  apply/iff_Diverges_wBisimsspin/Diverges_spinP/strongBisim_eq.
  move: HD.
  rewrite !whileE.
  exact: (whilewBs1 Hfg (Hfg a)).
Qed.
Lemma whilewB {A B} (f g : A -> M (B + A)) (a : A) : (forall a, (f a) ≈ (g a)) -> while f a ≈ while g a.
Proof.
move => H.
apply iff_wBisims_wBisim.
apply whilewBs => a'.
apply iff_wBisims_wBisim.
by apply (H a').
Qed.

Add Parametric Morphism A B : while
  with signature (pointwise_relation A (@wBisim (B + A))) ==> @eq A ==> (@wBisim B ) as whilemor.
Proof. by move=> f g + a; exact: whilewB. Qed.
Lemma uniformE {A B C} (f : A -> M (B + A)) (g : C -> M (B + C)) (h : C -> A) :
  (forall c, f (h c) = g c >>= sum_rect (fun => M (B + A)) ((M # inl) \o Ret) ((M # inr) \o Ret \o h)) ->
  forall c, (while f) (h c) ≈ while g c.
Proof.
move => H c.
rewrite whileE (H c) whileE.
set d := (g c).
move : d.
pcofix CIH => d.
case: d => [[b'|c']|d].
- apply (@paco2_mon_bot _ _ (@wBisim_gen B)) => //.
  rewrite !bindretf/= fmapE !bindretf/=.
  by apply wBisim_refl.
- rewrite !bindretf/= fmapE !bindretf/=.
  pfold.
  apply: wBLater.
  rewrite whileE whileE H.
  right.
  exact: CIH.
- rewrite !bindDmf.
  pfold.
  apply: wBLater.
  right.
  exact: CIH.
Qed.
HB.instance Definition _ := @isMonadDelay.Build M
  (@while) wBisim wBisim_refl wBisim_sym wBisim_trans (@fixpointE) (@naturalityE) (@codiagonalE) (@bindmwB) (@bindfwB) (@whilewB) (@uniformE).
End delayops.
End DelayOps.
HB.export DelayOps.
