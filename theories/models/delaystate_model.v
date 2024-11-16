Require Import JMeq.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import finmap.
From mathcomp Require boolp.
From mathcomp Require Import classical_sets.
From infotheo Require convex classical_sets_ext.
Require Import preamble.
From HB Require Import structures.
Require Import hierarchy monad_lib fail_lib state_lib trace_lib.
Require Import monad_transformer.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.
Module TensorS.
Section tensors.
Variable S:UU0.
Definition tensorS := fun (A: UU0) => (A * S)%type. 
Definition actmt (X Y: UU0):(X -> Y) -> tensorS X -> tensorS Y:=(fun f: X -> Y =>  (fun xs:X * S => match xs with (x, s) => (f x, s) end)). 
Let tensor_id : FunctorLaws.id actmt.
Proof.
rewrite/actmt/FunctorLaws.id => B. 
apply boolp.funext => x.
by case: x.
Qed.
Let tensor_o : FunctorLaws.comp actmt.
Proof.
rewrite/actmt/FunctorLaws.comp => X Y Z g h.
apply boolp.funext => x.
by case: x.
Qed.
HB.instance Definition _:= isFunctor.Build tensorS tensor_id tensor_o.
End tensors.
End TensorS.
HB.export TensorS.

Module HomS.
Section homs.
Variable S:UU0.
Definition homS := fun (A:UU0) => (S -> A).
Definition actmh (X Y: UU0):(X -> Y) -> homS X -> homS Y := fun (f: X -> Y) => fun (m: S ->X) => f \o m.
Let hom_id : FunctorLaws.id actmh.
Proof.
rewrite/actmh/FunctorLaws.id => B.
by apply boolp.funext => x.
Qed.
Let hom_o : FunctorLaws.comp actmh.
Proof.
rewrite/actmh/FunctorLaws.comp => X Y Z g h.
by apply boolp.funext => x.
Qed.
HB.instance Definition _:= isFunctor.Build homS hom_id hom_o.
End homs.
End HomS.
HB.export HomS.

Module StateTdelay.
Section stateTdelay.
Variable S: UU0.
Variable M: delayMonad.
Hint Extern 0 (wBisim _ _) => setoid_reflexivity.
Notation "a '≈' b" := (wBisim a b).
Definition DS := MS S M.
Lemma DSE {X}: DS X  = (homS S \o M \o tensorS S) X.
Proof. by rewrite/DS/MS/homS/tensorS => //=. Qed.
Lemma homSmap {A B} (f: A -> B) (m:S -> A) : (homS S # f) m = f \o m.
Proof. by []. Qed.
Lemma tensorSmap {A B} (f: A -> B) (m: tensorS S A) : (tensorS S # f) m = let (a, s) := m in (f a, s).
Proof. by []. Qed.
Lemma DSmapE {X Y} (f: X -> Y): DS # f = (homS S \o M \o tensorS S) # f.
Proof.
apply boolp.funext => x.
rewrite -compA FCompE FCompE //= homSmap.
apply boolp.funext => s //=.
rewrite fmapE//=/bindS/retS//=/uncurry/curry fmapE/=.
congr bind.
apply boolp.funext => xs.
by case: xs => x' s' //=.
Qed.
Definition dist1 {X Y} (s:tensorS S (Y + X)) :(tensorS S Y) + (tensorS S X) :=
  let (yx, s) := s in match yx with |inl y => inl (y,s) | inr x => inr (x,s) end.
Definition dist2 {X Y} (xy: (tensorS S Y) + (tensorS  S X)): tensorS S (Y + X) :=
  match xy with | inl (y, s) => (inl y,s) | inr (x, s) => (inr x,s) end.
Definition unitS {X}: X -> homS S (tensorS S X) := fun (x: X) => fun (s: S) => (x, s).
Definition counitS {X}: tensorS S (homS S X) -> X:= fun fs => let (f,s) := fs in f s.
(*curry*)
Definition adjlr {X Y}:((tensorS S X) -> Y) -> (X -> (homS S Y)) := fun f => homS S # f \o unitS.
(*uncurry*)
Definition adjrl {X Y}:(X -> (homS S Y)) -> ((tensorS S X) -> Y) := fun f => counitS \o tensorS S # f.
Lemma adjE1 {X Y} : (@adjlr X Y) \o (@adjrl X Y) = idfun.
Proof. by apply boolp.funext => f //=. Qed.
Lemma adjE2 {X Y} : (@adjrl X Y) \o (@adjlr X Y) = idfun.
Proof. by apply boolp.funext => f /=; apply boolp.funext => sx; case: sx. Qed.
Definition whileDS {X Y} (body: X -> homS S (M (tensorS S (Y + X)))) := adjlr (while (M # dist1 \o adjrl body)).
Definition wBisimDS {A} (ds1 ds2:DS A): Prop := forall s:S, wBisim (ds1 s) (ds2 s).
Section wBisimDS.
Notation "a '≈' b" := (wBisimDS a b).
Lemma wBisimDS_refl A (a: DS A): a ≈ a.
Proof. move => s. apply wBisim_refl. Qed.
Lemma wBisimDS_sym A (d1 d2: DS A): d1 ≈ d2 -> d2 ≈ d1.
Proof. move => Hs s. exact: wBisim_sym. Qed.
Lemma wBisimDS_trans A (d1 d2 d3: DS A): d1 ≈ d2 -> d2 ≈ d3 -> d1 ≈ d3.
Proof. move => H1 H2 s. exact/wBisim_trans/H2. Qed.
End wBisimDS.
Lemma adjlr_preserve {A B} (f g: tensorS S A -> M (tensorS S B)): (forall s a, wBisim (f (s, a)) (g(s, a))) -> forall a, wBisimDS (adjlr f a) (adjlr g a).
Proof. by rewrite/wBisimDS/adjlr => H a s //=; rewrite //=homSmap homSmap//=/unitS. Qed.
(*
Lemma joinE {A}: (@join DS) A  = (homS S # ((@join Delay) (tensorS S A) ) ) \o ((homS S \o Delay) # counitS ) .
Proof.
apply boolp.funext => m.
apply boolp.funext => s.
rewrite FCompE //= homSmap homSmap //= actm_bind.
have -> : (cofix bind_ (u : Delay (Delay (tensorS S A))) : Delay (tensorS S A) := match u with
                                                                                             | DNow x => x
                                                                                             | DLater m' => DLater (bind_ m')
                                                                                             end) (m s >>= (DNow (A:=Delay (tensorS S A)) \o counitS ))
= (m s >>= (@ret Delay _ \o counitS)) >>= idfun.
  by [].
rewrite bindA //=.
congr bind.
apply boolp.funext => xs.
by rewrite bindretf //= /counitS/uncurry //=.
Qed.
Lemma sumrectDSE' {A X}(f: X -> DS (A + X)%type) :
  (homS S \o Delay) # counitS \o  DS # sum_rect (fun =>  DS A) Ret (homS S # while ((Delay # dist1 \o adjrl f)) \o unitS )
= (homS S \o Delay) # (counitS \o tensorS S # (sum_rect (fun =>  DS A) Ret (homS S # while ((Delay # dist1 \o adjrl f)) \o unitS))).
Proof.
by rewrite DSmapE functor_o.
Qed.
Lemma sumrectDSE'' {A X}(f: X -> DS (A + X)%type):
counitS \o (tensorS S # (sum_rect (fun => DS A) Ret (homS S # (while ((Delay # dist1 \o adjrl f))) \o unitS))) =
 sum_rect (fun => (Delay \o tensorS S) A) Ret (while (Delay # dist1 \o adjrl f)) \o dist1.
Proof. apply boolp.funext => ts; case: ts => ax s //=; case: ax => [a|x] //=. Qed.
Lemma sumrectDSE {A X}  (f: X -> DS (A + X)%type) :
  (homS S \o Delay) # counitS \o  DS # sum_rect (fun =>  DS A) Ret (homS S # while ((Delay # dist1 \o adjrl f)) \o unitS )  =
(homS S \o Delay) # sum_rect (fun => (Delay \o tensorS S) A) Ret (while ((Delay # dist1 \o adjrl f))) \o  (homS S \o Delay) # dist1.
Proof.
by rewrite sumrectDSE' -functor_o sumrectDSE''. Qed.
Lemma tunitl  {A X}  (f: X -> DS (A + X)%type) :
 ((homS S \o Delay) # dist1) \o f = ((homS S \o Delay) # dist1) \o (homS S # adjrl f) \o unitS.
Proof. apply boolp.funext => x; rewrite/unitS //= testhomS => //=. Qed.
Lemma tildaf {A X} (f: X -> DS (A + X)%type) :
 ((homS S \o Delay) # dist1) \o (homS S # adjrl f) = homS S # ((Delay # dist1) \o adjrl f).
Proof. by apply boolp.funext => x //= homSmap homSmap FCompE homSmap homSmap. Qed.
Lemma fixpointDSE' {A X} (f: X -> DS (A + X)) (sx: tensorS S X): wBisim (((@join Delay) _ \o (Delay # (sum_rect (fun => (Delay \o tensorS S) A) Ret (while (Delay # dist1 \o adjrl f)))) \o (Delay # dist1 \o adjrl f)) sx) (while ((Delay # dist1 \o adjrl f)) sx).
Proof.
rewrite! compE.
set g := Delay # _ \o _ _. 
rewrite -bindE //= wBisim_sym.
by apply fixpointE.
Qed.
Lemma fixpointDSE'' {A X} (f: X -> DS (A + X)) (x: X): ( f x >>= (sum_rect (fun => DS A ) Ret (whileDS f))) = 
adjlr(((Join \o Delay # sum_rect (fun=> (Delay \o tensorS S) A) Ret (while (Delay # dist1 \o adjrl f))) \o (Delay # dist1 \o adjrl f))) x.
Proof.
rewrite bindE joinE -[LHS]compE.
set g := homS S # Join.
rewrite -(compA g ((homS S \o Delay) # counitS)  (DS # sum_rect (fun=> DS A) Ret (whileDS f))) sumrectDSE -[LHS]compE.
set h := (homS S \o Delay ) # _ .
set k := (homS S \o Delay ) # _ .
rewrite -(compA g (h \o k) f) -(compA h k f).
subst k.
rewrite tunitl tildaf.
subst g h.
rewrite FCompE.
set p := DelayMonad_Delay__canonical__hierarchy_Functor #  _.
set q := Delay # dist1 \o _.
by rewrite compA compA -functor_o -functor_o /adjlr.
Qed.
*)
Lemma fixpointDSE {A B} (f: A -> DS (B + A)%type):
forall (a:A), wBisimDS (whileDS f a) ( f a >>= (sum_rect (fun => DS B ) Ret (whileDS f))).
Proof.
move => a s.
rewrite/whileDS/adjlr/dist1/= MS_bindE !homSmap/=fixpointE/=/adjrl/unitS/=fmapE bindA/=.
under eq_bind => x.
- rewrite bindretf.
  over.
set g := uncurry _.
set h :=  (fun x : tensorS S (B + A) =>
      sum_rect _ _ _ (let (yx, s0) := x in match yx with
                              | inl y => inl (y, s0)
                              | inr x0 => inr (x0, s0)
                              end)).
rewrite bindfwB => //=.
move => [ab x].
subst g h.
rewrite /uncurry => /=.
by case: ab => [b'|a'] //=.
Qed.
Lemma naturalityDSE {A B C} (f: A -> DS (B + A)%type) (g: B -> DS C)(a:A):
   wBisimDS (bindS (whileDS f a) g) (whileDS (fun y => (f y) >>= (sum_rect (fun => DS (C + A)) (DS # inl \o g) (DS # inr \o (@ret DS A )))) a).
Proof.
rewrite/bindS/whileDS/adjlr => s //=.
rewrite !homSmap naturalityE /=.
apply whilewB => sa.
case: sa => s' a' /=.
rewrite/adjrl fmapE fmapE /=MS_bindE !bindA.
apply bindfwB => sba //=.
rewrite/dist1/uncurry bindretf.
case: sba => [[b''|a''] s''] /=.
- rewrite DSmapE -compA FCompE FCompE homSmap/= fmapE fmapE bindA.
  apply bindfwB => cs /=.
  rewrite bindretf /= tensorSmap /=.
  by case: cs => c cs /=.
- rewrite DSmapE -compA FCompE FCompE homSmap/= fmapE fmapE bindA.
  apply bindfwB => cs/=.
  rewrite bindretf /= tensorSmap /=.
  by case: cs => c cs.
Qed.
Lemma codiagonalDSE {A B} (f: A -> DS ((B + A) + A))(a:A):
   wBisimDS (whileDS ((DS # ((sum_rect (fun => (B + A)%type) idfun inr)))  \o f ) a) (whileDS (whileDS f) a).
Proof.
rewrite/whileDS.
apply adjlr_preserve.
rewrite -(compE adjrl _) -(compE adjrl _) adjE2 //= => a' s.
setoid_symmetry.
apply: wBisim_trans.
- apply whilewB => sa /=.
  by rewrite fmapE naturalityE.
- rewrite -codiagonalE DSmapE.
  apply whilewB => sa /=.
  case: sa => a'' s'' //=.
  rewrite/adjrl//=!fmapE.
  have -> : ((homS S \o M) \o tensorS S) # sum_rect (fun=> (B + A)%type) idfun inr = homS S # (M # (tensorS S # sum_rect (fun=> (B + A)%type) idfun inr)).
    by rewrite -compA FCompE.
  rewrite homSmap /= fmapE !bindA.
  apply bindfwB => sbaa.
  case: sbaa => [[[bl|al']|al] sl].
  + by rewrite! bindretf /= fmapE bindretf /= bindretf /=.
  + by rewrite! bindretf /= fmapE !bindretf /=.
  + by rewrite! bindretf /= fmapE bindretf /= bindretf /=.
Qed.
Lemma whilewBDS {A B} (f g: A -> DS (B + A)) (a: A) : (forall a, wBisimDS (f a) (g a)) -> wBisimDS (whileDS f a) (whileDS g a).
Proof.
rewrite/wBisimDS/whileDS => Hfg s.
apply adjlr_preserve => a' s'.
apply whilewB => sa /=.
rewrite! fmapE /adjrl/counitS /=.
case: sa => a'' s'' /=.
by apply bindmwB.
Qed.
Lemma bindmwBDS {A B} (f: A -> DS B) (d1 d2: DS A): wBisimDS d1 d2 -> wBisimDS (d1 >>= f) (d2 >>= f).
Proof. by rewrite /wBisimDS => Hd s /=;rewrite !MS_bindE;apply bindmwB. Qed.
Lemma bindfwBDS {A B} (f g: A -> DS B) (d: DS A): (forall a, wBisimDS (f a) (g a)) -> wBisimDS (d >>= f) (d >>= g).
Proof. by rewrite /wBisimDS => Hfg s /=;rewrite ! MS_bindE /=;apply bindfwB => a's';case: a's'. Qed.
HB.instance Definition _ := MonadState.on DS.
HB.instance Definition _ := @isMonadDelay.Build DS
  (@whileDS) (@wBisimDS) wBisimDS_refl wBisimDS_sym wBisimDS_trans (@fixpointDSE) (@naturalityDSE) (@codiagonalDSE)  (@bindmwBDS) (@bindfwBDS) (@whilewBDS).
(*mathcompで例を探す ex. ssr_num realdomaintype *)
End stateTdelay.
End StateTdelay.
