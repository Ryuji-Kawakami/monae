From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import hierarchy.

Local Open Scope monae_scope.

Section delayexample.

Notation "a '≈' b" := (wBisim a b).
Variable M : delayMonad.
Fixpoint fact (n:nat) :nat := match n with
                          |O => 1
                          |S n' => n * fact n'
                          end.
Definition fact_body: nat * nat -> M (nat + nat*nat)%type := fun (a: nat * nat) =>
                                            match a with
                                            |(O, a2) => ret _ (inl a2)
                                             |(S n', a2) => ret _ (inr (n', a2 * (S n') ))
                                            end .
Definition factdelay := fun (nm:nat*nat) => while fact_body nm.
Lemma eq_fact_factdelay :forall n m, factdelay (n,m) ≈ ret nat (m * fact n).
Proof.
move => n.
rewrite/factdelay.
elim: n.
- move =>m.
  by rewrite fixpointE //= bindretf muln1 //=.
- move => n IH m.
  by rewrite fixpointE //= bindretf //= IH mulnA.
Qed.
Definition collatzm_body (m:nat) (n:nat) : M (nat + nat)%type :=
  if n == 1 then ret _ (inl m)
  else if n %%2 == 0 then ret _ (inr (n./2))
       else ret _ (inr (3 * n + 1)).
Definition collatzm (m:nat) := fun n => while (collatzm_body m) n.
Definition delaymul (m:nat) (d: M nat) :M nat := d >>= (fun n => ret _ (m * n)).
Lemma collatzm_mul : forall (m n p: nat), delaymul p (collatzm m n)  ≈ collatzm (p * m ) n . 
Proof.
move => m n p.
rewrite /collatzm /delaymul.
rewrite naturalityE.
set x := (x in while x).
set y := collatzm_body (p*m).
have <-: x = y.
  apply boolp.funext => q.
  subst x y.
  case_eq (q == 1) => Hs.
  + by rewrite /collatzm_body Hs bindretf //= fmapE bindretf //=.
  + rewrite/collatzm_body Hs.
  case He: (q %% 2 == 0).
  * by rewrite bindretf //= fmapE bindretf //=.
  * by rewrite bindretf //= fmapE bindretf //=.
done.
Qed.
Definition minus1_body (nm: nat*nat)  :M ((nat + nat*nat) + nat*nat)%type:= match nm with
                                                                |(O, m) => match m with
                                                                         |O => ret _ (inl (inl O))
                                                                         |S m' => ret _ (inl (inr (m', m')))
                                                                         end
                                                                |(S n', m) => ret _ (inr (n', m ))
                                                                end.
Definition minus1 := fun nm => while (while minus1_body) nm.
Definition minus2_body (nm: nat*nat) : M (nat + nat*nat)%type := match nm with
                                                      |(O,m) => match m with
                                                                |O => ret _ (inl O)
                                                                |S m' => ret _ (inr (m', m'))
                                                                end
                                                      |(S n', m) => ret _ (inr (n',m))
                                                      end.
Definition minus2 := fun nm => while minus2_body nm.
Lemma eq_minus : forall (nm: nat*nat), minus1 nm  ≈  minus2 nm.
Proof.
move => nm.
rewrite/minus1 /minus2.
rewrite -codiagonalE.
apply: wBisim_whilewB.
move => [n m].
  case: n.
  + case: m => //= .
     * by rewrite fmapE bindretf.
     * move => n.
       by rewrite fmapE bindretf.
  + move => n //=.
    by rewrite fmapE bindretf.
Qed.
Definition collatzs1_body (nml: nat*nat*nat) : M ((nat*nat + nat*nat*nat))%type :=
match nml with (n,m,l) =>
if (l %% 4 == 1) && (n == 1) then ret _ (inl (m,l))
else if (n == 1) then ret _ (inr (m+1,m+1,0))
                 else if (n %% 2) == 0 then ret _ (inr (n./2,m,l+1))
                               else ret _ (inr (3*n + 1, m, l+1))
end.
Definition collatzs1 (n:nat):= while collatzs1_body (n,n,0).
Definition collatzs2'_body (nml: nat*nat*nat) : M ((nat*nat + nat*nat*nat) + nat*nat*nat)%type :=
match nml with (n,m,l) =>
if n== 1 then ret _ (inl(inr (m+1, m+1, l)))
         else if (n %% 2 == 0) then ret _ (inr (n./2,m,l+1))
                               else ret _ (inr (3*n + 1, m, l+1))
end.
Definition collatzs2_body (nml: nat*nat*nat) : M (nat*nat + nat*nat*nat)%type:=
match nml with (n,m,l) => if (l %% 4 == 1) then ret _ (inl (m,l)) else (while collatzs2'_body (n,n,0)) end.
Definition collatzs2 (n: nat) := (while collatzs2_body) (n,n,0).

Definition collatzaux_body (nml: nat*nat*nat) : M ((nat*nat + nat*nat*nat) + nat*nat*nat)%type :=
match nml with (n,m,l) =>
if n== 1 then if (l %% 4 == 1) then ret _ (inl(inl (m,l))) else ret _ (inl(inr (m+1, m+1, 0)))
         else if (n %% 2 == 0) then ret _ (inr (n./2,m,l+1))
                               else ret _ (inr (3*n + 1, m, l+1))
end.
(*
Lemma collatstepcE (n: nat): collatzs1 n ≈ collatzs2 n.  
Proof.
have: forall n, collatzs2_body (n,n,0) ≈ (while _ _ collatzaux_body) (n,n,0).
  move => n'.
  rewrite/collatzaux_body/collatzs2_body.  
  simpl.
  apply: wBisim_trans.
    + apply fixpointE.
    + simpl.
      case_eq (n' == 1) => Hn.
      * rewrite bindretf. simpl.
        rewrite wBisim_sym.
        apply: wBisim_trans.
        apply fixpointE.
        simpl. rewrite Hn. rewrite bindretf. simpl. apply wBisim_refl.
      * case_eq (n' %% 2 == 0) => He.
        ** simpl. rewrite bindretf. simpl. rewrite wBisim_sym. apply: wBisim_trans.
           apply fixpointE. simpl. rewrite Hn. rewrite He. simpl. rewrite bindretf. simpl. rewrite/collatzs2'_body.




  case_eq (l %% 4 == 1) => Hl.
  - case_eq (p == 1) => Hp. 
    + rewrite wBisim_sym.
      apply: wBisim_trans.
      * apply fixpointE.
      * rewrite //= Hp Hl bindretf //=. 
        by apply wBisim_refl.
    + rewrite wBisim_sym.
      apply: wBisim_trans.
      * apply fixpointE.
      * simpl.
        rewrite Hp.
        case_eq (p %% 2 == 0) => Hp'.
        ** rewrite bindretf.
           simpl.

rewrite //= Hp Hl bindretf //=. 
        by apply wBisim_refl.
rewrite/collatzs1/collatzs2.
rewrite/collatzs1_body/collatzs2_body. 
rewrite wBisim_sym.
apply wpreserve.
- case_eq (p == 1) => Hp //=.
  + by apply wBisim_refl. 
  + 
*)

Definition divide5_body (f:nat -> M nat)(nm: nat*nat):M(nat + nat*nat)%type := 
match nm with (n,m) => 
  if m %% 5 == 0 then ret _ (inl m) 
                 else f n >>= (fun x => ret _ (inr (n.+1 , x))) end.

Definition dividefac1 (n: nat):= while (divide5_body (fun n => factdelay (n, 1))) (n,1).
Definition dividefac2 (n: nat):= while (divide5_body (fun n => ret _ (fact n))) (n,1).
Lemma eq_dividefac: forall n, dividefac1 n ≈ dividefac2 n.
Proof.
move => n.
rewrite/dividefac1/dividefac2.
apply wBisim_whilewB.
move => [k l].
case/boolP: (l %% 5 == 0) => Hl //=.
- by rewrite Hl.
- rewrite !ifN // bindretf.
  rewrite wBisim_bindmwB; last by apply (eq_fact_factdelay k 1).
  by rewrite bindretf mul1n.
Qed.
Definition fastexp_body (nmk: nat*nat*nat) :M (nat + nat*nat*nat)%type :=
match  nmk with (n,m,k) => if n == 0 then ret _ (inl m)
                           else (if odd n then ret _ (inr (n.-1 , m*k, k))
                                 else ret _ (inr (n./2, m, k*k) )) end.
Definition fastexp (n m k: nat) := while fastexp_body (n,m,k).
Fixpoint exp (n k: nat) := match n with |O => 1 | S n' => k*exp n' k end.
Lemma expE_aux (n:nat):n <= n.*2.
Proof.
elim: n => //= n IH.
rewrite doubleS.
rewrite ltnS.
apply (leq_trans IH).
apply leqnSn.
Qed.
Lemma expE: forall n m k, fastexp n m k ≈ ret nat (m * expn k n).
Proof.
move => n.
rewrite/fastexp/fastexp_body.
elim: n {-2}n (leqnn n) => n.
- rewrite leqn0 => /eqP H0 m k.
  by rewrite H0 fixpointE /= bindretf //= expn0 mulnS muln0 addn0.
- move => IH [|m'] Hmn m k.
  + by rewrite fixpointE //= bindretf //= mulnS muln0 addn0.
  + case/boolP: (odd (m'.+1)) => Hm'.
    * by rewrite fixpointE Hm' //= bindretf //= IH //= expnSr (mulnC (k^m') k) mulnA.
    * rewrite fixpointE //= ifN //= bindretf //= IH.
      ** by rewrite uphalfE mulnn -expnM mul2n (even_halfK Hm').
      ** rewrite ltnS in Hmn.
         rewrite leq_uphalf_double.
         apply (leq_trans Hmn).
         apply expE_aux.
Qed.
