Require Export Omega.
Require Export Strings.String.
Local Open Scope string_scope.
Require Export Lists.List.
Export ListNotations.

Module Type TokenMod.

Parameter TOKENtp : Type.
Parameter dec_eq_tok : forall (tok1 tok2:TOKENtp), { tok1 = tok2 } + { tok1 <> tok2 }.

End TokenMod.

Module PrelimTheory (TM : TokenMod).
  
Export TM.

Fixpoint nthcdr (n:nat) (tl:list TOKENtp) {struct tl} : list TOKENtp :=
match n,tl with
| O,tl => tl
| S n,(tok::tr) => nthcdr n tr
| S n,nil => tl
end.

(*** "Tebbi Sublist" ***)
(*** This will be always be a sublist of tl1 and will specifically be tl2 if tl2 is a sublist of tl1. ***)
Definition tsubl (tl1 tl2:list TOKENtp) : list TOKENtp :=
nthcdr (minus (length tl1) (length tl2)) tl1.

Inductive subl (tl : list TOKENtp) : list TOKENtp -> Prop :=
| sublref : subl tl tl
| sublcons a tl' : subl tl tl' -> subl tl (a::tl').

Lemma subl_app (tl tl1 tl2:list TOKENtp) : subl tl tl2 -> subl tl (tl1 ++ tl2).
Proof.
  intros H1. induction tl1; simpl; try assumption.
  now apply sublcons.
Qed.  

Lemma subl_nil (tl:list TOKENtp) : subl nil tl.
Proof.
  induction tl.
  - apply sublref.
  - now apply sublcons.
Qed.

Lemma subl_leq tl1 tl2 : subl tl2 tl1 -> length tl2 <= length tl1.
intros H. induction H.
- omega.
- simpl. omega.
Qed.

Lemma subl_inv1 a tl tl' :
subl (a::tl) tl' -> subl tl tl'.
remember (a :: tl). intros H. induction H.
- rewrite Heql. apply sublcons. now apply sublref.
- now apply sublcons.
Qed.

Lemma subl_tra (tl1 tl2 tl3:list TOKENtp) :
 subl tl1 tl2 -> subl tl2 tl3 -> subl tl1 tl3.
intros A B. revert tl1 A. induction B; intros tl1 C; try tauto.
apply sublcons. now apply IHB.
Qed.

Lemma tsubl_ref tl : tsubl tl tl = tl.
induction tl.
- reflexivity.
- unfold tsubl. simpl.
   assert (H1:length tl - length tl = 0) by omega.
   rewrite H1. reflexivity.
Qed.

Lemma subl_tsubl_eq tl1 tl2 : subl tl2 tl1 -> tsubl tl1 tl2 = tl2.
intros H. induction H.
- now apply tsubl_ref.
- unfold tsubl.
   change (nthcdr (S (length tl') - length tl2) (a :: tl') = tl2).
   assert (H1:length tl2 <= length tl') by now apply subl_leq.
   assert (H2:S (length tl') - length tl2 = S (length tl' - length tl2)) by omega.
   rewrite H2. simpl. exact IHsubl.
Qed.

Lemma tsubl_app_eq tl tr : tsubl (tl ++ tr) tr = tr.
Proof.
  exact (subl_tsubl_eq (tl ++ tr) tr (subl_app tr tl tr (sublref tr))).
Qed.

Lemma tsubl_cons_eq t tl : tsubl (t::tl) tl = tl.
Proof.
  rewrite subl_tsubl_eq.
  - reflexivity.
  - apply sublcons. apply sublref.
Qed.

Lemma cons_app_neq (t:TOKENtp) tl tr : (t::tl ++ tr) <> tr.
Proof.
  intros H. generalize (app_length (t::tl) tr).
  change (length (t :: tl ++ tr) =
          length (t :: tl) + length tr -> False).
  rewrite H. simpl. omega.
Qed.

Lemma cons_subl_neq ts t tl : subl ts tl -> ts <> t::tl.
Proof.
  intros H1 H2. generalize (subl_leq _ _ H1).
  rewrite H2. simpl. omega.
Qed.

Lemma cons_neq (X:Type) (x:X) l : l <> x::l.
induction l; try discriminate.
intros H. inversion H. tauto.
Qed.

Lemma cons_nsubl t tl : ~subl (t::tl) tl.
revert t; induction tl; intros t H.
- inversion H.
- inversion H.
  + symmetry in H2. revert H2. apply cons_neq.
  + apply subl_inv1 in H1. revert H1. apply IHtl.
Qed.

Definition dec_eq_nat (n m:nat) : { n = m } + { n <> m }.
decide equality.
Defined.

Definition dec_eq_list_tok (l1 l2:list TOKENtp) : { l1 = l2 } + { l1 <> l2}.
revert l2. induction l1; intros [|b l2].
- tauto.
- right. discriminate.
- right. discriminate.
- destruct (IHl1 l2) as [H1|H1].
  + destruct (dec_eq_tok a b) as [H2|H2].
    * left. congruence.
    * right. intros H3. inversion H3. tauto.
  + right. intros H3. inversion H3. tauto.
Defined.

Fixpoint lt_b (n m:nat) : bool :=
match n,m with
| _,O => false
| O,_ => true
| S n,S m => lt_b n m
end.

Lemma lt_lt_b_t (n m:nat) : lt_b n m = true <-> n < m.
revert m. induction n; intros [|m]; simpl; split; try discriminate; try omega; try reflexivity.
- intros H1. apply IHn in H1. omega.
- intros H1. apply IHn. omega.
Qed.

Lemma lt_lt_b_f (n m:nat) : lt_b n m = false <-> ~(n < m).
case_eq (lt_b n m); intros H1; split; try discriminate.
- apply lt_lt_b_t in H1. tauto.
- intros _ H2. apply lt_lt_b_t in H2. rewrite H2 in H1. discriminate.
- reflexivity.
Qed.

Lemma complete_ind (p:nat -> Prop) :
(forall n, (forall m, m < n -> p m) -> p n) -> (forall n, p n).
Proof.
  intros H1 n. apply H1. induction n.
  - intros m. omega.
  - intros m H2. apply H1. intros k H3. apply IHn. omega.
Qed.

Lemma complete_subl_ind (p:list TOKENtp -> Prop) :
(forall tl, (forall tr, subl tr tl -> tr <> tl -> p tr) -> p tl)
-> forall tl, p tl.
Proof.
  intros IH.
  assert (L:forall n, forall tl, length tl = n -> p tl).
  {
    apply (complete_ind (fun n => forall tl, length tl = n -> p tl)).
    intros n H1 tl H2. apply IH. intros tr H3 H4.
    inversion H3.
    - tauto.
    - apply H1 with (m := (length tr)).
       + generalize (subl_leq _ _ H). subst tl. simpl in H2. omega.
       + reflexivity.
  }
  intros tl. apply L with (n := (length tl)). reflexivity.
Qed.

End PrelimTheory.