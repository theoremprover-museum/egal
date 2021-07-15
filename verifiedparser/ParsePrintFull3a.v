Require Export Prelim2.

(***
 Printer and Parser for mathematical expressions with prefix operators, postfix operators,
 infix operators and binders. There are a number of assumptions about the environment (see Hypothesis)
 to avoid ambiguity.

 Use 1000 as strict upper bound for declared priority using penv.
 Use 1010 for most terms and 1023 for "all" terms. 1010 probably includes all terms too.
 S(1023) "start"

 S(q) ::= x | number
            | prefixop[p<q] S(p+1)
            | S(p+1) postfixop[p<q]
            | S(p) infix[p<q,none] S(p)
            | S(p+1) infix[p<q,left] S(p)
            | S(p) infix[p<q,right] S(p+1)
            | S(500) :e S(500)
            | S(500) c= S(500)
            | S(1) S(0) [if q > 0]
            | binder V mid S(1010) [if q > 0]
            | let x ASCTOK S(1010) := S(1010) in S(1010) [if q > 0]
            | let x := S(1010) in S(1010) [if q > 0]
            | { x :e S(1010) | S(1010) }
            | { S(1010) | x :e S(1010) }
            | { S(1010) | x :e S(1010), S(1010) }
            | { x c= S(1010) | S(1010) }
            | { S(1010) | x c= S(1010) }
            | { S(1010) | x c= S(1010), S(1010) }
            | {}
            | { S(1023) [, S(1023)]* }
            | [ S(1023) [, S(1023)]* ]
            | ( S(1023) [, S(1023)]* )
            | if S(1010) then S(1010) else S(1010)
 V    ::= U | U : S(1010) | U :e S(1010) | U c= S(1010) | T
 U    ::= [empty] | x U
 T    ::= [empty] | ( U ) T | ( U : S(1010)) T | ( U :e S(1010)) T | ( U c= S(1010)) T

Version without left recursion:

 S'(q) ::= [empty] | infix[p<q,none] S(p,0) [end p] S'(q)
                   | infix[p<q,left] S(p,0) [end p] S'(q)
                   | infix[p<q,right] S(p+1,0) [end p+1] S'(q)
                   | infix[p<q,none] S(p,1)
                   | infix[p<q,left] S(p,1)
                   | infix[p<q,right] S(p+1,1)
                   | postfixop[p<q] S'(q)
                   | S(0,0) S'(q) [if q > 0]

 S(q,b)  ::= x S'(q) [if b = 0]
           | binder x U mtok S(1010,b') [if q > 0 and b = 1]
           | binder x U ASCTOK S(1010,b') mtok S(1010) [if q > 0 and b = 1]
           | binder TVs mtok S(1010,b') [if q > 0 and b = 1]
           | prefixop[p<q] S(p+1,1)
           | prefixop[p<q] S(p+1,0) S'(q)
           | ( S(1023,b') N ) S'(q) [if b = 0]
           ... etc

 S(q,0)  ::= x S'(q)
           | prefixop[p<q] S(p+1,0) S'(q)
           | ( S(1023,0) N ) S'(q)

 S(q,1)  ::= binder x U mtok S(1010,b') [if q > 0]
           | binder x U ASCTOK S(1010,b') mtok S(1010) [if q > 0]
           | binder TVs mtok S(1010,b') [if q > 0]
           | prefixop[p<q] S(p+1,1)

 TVs   ::= [empty] | ( x U ) TVs | ( x U ASCTOK S(1010) ) TVs
 N     ::= [empty] | , M N
 ASCTOK ::= : | :e | c=

The b in S(q,b) is a boolean output indicating whether or not a binder was reached.
The b is used to decide whether or not to continue parsing with S'(q) after reading an operator.

 ***)
Inductive SetInfixOp := InfMem | InfSubq.

Inductive InfixOp :=
| InfSet : SetInfixOp -> InfixOp
| InfNam : string -> InfixOp.

Inductive AscKind := AscTp | AscSet | AscSubeq.

(*** ATree : Term without information about how to lay it out (i.e., print it). ***)
Inductive ATree :=
| Na : string -> ATree
| Nu : bool -> nat -> nat -> ATree
| Le : string -> option (AscKind * ATree) -> ATree -> ATree -> ATree
| Bi : string -> list ((list string) * (option (AscKind * ATree))) -> ATree -> ATree
| Preo : string -> ATree -> ATree
| Posto : string -> ATree -> ATree
| Info : InfixOp -> ATree -> ATree -> ATree
| Implop : ATree -> ATree -> ATree
| Sep : string -> SetInfixOp -> ATree -> ATree -> ATree
| Rep : string -> SetInfixOp -> ATree -> ATree -> ATree
| SepRep : string -> SetInfixOp -> ATree -> ATree -> ATree -> ATree
| SetEnum : list ATree -> ATree
| MTuple : ATree -> list ATree -> ATree
| Tuple : ATree -> ATree -> list ATree -> ATree
| IfThenElse : ATree -> ATree -> ATree -> ATree
.

Inductive BinderMid : Type := BinderMidComma | BinderMidDarr.

(*** "Layout Tree" - Version with presentation information. ***)
Inductive LTree :=
| Nam : string -> LTree
| Num : bool -> nat -> nat -> LTree
| LetL : string -> option (AscKind * LTree) -> LTree -> LTree -> LTree
| Binder : string -> BinderMid -> list ((list string) * (option (AscKind * LTree))) -> LTree -> LTree
| Preop : string -> LTree -> LTree
| Postop : string -> LTree -> LTree
| Infop : InfixOp -> LTree -> LTree -> LTree
| ImplicitInfop : LTree -> LTree -> LTree
| SepL : string -> SetInfixOp -> LTree -> LTree -> LTree
| RepL : string -> SetInfixOp -> LTree -> LTree -> LTree
| SepRepL : string -> SetInfixOp -> LTree -> LTree -> LTree -> LTree
| SetEnumL : LTreeL -> LTree
| MTupleL : LTree -> LTreeL -> LTree
| Paren : LTree -> LTreeL -> LTree
| IfThenElseL : LTree -> LTree -> LTree -> LTree
with LTreeL :=
| LNil : LTreeL
| LCons : LTree -> LTreeL -> LTreeL
.

Inductive PICase := Postfix | InfixNone | InfixLeft | InfixRight.

(***
 A member penv:ParseEnv can be used to determine if the string
 represents a prefix operator and/or a postfix or infix operator and/or a binder.
 In the case of prefix, postfix and infix operators, penv gives the priority.
 In the case of infix operators, it gives the associativity.
 In the case of binders, it gives the token that separates the bindvars from the body.
 Something can be both a prefix and a postfix operator.
 Something can be both a prefix and an infix operator.
 Nothing can be both a postfix and infix operator.
 ***)
Definition ParseEnv : Type :=
string -> option nat * option (nat * PICase) * option BinderMid.

Variable penv:ParseEnv.

Definition preop_priority (x:string) : option nat :=
match penv x with
| (z,_,_) => z
end.

Definition postinfop_info (x:string) : option (nat * PICase) :=
match penv x with
| (_,z,_) => z
end.

Definition binder_midtok (x:string) : option BinderMid :=
match penv x with
| (_,_,z) => z
end.

Definition nam_p (x:string) :=
match penv x with
| (None,None,None) => True
| _ => False
end.

(*** Conditions: ***)
(*** No prefix operator is also a binder. ***)
Hypothesis penv_Preop_Binder : forall x y p tok, preop_priority x = Some p -> binder_midtok y = Some (tok) -> x <> y.
(*** No prefix operator has the same priority as a postfix operator. ***)
Hypothesis penv_Preop_Postop : forall x y p q, preop_priority x = Some p -> postinfop_info y = Some (q,Postfix) -> p <> q.
(*** No prefix operator has the same priority as a nonassociative infix operator. ***)
Hypothesis penv_Preop_InfixNone : forall x y p q, preop_priority x = Some p -> postinfop_info y = Some (q,InfixNone) -> p <> q.
(*** No prefix operator has the same priority as a left associative infix operator. ***)
Hypothesis penv_Preop_InfixLeft : forall x y p q, preop_priority x = Some p -> postinfop_info y = Some (q,InfixLeft) -> p <> q.
(*** No prefix operator has the same priority as a right associative infix operator. Hmm ***)
Hypothesis penv_Preop_InfixRight : forall x y p q, preop_priority x = Some p -> postinfop_info y = Some (q,InfixRight) -> p <> q.
(*** No right associative infix operator has the same priority as a postfix operator. ***)
Hypothesis penv_InfixRight_Postop : forall x y p q, postinfop_info x = Some(p,InfixRight) -> postinfop_info y = Some (q,Postfix) -> p <> q.
(*** No right associative infix operator has the same priority as a nonassociative infix operator. ***)
Hypothesis penv_InfixRight_InfixNone : forall x y p q, postinfop_info x = Some(p,InfixRight) -> postinfop_info y = Some (q,InfixNone) -> p <> q.
(*** No right associative infix operator has the same priority as a left associative infix operator. ***)
Hypothesis penv_InfixRight_InfixLeft : forall x y p q, postinfop_info x = Some(p,InfixRight) -> postinfop_info y = Some (q,InfixLeft) -> p <> q.
(*** No right associative infix operator has priority 500, the priority of membership and subseteq (SetInf). ***)
Hypothesis penv_InfixRight_not500 : forall x p, postinfop_info x = Some(p,InfixRight) -> p <> 500.
(*** No prefix operator has priority 500. ***)
Hypothesis penv_Preop_not500 : forall x p, preop_priority x = Some p -> p <> 500.
(*** Prefix operators have nonzero priority. ***)
Hypothesis penv_Preop_nonzero : forall x, preop_priority x <> Some 0.
(*** Postfix and Infix operators have nonzero priority. ***)
Hypothesis penv_PostInfop_nonzero : forall x p k, postinfop_info x = Some(p,k) -> p <> 0.
(*** Prefix operators have priority less than 1000. ***)
Hypothesis penv_Preop_max : forall x p, preop_priority x = Some p -> p < 1000.
(*** Postfix and infix operators have priority less than 1000. ***)
Hypothesis penv_PostInfop_max : forall x p k, postinfop_info x = Some (p,k) -> p < 1000.

(*** These tests are used to prevent ambiguity with Sep and Rep.
 A case like {x :e X | y :e Y} should be parsed as Separation, not Replacement.
 One reason is that it would be ill-typed as Replacement.
 Note that there can also be tricky cases. Suppose C if an infix operator taking a prop and a set to a set
 and that C has priority 600. Then {x :e X C a | y :e Y} should be parsed as Replacement, not Separation.
 ***)
Definition SetInfixOp_p (a : ATree) : Prop :=
match a with (Info (InfSet _) _ _) => True | _ => False end.

Fixpoint SetInfixOpL_p (a : LTree) : Prop :=
match a with
| (Infop (InfSet _) _ _) => True
| (Paren a LNil) => SetInfixOpL_p a
| _ => False
end.

(***
 Rules for when a term is supported by environment penv.
 When this holds, the ATree can be layed out to be a corresponding LTree.
 Here it only matters that operators and binders are declared in penv, but not the specific info.
 ***)
Inductive supp : ATree -> Prop :=
| supp_Na x : nam_p x -> supp (Na x)
| supp_Nu b n m : supp (Nu b n m)
| supp_Le_U x a c : nam_p x -> supp a -> supp c -> supp (Le x None a c)
| supp_Le_T x bkd b a c : nam_p x -> supp b -> supp a -> supp c -> supp (Le x (Some (bkd,b)) a c)
| supp_Bi x mtok vl a : binder_midtok x = Some mtok
  -> (forall zl ob, In (zl,ob) vl -> forall z, In z zl -> nam_p z)
  -> (forall zl akd b, In (zl,Some(akd,b)) vl -> supp b)
  -> supp a -> supp (Bi x vl a)
| supp_Preo x p a : preop_priority x = Some p -> supp a -> supp (Preo x a)
| supp_Posto x p a : postinfop_info x = Some (p,Postfix) -> supp a -> supp (Posto x a)
| supp_Info x p k a b : postinfop_info x = Some (p,k) -> match k with Postfix => False | _ => True end
  -> supp a -> supp b -> supp (Info (InfNam x) a b)
| supp_SetInfo x a b : supp a -> supp b -> supp (Info (InfSet x) a b)
| supp_Implop a b : supp a -> supp b -> supp (Implop a b)
| supp_Sep x i a b : nam_p x -> supp a -> supp b -> supp (Sep x i a b)
| supp_Rep x i a b :
  nam_p x -> supp a
 -> ~SetInfixOp_p a (*** We insist that the a in {a|x :e b} is not of the form s :e t or s c= t. It won't be in a well-typed term since a must be of type set, not of type prop. This is essentially a very weak 'well-typedness' condition. The reason it's here is so that we can use the {...|...} notation for both Sep and Rep (and SepRep) without ambiguity. ***)
 -> supp b -> supp (Rep x i a b)
| supp_SepRep x i a b c :
  nam_p x -> supp a
 -> ~SetInfixOp_p a (*** We also insist that the a in {a|x :e b, c} is not of the form s :e t or s c= t. This potential ambiguity could be resolved by the comma before the c, but it seems like a better idea to resolve it early. ***)
  -> supp b -> supp c -> supp (SepRep x i a b c)
| supp_SetEnum cl : (forall c, In c cl -> supp c) -> supp (SetEnum cl)
| supp_MTuple a cl : supp a -> (forall c, In c cl -> supp c) -> supp (MTuple a cl)
| supp_Tuple a b cl : supp a -> supp b -> (forall c, In c cl -> supp c) -> supp (Tuple a b cl)
| supp_IfThenElse a b c : supp a -> supp b -> supp c -> supp (IfThenElse a b c)
.

Definition Binderp (a:LTree) : Prop :=
match a with
| Binder _ _ _ _ => True
| _ => False
end.

Definition dec_Binderp (a:LTree) : {Binderp a} + {~ Binderp a}.
destruct a; simpl; tauto.
Defined.

Fixpoint Binderishp (a:LTree) : bool :=
match a with
| Binder _ _ _ _ => true
| LetL _ _ _ _ => true
| IfThenElseL _ _ _ => true
| Preop x a => Binderishp a
| Infop x a b => Binderishp b
| _ => false
end.

(***
 Rules for when an LTree is supported by penv. This means it is already layed out.
 ***)
Inductive suppL : nat -> LTree -> Prop :=
| suppL_Nam q x : nam_p x -> suppL q (Nam x)
| suppL_Num q b n m : suppL q (Num b n m)
| suppL_LetL_U q x a c : q > 0
  -> nam_p x
  -> suppL 1010 a
  -> suppL 1010 c
  -> suppL q (LetL x None a c)
| suppL_LetL_T q x bkd b a c : q > 0
  -> nam_p x
  -> suppL 1010 b
  -> suppL 1010 a
  -> suppL 1010 c
  -> suppL q (LetL x (Some (bkd,b)) a c)
| suppL_Binder q x mtok vl a : q > 0 -> binder_midtok x = Some mtok
  -> (forall zl ob, In (zl,ob) vl -> forall z, In z zl -> nam_p z)
  -> (forall zl akd b, In (zl,Some(akd,b)) vl -> suppL 1010 b)
  -> suppL 1010 a -> suppL q (Binder x mtok vl a)
| suppL_Preop q x p a : preop_priority x = Some p -> p < q -> suppL (S p) a -> suppL q (Preop x a)
| suppL_Postop q x p a : postinfop_info x = Some (p,Postfix) -> p < q -> suppL (S p) a -> Binderishp a = false -> suppL q (Postop x a)
| suppL_InfixNoneop q x p a b : postinfop_info x = Some (p,InfixNone) -> p < q -> suppL p a -> suppL p b -> Binderishp a = false -> suppL q (Infop (InfNam x) a b)
| suppL_InfixLeftop q x p a b : postinfop_info x = Some (p,InfixLeft) -> p < q -> suppL (S p) a -> suppL p b -> Binderishp a = false -> suppL q (Infop (InfNam x) a b)
| suppL_InfixRightop q x p a b : postinfop_info x = Some (p,InfixRight) -> p < q -> suppL p a -> suppL (S p) b -> Binderishp a = false -> suppL q (Infop (InfNam x) a b)
| suppL_SetInfixop q x a b : 500 < q -> suppL 500 a -> suppL 500 b -> Binderishp a = false -> suppL q (Infop (InfSet x) a b)
| suppL_ImplicitInfop q a b : q > 0 -> suppL 1 a -> suppL 0 b -> Binderishp a = false -> suppL q (ImplicitInfop a b)
| suppL_Sep q x i a b : nam_p x -> suppL 500 a -> suppL 1010 b -> suppL q (SepL x i a b)
| suppL_Rep q x i a b : nam_p x -> suppL 1010 a -> ~SetInfixOpL_p a -> suppL 500 b -> suppL q (RepL x i a b)
| suppL_SepRep q x i a b c : nam_p x -> suppL 1010 a -> ~SetInfixOpL_p a -> suppL 500 b -> suppL 1010 c -> suppL q (SepRepL x i a b c)
| suppL_SetEnum q cl : suppLL cl -> suppL q (SetEnumL cl)
| suppL_MTuple q a cl : suppL 1023 a -> suppLL cl -> suppL q (MTupleL a cl)
| suppL_Paren q a bl : suppL 1023 a -> suppLL bl -> suppL q (Paren a bl)
| suppL_IfThenElseL q a b c : q > 0 -> suppL 1010 a -> suppL 1010 b -> suppL 1010 c -> suppL q (IfThenElseL a b c)
with suppLL : LTreeL -> Prop :=
| suppLL_Nil : suppLL LNil
| suppLL_Cons a bl : suppL 1023 a -> suppLL bl -> suppLL (LCons a bl)
.

Lemma suppL_0_not_Binderishp (a:LTree) : suppL 0 a -> Binderishp a = false.
Proof.
  intros H. remember 0 in H. destruct H; try omega; simpl; reflexivity.
Qed.

(***
 Relation relating ATrees to LTrees (abstract terms to a layout).
 ***)
Inductive AL : ATree -> LTree -> Prop :=
| AL_Nam x : nam_p x -> AL (Na x) (Nam x)
| AL_Num b n m : AL (Nu b n m) (Num b n m)
| AL_Let_U x a a' c c' : AL a a' -> AL c c' -> AL (Le x None a c) (LetL x None a' c')
| AL_Let_T x bkd b b' a a' c c' : AL b b' -> AL a a' -> AL c c' -> AL (Le x (Some (bkd,b)) a c) (LetL x (Some (bkd,b')) a' c')
| AL_Binder x mtok vlvl' vl vl' a a' : binder_midtok x = Some mtok
  -> (forall zl akd b', ~In (zl,None,Some(akd,b')) vlvl')
  -> (forall zl akd b, ~In (zl,Some(akd,b),None) vlvl')
  -> (forall zl akd b akd' b', In (zl,Some(akd,b),Some(akd',b')) vlvl' -> akd = akd')
  -> (forall zl akd b akd' b', In (zl,Some(akd,b),Some(akd',b')) vlvl' -> AL b b')
  -> vl = map (fun xobob' => match xobob' with (x,ob,_) => (x,ob) end) vlvl'
  -> vl' = map (fun xobob' => match xobob' with (x,_,ob') => (x,ob') end) vlvl'
  -> AL a a'
  -> AL (Bi x vl a) (Binder x mtok vl' a')
| AL_Preop x a a' : AL a a' -> AL (Preo x a) (Preop x a')
| AL_Postop x a a' : AL a a' -> AL (Posto x a) (Postop x a')
| AL_Infixop x a a' b b' : AL a a' -> AL b b' -> AL (Info x a b) (Infop x a' b')
| AL_Implicit a a' b b' : AL a a' -> AL b b' -> AL (Implop a b) (ImplicitInfop a' b')
| AL_Sep x i a a' b b' : AL a a' -> AL b b' -> AL (Sep x i a b) (SepL x i a' b')
| AL_Rep x i a a' b b' : AL a a' -> AL b b' -> AL (Rep x i a b) (RepL x i a' b')
| AL_SepRep x i a a' b b' c c' : AL a a' -> AL b b' -> AL c c' -> AL (SepRep x i a b c) (SepRepL x i a' b' c')
| AL_SetEnum cl cl' : ALL cl cl' -> AL (SetEnum cl) (SetEnumL cl')
| AL_MTuple a a' cl cl' : AL a a' -> ALL cl cl' -> AL (MTuple a cl) (MTupleL a' cl')
| AL_Tuple a a' b b' cl cl' : AL a a' -> AL b b' -> ALL cl cl' -> AL (Tuple a b cl) (Paren a' (LCons b' cl'))
| AL_Paren a a' : AL a a' -> AL a (Paren a' LNil)
| AL_IfThenElse a a' b b' c c' : AL a a' -> AL b b' -> AL c c' -> AL (IfThenElse a b c) (IfThenElseL a' b' c')
with ALL : list ATree -> LTreeL -> Prop :=
| ALL_Nil : ALL nil LNil
| ALL_Cons a a' bl bl' : AL a a' -> ALL bl bl' -> ALL (a::bl) (LCons a' bl')
.

(*** Function to erase the layout of a term (LTree) to just be the term (ATree). ***)
Fixpoint L2A (a:LTree) : ATree :=
match a with
| Nam x => Na x
| Num b n m => Nu b n m
| LetL x None a c => Le x None (L2A a) (L2A c)
| LetL x (Some (bkd,b)) a c => Le x (Some (bkd,L2A b)) (L2A a) (L2A c)
| Preop x a => Preo x (L2A a)
| Postop x a => Posto x (L2A a)
| Infop x a b => Info x (L2A a) (L2A b)
| ImplicitInfop a b => Implop (L2A a) (L2A b)
| Binder x mtok vll a => Bi x (map (fun vl => match vl with (yl,None) => (yl,None) | (yl,Some(akd,b)) => (yl,Some(akd,L2A b)) end) vll) (L2A a)
| SepL x i a b => Sep x i (L2A a) (L2A b)
| RepL x i a b => Rep x i (L2A a) (L2A b)
| SepRepL x i a b c => SepRep x i (L2A a) (L2A b) (L2A c)
| SetEnumL cl => SetEnum (LL2AL cl)
| MTupleL a cl => MTuple (L2A a) (LL2AL cl)
| Paren a LNil => L2A a
| Paren a (LCons b cl) => Tuple (L2A a) (L2A b) (LL2AL cl)
| IfThenElseL a b c => IfThenElse (L2A a) (L2A b) (L2A c)
end
with LL2AL (a:LTreeL) : list ATree :=
match a with
| LNil => nil
| LCons a b => L2A a::LL2AL b
end.

Scheme suppL_ind2 := Minimality for suppL Sort Prop
with suppLL_ind2 := Minimality for suppLL Sort Prop.

Combined Scheme suppL_mutind from suppL_ind2, suppLL_ind2.

Scheme AL_ind2 := Minimality for AL Sort Prop
with ALL_ind2 := Minimality for ALL Sort Prop.

Combined Scheme AL_mutind from AL_ind2, ALL_ind2.

Lemma SetInfixOp_p_L2A a :
SetInfixOp_p (L2A a) -> SetInfixOpL_p a.
Proof.
  induction a; simpl; try tauto.
  - destruct o; simpl; try tauto. destruct p. simpl. tauto.
  - destruct l; simpl; tauto.
Qed.

Lemma supp_L2A :
 (forall p a, suppL p a -> supp (L2A a))
 /\
 (forall al, suppLL al -> forall a, In a (LL2AL al) -> supp a).
Proof.
  apply suppL_mutind.
  - intros _ x H1. simpl. now apply supp_Na.
  - intros _ b n m. simpl. now apply supp_Nu.
  - intros q x a c Hq H1 IH1 H2 IH2. simpl. now apply supp_Le_U.
  - intros q x bkd b a c Hq Hx H1 IH1 H2 IH2 H3 IH3. simpl. now apply supp_Le_T.
  - intros q x mtok vl a Hq H1 H2 H3 IH3 H4 IH4. simpl.
     apply supp_Bi with (mtok := mtok); try assumption.
     + intros zl b H6.
        apply in_map_iff in H6. destruct H6 as [[zl' [[akd' b']|]] [H7 H8]].
        * inversion H7. subst zl'. apply (H2 zl (Some (akd',b')) H8).
        * inversion H7. subst zl'. apply (H2 zl None H8).
     + intros zl akd b H6.
        apply in_map_iff in H6. destruct H6 as [[zl' [[akd' b']|]] [H7 H8]].
        * inversion H7. subst zl'. subst akd'. apply (IH3 zl akd b' H8).
        * discriminate H7.
  - intros q x p a Hx Hpq H1 IH1. simpl. now apply (supp_Preo x p).
  - intros q x p a Hx Hpq H1 IH1 Hnb. simpl. now apply (supp_Posto x p).
  - intros q x p a b Hx Hpq H1 IH1 H2 IH2 Hnb. simpl. now apply (supp_Info x p InfixNone).
  - intros q x p a b Hx Hpq H1 IH1 H2 IH2 Hnb. simpl. now apply (supp_Info x p InfixLeft).
  - intros q x p a b Hx Hpq H1 IH1 H2 IH2 Hnb. simpl. now apply (supp_Info x p InfixRight).
  - intros q x a b Hq H1 IH1 H2 IH2 NBa. simpl. now apply supp_SetInfo.
  - intros q a b Hq H1 IH1 H2 IH2 Hnb. simpl. now apply supp_Implop.
  - intros _ x i a b Hx H1 IH1 H2 IH2. simpl. now apply supp_Sep.
  - intros _ x i a b Hx H1 IH1 K1 H2 IH2. simpl. apply supp_Rep; try assumption.
    intros K2. apply K1. now apply SetInfixOp_p_L2A.
  - intros _ x i a b c Hx H1 IH1 K1 H2 IH2 H3 IH3. simpl. apply supp_SepRep; try assumption.
    intros K2. apply K1. now apply SetInfixOp_p_L2A.
  - intros _ cl H1 IH1. simpl. now apply supp_SetEnum.
  - intros _ a cl H1 IH1 H2 IH2. simpl. now apply supp_MTuple.
  - intros _ a bl H1 IH1 H2 IH2. simpl. destruct bl as [|b bl].
     + assumption.
     + inversion H2. apply supp_Tuple.
        * assumption.
        * apply IH2. simpl. left. reflexivity.
        * intros c H5. apply IH2. simpl. right. assumption.
  - intros q a b c Hq H1 IH1 H2 IH2 H3 IH3. simpl. now apply supp_IfThenElse. 
  - intros a H1. contradiction H1.
  - intros a bl H1 IH1 H2 IH2 c H3. simpl in H3. destruct H3 as [H3|H3].
     + subst c. assumption.
     + now apply IH2.
Qed.

Lemma suppL_leq p a :
 suppL p a -> forall q, p <= q -> suppL q a.
Proof.
  intros H. induction H.
  - intros p' K'. now apply suppL_Nam.
  - intros p' K'. now apply suppL_Num.
  - intros q' Hq. apply suppL_LetL_U; try assumption. omega.
  - intros q' Hq. apply suppL_LetL_T; try assumption. omega.
  - intros p' K'. apply suppL_Binder with (mtok := mtok); try assumption. omega.
  - intros p' K'. apply (suppL_Preop p' x p); try assumption. omega.
  - intros p' K'. apply (suppL_Postop p' x p); try assumption. omega.
  - intros p' K'. apply (suppL_InfixNoneop p' x p); try assumption. omega.
  - intros p' K'. apply (suppL_InfixLeftop p' x p); try assumption. omega.
  - intros p' K'. apply (suppL_InfixRightop p' x p); try assumption. omega.
  - intros p' K'. apply suppL_SetInfixop; try assumption. omega.
  - intros p' K'. apply (suppL_ImplicitInfop p'); try assumption. omega.
  - intros q' Hq'. apply suppL_Sep; try assumption.
  - intros q' Hq'. apply suppL_Rep; try assumption.
  - intros q' Hq'. apply suppL_SepRep; try assumption.
  - intros q' Hq'. now apply suppL_SetEnum.
  - intros q' Hq'. now apply suppL_MTuple.
  - intros p' K'. apply suppL_Paren.
     + apply IHsuppL. omega.
     + assumption.
  - intros q' Hq'. apply suppL_IfThenElseL; try assumption. omega.
Qed.

Lemma AL_L2A :
 (forall p a, suppL p a -> AL (L2A a) a)
 /\
 (forall al, suppLL al -> ALL (LL2AL al) al).
Proof.
  apply suppL_mutind.
  - intros _ x Hx. simpl. now apply AL_Nam.
  - intros _ b n m. simpl. apply AL_Num.
  - intros q x a c Hq H1 IH1 H2 IH2. simpl. now apply AL_Let_U.
  - intros q x bkd b a c Hq Hx H1 IH1 H2 IH2 H3 IH3. simpl. now apply AL_Let_T.
  - intros q x mtok vll a Hq Hx H0 H1 IH1 H2 IH2. simpl.
     apply (AL_Binder x mtok
             (map
               (fun vl : list string * option (AscKind * LTree) =>
                 let (yl, y) := vl in
                   match y with
                     | Some (akd,b) => (yl, Some (akd,L2A b), y)
                     | None => (yl, None, y)
                   end) vll)).
     + assumption.
     + intros zl akd' b' H3. apply in_map_iff in H3. destruct H3 as [[yl [[ckd c]|]] [H4 H5]]; discriminate H4.
     + intros zl akd' b' H3. apply in_map_iff in H3. destruct H3 as [[yl [[ckd c]|]] [H4 H5]]; discriminate H4.
     + intros zl akd' b' ckd' c' H3. apply in_map_iff in H3. destruct H3 as [[yl [[ckd c]|]] [H4 H5]].
        * inversion H4. reflexivity.
        * discriminate H4.
     + intros zl akd' b' ckd' c' H3. apply in_map_iff in H3. destruct H3 as [[yl [[ckd c]|]] [H4 H5]].
        * inversion H4. apply (IH1 yl ckd). subst c'. assumption.
        * discriminate H4.
     + rewrite map_map. apply map_ext. intros [yl [[ckd c]|]]; reflexivity.
     + rewrite map_map. rewrite <- (map_id vll) at 1. apply map_ext. intros [yl [[ckd c]|]]; reflexivity.
     + assumption.
  - intros q x p a Hx Hpq H1 IH1. simpl. now apply AL_Preop.
  - intros q x p a Hx Hpq H1 IH1 Hnb. simpl. now apply AL_Postop.
  - intros q x p a b Hx Hpq H1 IH1 H2 IH2 Hnb. simpl. now apply AL_Infixop.
  - intros q x p a b Hx Hpq H1 IH1 H2 IH2 Hnb. simpl. now apply AL_Infixop.
  - intros q x p a b Hx Hpq H1 IH1 H2 IH2 Hnb. simpl. now apply AL_Infixop.
  - intros q x a b Hq H1 IH1 H2 IH2 NBa. simpl. now apply AL_Infixop.
  - intros q a b Hq H1 IH1 H2 IH2 Hnb. simpl. now apply AL_Implicit.
  - intros _ x i a b Hx H1 IH1 H2 IH2. simpl. now apply AL_Sep.
  - intros _ x i a b Hx H1 IH1 H2 IH2. simpl. now apply AL_Rep.
  - intros _ x i a b c Hx H1 IH1 H2 IH2 H3 IH3. simpl. now apply AL_SepRep.
  - intros _ cl H1 IH1. simpl. now apply AL_SetEnum.
  - intros _ a cl H1 IH1 H2 IH2. simpl. now apply AL_MTuple.
  - intros q a bl H1 IH1 H2 IH2. simpl. destruct bl as [|b cl].
     + now apply AL_Paren.
     + simpl in IH2. inversion IH2. now apply AL_Tuple.
  - intros q a b c Hq H1 IH1 H2 IH2 H3 IH3. simpl. now apply AL_IfThenElse.
  - simpl. apply ALL_Nil.
  - intros a bl H1 IH1 H2 IH2. simpl. now apply ALL_Cons.
Qed.        

(***
 AL_A2L*:
 Every supported ATree can be layed out as a supported LTree (for any given priority p).
 I found it difficult to write this as a function in Coq,
 so I've only proven existence. The function is implicit in the proof.
 The lemmas and proofs are also more complicated than necessary because I want to mimic the intended algorithm.
 ***)
(***
 If we have a layout a' for a supported at p, then we also have one supported at q.
 This may require putting in parentheses.
 ***)
Lemma AL_A2L_aux p q a : p <= 1023 -> (exists a', suppL p a' /\ AL a a') -> exists a', suppL q a' /\ AL a a'.
Proof.
  intros H [a' [H1 H2]].
  destruct (le_gt_dec p q) as [Hpq|Hpq].
  - (*** No New Parens ***)
     exists a'. split; try assumption. revert Hpq. now apply suppL_leq.
  - (*** Parens ***)
     exists (Paren a' LNil). split.
     + apply suppL_Paren.
        * revert H. now apply suppL_leq.
        * apply suppLL_Nil.
     + now apply AL_Paren.
Qed.

(*** ALL_A2L would correspond to an auxiliary function taking a list of ATrees to an LTreeL. ***)
Lemma ALL_A2L (cl : list ATree) :
   (forall c : ATree, In c cl -> supp c) ->
   (forall c : ATree,
    In c cl ->
    exists p : nat, p <= 1023 /\ (exists a' : LTree, suppL p a' /\ AL c a')) ->
   exists cl' : LTreeL, suppLL cl' /\ ALL cl cl'.
Proof.
 induction cl.
       - intros H1 H2. exists LNil. split.
          + apply suppLL_Nil.
          + apply ALL_Nil.
       - intros H1 H2.
          assert (La:exists p, p <= 1023 /\ exists a', suppL p a' /\ AL a a').
          {
            apply H2. left. reflexivity.
          }
          assert (L2:forall c : ATree, In c cl -> supp c).
          {
            intros c H3. apply H1. now right.
          }
          assert (L3:forall c : ATree, In c cl -> exists p : nat, p <= 1023 /\ exists a' : LTree, suppL p a' /\ AL c a').
          {
            intros c H3. apply H2. now right.
          }
          destruct La as [p' [Hp' [a' [Ha1 Ha2]]]].
          destruct (IHcl L2 L3) as [cl' [Hc1 Hc2]].
          exists (LCons a' cl'). split.
          + apply suppLL_Cons; try assumption. apply (suppL_leq p'); try assumption.
          + now apply ALL_Cons.
Qed.

Lemma AL_SetInfixOp_p a a' :
  AL a a' -> SetInfixOpL_p a' -> SetInfixOp_p a.
Proof.
  intros H. induction H; simpl; try tauto.
Qed.

(***
 Every supported a can be layed out as a corresponding a' supported by some p <= 1023.
 This is the meat of the algorithm.
 ***)
Lemma AL_A2L_exp a : supp a -> exists p, p <= 1023 /\ exists a', suppL p a' /\ AL a a'.
Proof.
  intros H. induction H.
  - (*** Nam ***)
     exists 0. (*** return priority 0 ***) split; try omega.
     exists (Nam x). (*** return as layout ***) split. 
     + now apply suppL_Nam.
     + now apply AL_Nam.
  - (*** Num return priority 0 and Num ***)
     exists 0. split; try omega.
     exists (Num b n m). split.
     + now apply suppL_Num.
     + now apply AL_Num.
  - assert (L2:exists a', suppL 1010 a' /\ AL a a').
     {
       destruct IHsupp1 as [p' [Hp' Ha]].
       apply (AL_A2L_aux p'); try assumption.
     }
     destruct L2 as [a' [L2a L2b]].
     assert (L3:exists c', suppL 1010 c' /\ AL c c').
     {
       destruct IHsupp2 as [p' [Hp' Hc]].
       apply (AL_A2L_aux p'); try assumption.
     }
     destruct L3 as [c' [L3a L3b]].
     exists 1. split.
     + omega.
     + exists (LetL x None a' c'). split.
        * apply suppL_LetL_U; try assumption. omega.
        * now apply AL_Let_U.
  - assert (L1:exists b', suppL 1010 b' /\ AL b b').
     {
       destruct IHsupp1 as [p' [Hp' Hb]].
       apply (AL_A2L_aux p'); try assumption.
     }
     destruct L1 as [b' [L1a L1b]].
     assert (L2:exists a', suppL 1010 a' /\ AL a a').
     {
       destruct IHsupp2 as [p' [Hp' Ha]].
       apply (AL_A2L_aux p'); try assumption.
     }
     destruct L2 as [a' [L2a L2b]].
     assert (L3:exists c', suppL 1010 c' /\ AL c c').
     {
       destruct IHsupp3 as [p' [Hp' Hc]].
       apply (AL_A2L_aux p'); try assumption.
     }
     destruct L3 as [c' [L3a L3b]].
     exists 1. split.
     + omega.
     + exists (LetL x (Some (bkd,b')) a' c'). split.
        * apply suppL_LetL_T; try assumption. omega.
        * now apply AL_Let_T.
  - (** Binder -- this also would apparently need an auxiliary function. **)
     assert (L1:exists vlvl' : list (list string * option (AscKind * ATree) * option (AscKind * LTree)),
                exists vll' : list (list string * option (AscKind * LTree)),
                (forall (zl : list string) (bkd : AscKind) (b : LTree),
                 In (zl, Some (bkd,b)) vll' -> suppL 1010 b)
                /\
                (forall (zl : list string) (bkd' : AscKind) (b' : LTree), ~ In (zl, None, Some (bkd',b')) vlvl')
                /\
                (forall (zl : list string) (bkd : AscKind) (b : ATree), ~ In (zl, Some (bkd,b), None) vlvl')
                /\
                (forall (zl : list string) (bkd : AscKind) (b : ATree) (bkd' : AscKind) (b' : LTree), In (zl, Some (bkd,b), Some (bkd',b')) vlvl' -> bkd = bkd' /\ AL b b')
                /\
                (vl =
                  map
                  (fun xobob' : list string * option (AscKind * ATree) * option (AscKind * LTree) =>
                    let (y, _) := xobob' in let (x0, ob) := y in (x0, ob)) vlvl')
                /\
                (vll' =
                  map
                  (fun xobob' : list string * option (AscKind * ATree) * option (AscKind * LTree) =>
                    let (y, ob') := xobob' in let (x0, _) := y in (x0, ob')) vlvl')).
     {
       revert H0 H1 H2. clear. induction vl.
       - intros H0 H1 H2. exists nil. exists nil. repeat split; simpl; try tauto; simpl in H; tauto.
       - intros H0 H1 H2.
          assert (Lc:forall (zl : list string) (ob : option (AscKind * ATree)), In (zl, ob) vl -> forall z, In z zl -> nam_p z).
          {
            intros zl ob H3 z H4. apply (H0 zl ob).
            - now right.
            - assumption.
          }
          assert (Ld:forall (zl : list string) (bkd : AscKind) (b : ATree), In (zl, Some (bkd,b)) vl -> supp b).
          {
            intros zl bkd b H3. apply (H1 zl bkd). now right.
          }
          assert (Le:forall (zl : list string) (bkd : AscKind) (b : ATree), In (zl, Some (bkd,b)) vl -> exists (p : nat), p <= 1023 /\ exists (a' : LTree), suppL p a' /\ AL b a').
          {
            intros zl bkd b H3. apply (H2 zl bkd). now right.
          }
          destruct (IHvl Lc Ld Le) as [vlvl' [vll' [Hv1 [Hv2 [Hv3 [Hv4 [Hv5 Hv6]]]]]]].
          destruct a as [zl [[bkd b]|]].
          + assert (La:supp b).
             {
               apply (H1 zl bkd). now left.
             }
             assert (Lb:exists (a' : LTree), suppL 1010 a' /\ AL b a').
             {
                destruct (H2 zl bkd b) as [p' [K1 [a' [K2 K3]]]].
                - now left.
                - apply (AL_A2L_aux p'); try omega. exists a'. tauto.
             }
             destruct Lb as [b' [Hb1 Hb2]].
             exists ((zl,Some (bkd,b),Some (bkd,b'))::vlvl'). exists ((zl,Some (bkd,b'))::vll'). repeat split.
             * { intros yl ckd c [H3|H3].
                  - inversion H3. subst c. assumption.
                  - apply Hv1 with (zl := yl) (bkd := ckd); try assumption.
                }
             * { intros yl ckd c [H3|H3].
                  - discriminate H3.
                  - revert H3. apply Hv2.
                }
             * { intros yl ckd c [H3|H3].
                  - discriminate H3.
                  - revert H3. apply Hv3.
                }
             * { destruct H as [H3|H3].
                  - inversion H3. reflexivity.
                  - generalize (Hv4 _ _ _ _ _ H3). tauto.
                }
             * { destruct H as [H3|H3].
                  - inversion H3. congruence.
                  - generalize (Hv4 _ _ _ _ _ H3). tauto.
                }
             * simpl. f_equal. exact Hv5.
             * simpl. f_equal. exact Hv6.
          + exists ((zl,None,None)::vlvl'). exists ((zl,None)::vll'). repeat split.
             * { intros yl bkd b [H3|H3].
                  - discriminate H3.
                  - now apply Hv1 with (zl := yl) (bkd := bkd).
                }
             * { intros yl bkd b [H3|H3].
                  - discriminate H3.
                  - revert H3. apply Hv2.
                }
             * { intros yl bkd b [H3|H3].
                  - discriminate H3.
                  - revert H3. apply Hv3.
                }
             * { destruct H as [H3|H3].
                  - discriminate H3.
                  - generalize (Hv4 _ _ _ _ _ H3). tauto.
                }
             * { destruct H as [H3|H3].
                  - discriminate H3.
                  - generalize (Hv4 _ _ _ _ _ H3). tauto.
                }
             * simpl. f_equal. exact Hv5.
             * simpl. f_equal. exact Hv6.
     }
     assert (L2:exists a', suppL 1010 a' /\ AL a a').
     {
       destruct IHsupp as [p' [Hp' Ha]].
       apply (AL_A2L_aux p'); try assumption.
     }
     destruct L2 as [a' [Ha1 Ha2]].
     destruct L1 as [vlvl' [vll' [Lv1 [Lv2 [Lv3 [Lv4 [Lv5 Lv6]]]]]]].
     (*** return priority 1 and (Binder x mtok vll' a') ***)
     exists 1. split; try omega.
     exists (Binder x mtok vll' a'). split.
     + apply suppL_Binder with (mtok := mtok); try assumption; try omega.
        intros zl ob K1.
        rewrite Lv6 in K1. apply in_map_iff in K1. destruct K1 as [[[yl ao] ao'] [K2 K3]].
        inversion K2. subst ao'. destruct ao as [[bkd b]|]; destruct ob as [[bkd' b']|].
        * { generalize (Lv4 yl bkd b bkd' b' K3). intros K4.
             apply (H0 zl (Some (bkd,b))). rewrite Lv5. apply in_map_iff. exists (yl,Some (bkd,b),Some (bkd',b')).
             split.
             - subst zl. reflexivity.
             - assumption.
           }
        * exfalso. now apply (Lv3 yl bkd b).
        * exfalso. now apply (Lv2 yl bkd' b').
        * apply (H0 zl None). rewrite Lv5. apply in_map_iff. exists (yl,None,None).
             split; try assumption. subst zl. reflexivity.
     + apply AL_Binder with (mtok := mtok) (vlvl' := vlvl'); try tauto.
        * intros zl bkd b bkd' b'. generalize (Lv4 zl bkd b bkd' b'). tauto.
        * intros zl bkd b bkd' b'. generalize (Lv4 zl bkd b bkd' b'). tauto.
  - destruct IHsupp as [q [Hq Ha]].
     destruct (AL_A2L_aux q (S p) a) as [a' [Ha1 Ha2]]; try assumption.
     (*** Return S p and (Preop x a') ***)
     exists (S p). split.
     + generalize (penv_Preop_max x p H). omega.
     + exists (Preop x a'). split.
        * apply (suppL_Preop (S p) x p); try assumption. omega.
        * now apply AL_Preop.
  - destruct IHsupp as [q [Hq Ha]].
     destruct (AL_A2L_aux q (S p) a) as [a' [Ha1 Ha2]]; try assumption. (*** Recursive Call + Add Parens if needed. ***)
     (*** return (S p) and either (Postop x a') or (Postop x (Paren a' [])) depending on whether or not a' is a binder. ***)
     exists (S p). split.
     + generalize (penv_PostInfop_max x p _ H). omega.
     + case_eq (Binderishp a'); intros E. (*** Two cases: a' is a binderish or not. If it's binderish, we need parens. ***)
        * { exists (Postop x (Paren a' LNil)). split.
             - apply (suppL_Postop (S p) x p); try assumption.
                + omega.
                + apply suppL_Paren.
                   * apply (suppL_leq (S p)); try assumption.
                      generalize (penv_PostInfop_max x p _ H). omega.
                   * apply suppLL_Nil.
                + simpl. tauto.
             - apply AL_Postop. now apply AL_Paren.
           }
        * { exists (Postop x a'). split.
             - apply (suppL_Postop (S p) x p); try assumption.
                omega.
             - now apply AL_Postop.
           }
  - destruct IHsupp1 as [qa [Hqa Ha]]. destruct IHsupp2 as [qb [Hqb Hb]]. (*** Recursive Calls ***)
     destruct k; try contradiction H0. (*** Split into the three cases ***)
     + (*** InfixNone ***)
        destruct (AL_A2L_aux qa p a) as [a' [Ha1 Ha2]]; try assumption. (*** Add Parens if needed. ***)
        destruct (AL_A2L_aux qb p b) as [b' [Hb1 Hb2]]; try assumption. (*** Add Parens if needed. ***)
        (*** Return (S p) and either (Infop x a' b') or (Infop x (Paren a' []) b') depending on whether or not a' is a binder. ***)
        exists (S p). split.
        * generalize (penv_PostInfop_max x p _ H). omega.
        * { case_eq (Binderishp a'); intros E. (*** Two cases: a' is a binderish or not. If it's binderish, we need parens. ***)
          - exists (Infop (InfNam x) (Paren a' LNil) b'). split.
             + apply (suppL_InfixNoneop (S p) x p); try assumption.
                * omega.
                * { apply suppL_Paren.
                   - apply (suppL_leq p); try assumption.
                      generalize (penv_PostInfop_max x p _ H). omega.
                   - apply suppLL_Nil.
                   }
                * simpl. tauto.
             + apply AL_Infixop; try assumption. now apply AL_Paren.
          - exists (Infop (InfNam x) a' b'). split.
             + apply (suppL_InfixNoneop (S p) x p); try assumption.
                omega.
             + now apply AL_Infixop.
           }
     + (*** InfixLeft ***)
        destruct (AL_A2L_aux qa (S p) a) as [a' [Ha1 Ha2]]; try assumption. (*** Add Parens if needed. ***)
        destruct (AL_A2L_aux qb p b) as [b' [Hb1 Hb2]]; try assumption. (*** Add Parens if needed. ***)
        (*** Return (S p) and either (Infop x a' b') or (Infop x (Paren a' []) b') depending on whether or not a' is a binder. ***)
        exists (S p). split.
        * generalize (penv_PostInfop_max x p _ H). omega.
        * { case_eq (Binderishp a'); intros E. (*** Two cases: a' is a binderish or not. If it's binderish, we need parens. ***)
          - exists (Infop (InfNam x) (Paren a' LNil) b'). split.
             + apply (suppL_InfixLeftop (S p) x p); try assumption.
                * omega.
                * { apply suppL_Paren.
                   - apply (suppL_leq (S p)); try assumption.
                      generalize (penv_PostInfop_max x p _ H). omega.
                   - apply suppLL_Nil.
                   }
                * simpl. tauto.
             + apply AL_Infixop; try assumption. now apply AL_Paren.
          - exists (Infop (InfNam x) a' b'). split.
             + apply (suppL_InfixLeftop (S p) x p); try assumption.
                omega.
             + now apply AL_Infixop.
           }
     + (*** InfixRight ***)
        destruct (AL_A2L_aux qa p a) as [a' [Ha1 Ha2]]; try assumption. (*** Add Parens if needed. ***)
        destruct (AL_A2L_aux qb (S p) b) as [b' [Hb1 Hb2]]; try assumption. (*** Add Parens if needed. ***)
        (*** Return (S p) and either (Infop x a' b') or (Infop x (Paren a' []) b') depending on whether or not a' is a binder. ***)
        exists (S p). split.
        * generalize (penv_PostInfop_max x p _ H). omega.
        * { case_eq (Binderishp a'); intros E. (*** Two cases: a' is a binderish or not. If it's binderish, we need parens. ***)
          - exists (Infop (InfNam x) (Paren a' LNil) b'). split.
             + apply (suppL_InfixRightop (S p) x p); try assumption.
                * omega.
                * { apply suppL_Paren.
                   - apply (suppL_leq p); try assumption.
                      generalize (penv_PostInfop_max x p _ H). omega.
                   - apply suppLL_Nil.
                   }
                * simpl. tauto.
             + apply AL_Infixop; try assumption. now apply AL_Paren.
          - exists (Infop (InfNam x) a' b'). split.
             + apply (suppL_InfixRightop (S p) x p); try assumption.
                omega.
             + now apply AL_Infixop.
           }
  - destruct IHsupp1 as [qa [Hqa Ha]]. destruct IHsupp2 as [qb [Hqb Hb]]. (*** Recursive Calls ***) (*** Set Infix ***)
     destruct (AL_A2L_aux qa 500 a) as [a' [Ha1 Ha2]]; try assumption. (*** Add Parens if needed. ***)
     destruct (AL_A2L_aux qb 500 b) as [b' [Hb1 Hb2]]; try assumption. (*** Add Parens if needed. ***)
     exists 501. split; try omega.
     case_eq (Binderishp a'); intros E. (*** Two cases: a' is a binderish or not. If it's binderish, we need parens. ***)
     + exists (Infop (InfSet x) (Paren a' LNil) b'). split.
        * { apply suppL_SetInfixop; try assumption.
             - omega.
             - apply suppL_Paren.
                + apply (suppL_leq 500); try assumption. omega.
                + apply suppLL_Nil.
             - simpl. reflexivity.
           }
        * apply AL_Infixop; try assumption. apply AL_Paren. assumption.
     + exists (Infop (InfSet x) a' b'). split.
        * apply suppL_SetInfixop; try assumption. omega.
        * apply AL_Infixop; try assumption.
  - (*** Implicit Binary Operator (application) ***)
     destruct IHsupp1 as [qa [Hqa Ha]]. destruct IHsupp2 as [qb [Hqb Hb]]. (*** Recursive Calls ***)
     destruct (AL_A2L_aux qa 1 a) as [a' [Ha1 Ha2]]; try assumption. (*** Add Parens if needed. ***)
     destruct (AL_A2L_aux qb 0 b) as [b' [Hb1 Hb2]]; try assumption. (*** Add Parens if needed. ***)
     (*** Return 1 and either (ImplicitInfop a' b') or (ImplicitInfop (Paren a' []) b') depending on whether or not a' is a binder. ***)
        exists 1. split.
        * omega.
        * { case_eq (Binderishp a'); intros E. (*** Two cases: a' is a binderish or not. If it's binderish, we need parens. ***)
          - exists (ImplicitInfop (Paren a' LNil) b'). split.
             + apply suppL_ImplicitInfop; try assumption.
                * omega.
                * { apply suppL_Paren.
                   - apply (suppL_leq 1); try assumption. omega.
                   - apply suppLL_Nil.
                   }
                * simpl. tauto.
             + apply AL_Implicit; try assumption. now apply AL_Paren.
          - exists (ImplicitInfop a' b'). split.
             + apply suppL_ImplicitInfop; try assumption.
                omega.
             + now apply AL_Implicit.
           }
  - (*** Sep ***)
     destruct IHsupp1 as [qa [Hqa Ha]]. destruct IHsupp2 as [qb [Hqb Hb]]. (*** Recursive Calls ***)
     destruct (AL_A2L_aux qa 500 a) as [a' [Ha1 Ha2]]; try assumption. (*** Add Parens if needed. ***)
     destruct (AL_A2L_aux qb 1010 b) as [b' [Hb1 Hb2]]; try assumption. (*** Add Parens if needed. ***)
     exists 0. split; try omega.
     exists (SepL x i a' b').
     split.
     + now apply suppL_Sep.
     + now apply AL_Sep.
  - (*** Rep ***)
     destruct IHsupp1 as [qa [Hqa Ha]]. destruct IHsupp2 as [qb [Hqb Hb]]. (*** Recursive Calls ***)
     destruct (AL_A2L_aux qa 1010 a) as [a' [Ha1 Ha2]]; try assumption. (*** Add Parens if needed. ***)
     destruct (AL_A2L_aux qb 500 b) as [b' [Hb1 Hb2]]; try assumption. (*** Add Parens if needed. ***)
     exists 0. split; try omega.
     exists (RepL x i a' b').
     split.
     + apply suppL_Rep; try assumption. intros K1. apply H1. revert Ha2 K1.
        apply AL_SetInfixOp_p.
     + now apply AL_Rep.
  - (*** SepRep ***)
     destruct IHsupp1 as [qa [Hqa Ha]]. destruct IHsupp2 as [qb [Hqb Hb]]. destruct IHsupp3 as [qc [Hqc Hc]]. (*** Recursive Calls ***)
     destruct (AL_A2L_aux qa 1010 a) as [a' [Ha1 Ha2]]; try assumption. (*** Add Parens if needed. ***)
     destruct (AL_A2L_aux qb 500 b) as [b' [Hb1 Hb2]]; try assumption. (*** Add Parens if needed. ***)
     destruct (AL_A2L_aux qc 1010 c) as [c' [Hc1 Hc2]]; try assumption. (*** Add Parens if needed. ***)
     exists 0. split; try omega.
     exists (SepRepL x i a' b' c').
     split.
     + apply suppL_SepRep; try assumption. intros K1. apply H1. revert Ha2 K1.
        apply AL_SetInfixOp_p.
     + now apply AL_SepRep.
  - (*** SetEnum ***)
     assert (L1:exists cl', suppLL cl' /\ ALL cl cl').
     {
       apply ALL_A2L; try assumption.
     }
     destruct L1 as [cl' [Hcl1 Hcl2]].
     exists 0. split; try omega.
     exists (SetEnumL cl'). split.
     + now apply suppL_SetEnum.
     + now apply AL_SetEnum.
  - (*** MTuple ***)
     destruct IHsupp as [qa [Hqa [a' [Ha1 Ha2]]]].
     assert (L1:exists cl', suppLL cl' /\ ALL cl cl').
     {
       apply ALL_A2L; try assumption.
     }
     destruct L1 as [cl' [Hcl1 Hcl2]].
     exists 0. split; try omega.
     exists (MTupleL a' cl'). split.
     + apply suppL_MTuple; try assumption. apply (suppL_leq qa); try assumption.
     + now apply AL_MTuple.
  - (*** Tuple ***)
     destruct IHsupp1 as [qa [Hqa [a' [Ha1 Ha2]]]]. destruct IHsupp2 as [qb [Hqb [b' [Hb1 Hb2]]]]. (*** First two Recursive Calls; no need to add parens here. ***)
     assert (L1:exists cl', suppLL cl' /\ ALL cl cl').
     {
       apply ALL_A2L; try assumption.
     }
     destruct L1 as [cl' [Hcl1 Hcl2]].
     (*** return 0 and (Paren a' (b'::cl')) ***)
     exists 0. split; try omega.
     exists (Paren a' (LCons b' cl')).
     split.
     + apply suppL_Paren.
        * apply (suppL_leq qa); try assumption.
        * apply suppLL_Cons; try assumption. apply (suppL_leq qb); try assumption.
     + apply AL_Tuple; try assumption.
  - assert (L1:exists a', suppL 1010 a' /\ AL a a').
     {
       destruct IHsupp1 as [p [IHa IHb]]. now apply AL_A2L_aux with (p := p).
     }
     assert (L2:exists b', suppL 1010 b' /\ AL b b').
     {
       destruct IHsupp2 as [p [IHa IHb]]. now apply AL_A2L_aux with (p := p).
     }
     assert (L3:exists c', suppL 1010 c' /\ AL c c').
     {
       destruct IHsupp3 as [p [IHa IHb]]. now apply AL_A2L_aux with (p := p).
     }
     (*** return priority 1 and (IfThenElseL a' b' c') ***)
     exists 1. split.
     + omega. 
     + destruct L1 as [a' [L1' L1'']]. destruct L2 as [b' [L2' L2'']]. destruct L3 as [c' [L3' L3'']].
        exists (IfThenElseL a' b' c'). split.
        * apply suppL_IfThenElseL; try assumption. omega.
        * now apply AL_IfThenElse.
Qed.

(*** Given a supported a and p <= 1023, there is a corresponding layout a'. ***)
Lemma AL_A2L_allp a : supp a -> forall p, p <= 1023 -> exists a', suppL p a' /\ AL a a'.
Proof.
  intros H p Hp. destruct (AL_A2L_exp a H) as [p' [Hp' Ha']].
  apply (AL_A2L_aux p'); try assumption.
Qed.

(*** Each layout corresponds to at most one ATree. ***)
Lemma AL_inj :
 (forall a1 a', AL a1 a' -> forall a2, AL a2 a' -> a1 = a2)
 /\
 (forall al1 al', ALL al1 al' -> forall al2, ALL al2 al' -> al1 = al2).
Proof.
  apply AL_mutind.
  - intros x Hx a2 K. inversion K. reflexivity.
  - intros b n m a2 K. inversion K. reflexivity.
  - intros x a a' c c' H1 IH1 H2 IH2 a2 K. inversion K. f_equal.
    + now apply IH1.
    + now apply IH2.
  - intros x bkd b b' a a' c c' H1 IH1 H2 IH2 H3 IH3 a2 K. inversion K. f_equal.
     + f_equal. f_equal. now apply IH1.
     + now apply IH2.
     + now apply IH3.
  - intros x mtok vlvl' vl vl' a1 a' Hx H2 H3 H4 H5 IH5 H6 H7 H8 IH8 a2 K.
     inversion K.
     apply IH8 in H18. subst a1. f_equal. subst.
     clear K.
     revert vlvl'0 H2 H3 H4 H5 IH5 H11 H12 H13 H15 H17.
     clear.
     induction vlvl' as [|[[zl oa] ob] vlvl' IHvlvl']; simpl.
     + intros vlvl' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10. destruct vlvl'; try discriminate H10.
        simpl. reflexivity.
     + intros vlvl'' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10. destruct vlvl''; try discriminate H10.
        destruct p as [[zl' oa'] ob']. simpl in H1.
        simpl in H10. simpl. inversion H10. subst zl'. subst ob'.
        simpl. f_equal.
        * { f_equal. destruct oa as [[akd a]|]; destruct ob as [[bkd b]|].
             - destruct oa' as [[akd' a']|].
                + assert (L1:In (zl, Some (akd',a'), Some (bkd,b)) ((zl, Some (akd',a'), Some (bkd,b)) :: vlvl'')) by now left.
                   generalize (H8 zl akd' a' bkd b L1). intros L2. subst akd'.
                   assert (L3:(zl, Some (akd,a), Some (bkd,b)) = (zl, Some (akd,a), Some (bkd,b)) \/ In (zl, Some (akd,a), Some (bkd,b)) vlvl') by now left.
                   generalize (H3 zl akd a bkd b L3). intros L4.
                   subst akd. f_equal. f_equal. 
                   apply (H5 zl bkd a bkd b).
                   * exact L3.
                   * apply (H9 zl bkd a' bkd b L1).
                + exfalso. apply (H6 zl bkd b). simpl. tauto.
             - exfalso. generalize (H2 zl akd a). tauto.
             - exfalso. apply (H1 zl bkd b). tauto.
             - destruct oa' as [[akd' a']|]; try reflexivity.
                exfalso. apply (H7 zl akd' a'). left. reflexivity.
           }
        * { apply IHvlvl'; try assumption.
             - intros wl dkd d K. apply (H1 wl dkd d). now right.
             - intros wl dkd d K. apply (H2 wl dkd d). now right.
             - intros wl dkd d ekd e K. apply (H3 wl dkd d ekd e). now right.
             - intros wl dkd d ekd e K. apply (H4 wl dkd d ekd e). now right.
             - intros wl dkd d ekd e K. apply (H5 wl dkd d ekd e). now right.
             - intros wl dkd d K. apply (H6 wl dkd d). now right.
             - intros wl dkd d K1. apply (H7 wl dkd d). now right.
             - intros wl dkd d ekd e K. apply (H8 wl dkd d ekd e). now right.
             - intros wl dkd d ekd e K. apply (H9 wl dkd d ekd e). now right.
           }
  - intros x a a' H1 IH1 a2 K. inversion K. subst. now rewrite (IH1 a0 H2).
  - intros x a a' H1 IH1 a2 K. inversion K. subst. now rewrite (IH1 a0 H2).
  - intros x a a' b b' H1 IH1 H2 IH2 a2 K. inversion K. subst. rewrite (IH1 a0 H4). now rewrite (IH2 b0 H6).
  - intros a a' b b' H1 IH1 H2 IH2 a2 K. inversion K. f_equal.
     + now apply IH1.
     + now apply IH2.
  - intros x i a a' b b' H1 IH1 H2 IH2 a2 K. inversion K. f_equal.
     + now apply IH1.
     + now apply IH2.
  - intros x i a a' b b' H1 IH1 H2 IH2 a2 K. inversion K. f_equal.
     + now apply IH1.
     + now apply IH2.
  - intros x i a a' b b' c c' H1 IH1 H2 IH2 H3 IH3 a2 K. inversion K. f_equal.
     + now apply IH1.
     + now apply IH2.
     + now apply IH3.
  - intros cl cl' H1 IH1 a2 K. inversion K. f_equal. now apply IH1.
  - intros a a' cl cl' H1 IH1 H2 IH2 a2 K. inversion K. f_equal.
     + now apply IH1.
     + now apply IH2.
  - intros a a' b b' cl cl' H1 IH1 H2 IH2 H3 IH3 a2 K. inversion K. subst.
     rewrite (IH1 a0 H6). rewrite (IH2 b0 H7). now rewrite (IH3 cl0 H8).
  - intros a a' H1 IH1 a2 K. inversion K. now apply IH1.
  - intros a a' b b' c c' H1 IH1 H2 IH2 H3 IH3 d K.
     inversion K. rewrite (IH1 _ H6). rewrite (IH2 _ H7). rewrite (IH3 _ H8). reflexivity.
  - intros al2 K. inversion K. reflexivity.
  - intros a a' bl bl' H1 IH1 H2 IH2 al2 K. inversion K. subst. rewrite (IH1 _ H4). now rewrite (IH2 _ H5).
Qed.

Opaque le_gt_dec.

(*** Tokens ***)
Inductive TOKEN :=
| NAM : string -> TOKEN
| NUM : bool -> nat -> nat -> TOKEN
| LPAREN : TOKEN
| RPAREN : TOKEN
| COMMA : TOKEN
| COLON : TOKEN
| DARR : TOKEN
| LET : TOKEN
| DEQ : TOKEN
| IN : TOKEN
| MEM : TOKEN
| SUBEQ : TOKEN
| VBAR : TOKEN
| LCBRACE : TOKEN
| RCBRACE : TOKEN
| LBRACK : TOKEN
| RBRACK : TOKEN
| IF_ : TOKEN
| THEN : TOKEN
| ELSE : TOKEN
.

Module TM <: TokenMod.

Definition TOKENtp := TOKEN.

Definition eq_bool_dec (b c:bool) : { b = c } + { b <> c }.
destruct b; destruct c; try tauto; right; discriminate.
Defined.

Definition dec_eq_tok (tok1 tok2:TOKEN) : { tok1 = tok2 } + { tok1 <> tok2 }.
destruct tok1,tok2; try tauto; try now (right; discriminate).
destruct (string_dec s s0) as [H1|H1].
left. congruence.
right. congruence.
destruct (eq_bool_dec b b0) as [H1|H1].
destruct (eq_nat_dec n n1) as [H2|H2].
destruct (eq_nat_dec n0 n2) as [H3|H3].
left. congruence.
right. congruence.
right. congruence.
right. congruence.
Defined.

End TM.
Export TM.

Module PrelimTM := PrelimTheory(TM).
Export PrelimTM.

(*** This function recognize when a list is either empty or the first element indicates some kind of boundary. ***)
Definition S'__endp (q : nat) (tl : list TOKEN) : Prop :=
  match q with
    | 0 => True
    | S _ =>
      match tl with
        | NAM x::_ =>
          match penv x with
            | (_,Some (p,_),_) => if (le_gt_dec q p) then True else False
            | (Some _,_,_) => True
            | (_,_,Some _) => True
            | _ => False (*** Not the end since we can use it as an argument to an implicit infix operator (application) ***)
          end
        | NUM _ _ _::_ => False (*** Not the end since we can use it as an argument to an implicit infix operator (application) ***)
        | LPAREN::_ => False
        | LCBRACE::_ => False
        | LBRACK::_ => False
        | MEM::_ => if (le_gt_dec q 500) then True else False
        | SUBEQ::_ => if (le_gt_dec q 500) then True else False
        | _ => True
      end
  end.

Lemma S'__endp_0 tl : S'__endp 0 tl.
Proof.
  exact I.
Qed.

Lemma S'__endp_leq p q tl : p >= q -> S'__endp p tl -> S'__endp q tl.
Proof.
  destruct q as [|q]; try exact (fun _ _ => I). destruct p as [|p]; try omega.
  unfold S'__endp. intros Hq. destruct tl; try tauto.
  destruct t; try tauto.
  destruct (penv s); try tauto.
  - destruct p0. destruct o0.
     + destruct o1; try tauto. destruct p0; try tauto.
        destruct (le_gt_dec (S p) n0); try tauto; destruct (le_gt_dec (S q) n0); try tauto; omega.
     + destruct o1; try tauto. destruct p0; try tauto.
        destruct (le_gt_dec (S p) n); try tauto; destruct (le_gt_dec (S q) n); try tauto; omega.
  - destruct (le_gt_dec (S p) 500); try tauto; destruct (le_gt_dec (S q) 500); try tauto; omega.
  - destruct (le_gt_dec (S p) 500); try tauto; destruct (le_gt_dec (S q) 500); try tauto; omega.
Qed.

Lemma S'__endp_app p tl tr : S'__endp p tl -> S'__endp p tr -> S'__endp p (tl ++ tr).
Proof.
  intros H1 H2. destruct tl.
  - simpl. exact H2.
  - exact H1.
Qed.

(*** TOKENS for different kinds of "type" ascription in binders. ***)
Definition AscKindTok (a:AscKind) : TOKEN :=
match a with
| AscTp => COLON
| AscSet => MEM
| AscSubeq => SUBEQ
end.

(*** TOKENS for different kinds of ways to separate bindvars from body in binders. ***)
Definition BinderMidTok (b:BinderMid) : TOKEN :=
match b with
| BinderMidComma => COMMA
| BinderMidDarr => DARR
end.

(*** Reln for lists of names ***)
Inductive pReln_Names : list TOKEN -> list string -> Prop :=
| pReln_Names_Nil : pReln_Names [] []
| pReln_Names_Cons x tl xl : nam_p x -> pReln_Names tl xl -> pReln_Names (NAM x::tl) (x::xl)
.

Definition SetInfixTOK (i:SetInfixOp) :=
match i with InfMem => MEM | InfSubq => SUBEQ end.

(*** Reln for grammar with no left recursion. InfixNone is treated the same as InfixLeft here, but print_S puts more parens in for InfixNone. ***)
Inductive pReln_S'_ : nat -> list TOKEN -> LTree -> LTree -> Prop :=
| pReln_S'__Empty a q : pReln_S'_ q [] a a
| pReln_S'__Postop_S'_ a q x p tl c : postinfop_info x = Some (p,Postfix) -> p < q -> pReln_S'_ q tl (Postop x a) c -> pReln_S'_ q (NAM x::tl) a c
| pReln_S'__InfixNone_S'_ a q x p tl b tr c : postinfop_info x = Some (p,InfixNone) -> p < q -> pReln_S_ p tl b -> Binderishp b = false -> S'__endp p tr -> pReln_S'_ q tr (Infop (InfNam x) a b) c -> pReln_S'_ q (NAM x::tl ++ tr) a c
| pReln_S'__InfixLeft_S'_ a q x p tl b tr c : postinfop_info x = Some (p,InfixLeft) -> p < q -> pReln_S_ p tl b -> Binderishp b = false -> S'__endp p tr -> pReln_S'_ q tr (Infop (InfNam x) a b) c -> pReln_S'_ q (NAM x::tl ++ tr) a c
| pReln_S'__InfixRight_S'_ a q x p tl b tr c : postinfop_info x = Some (p,InfixRight) -> p < q -> pReln_S_ (S p) tl b -> Binderishp b = false -> S'__endp (S p) tr -> pReln_S'_ q tr (Infop (InfNam x) a b) c -> pReln_S'_ q (NAM x::tl ++ tr) a c
| pReln_S'__InfixNone_B a q x p tl b : postinfop_info x = Some (p,InfixNone) -> p < q -> pReln_S_ p tl b -> Binderishp b = true -> pReln_S'_ q (NAM x::tl) a (Infop (InfNam x) a b)
| pReln_S'__InfixLeft_B a q x p tl b : postinfop_info x = Some (p,InfixLeft) -> p < q -> pReln_S_ p tl b -> Binderishp b = true -> pReln_S'_ q (NAM x::tl) a (Infop (InfNam x) a b)
| pReln_S'__InfixRight_B a q x p tl b : postinfop_info x = Some (p,InfixRight) -> p < q -> pReln_S_ (S p) tl b -> Binderishp b = true -> pReln_S'_ q (NAM x::tl) a (Infop (InfNam x) a b)
| pReln_S'__SetInfix_S'_ a q x itok tl b tr c : itok = SetInfixTOK x -> 500 < q -> pReln_S_ 500 tl b -> Binderishp b = false -> S'__endp 500 tr -> pReln_S'_ q tr (Infop (InfSet x) a b) c -> pReln_S'_ q (itok::tl ++ tr) a c
| pReln_S'__SetInfix_B a q x itok tl b : itok = SetInfixTOK x -> 500 < q -> pReln_S_ 500 tl b -> Binderishp b = true -> pReln_S'_ q (itok::tl) a (Infop (InfSet x) a b)
| pReln_S'__Implicit_S'_ a q tl b tr c : q > 0 -> pReln_S_ 0 tl b -> pReln_S'_ q tr (ImplicitInfop a b) c -> pReln_S'_ q (tl ++ tr) a c
with pReln_S_ : nat -> list TOKEN -> LTree -> Prop :=
| pReln_S__Nam_S'_ q x tl c : nam_p x -> pReln_S'_ q tl (Nam x) c -> pReln_S_ q (NAM x::tl) c
| pReln_S__Num_S'_ q b n m tl c : pReln_S'_ q tl (Num b n m) c -> pReln_S_ q (NUM b n m::tl) c
| pReln_S__Preop_B q x p tl a : preop_priority x = Some p -> p < q -> pReln_S_ (S p) tl a -> Binderishp a = true -> pReln_S_ q (NAM x::tl) (Preop x a)
| pReln_S__Preop_S'_ q x p tl a tr c : preop_priority x = Some p -> p < q -> pReln_S_ (S p) tl a -> Binderishp a = false -> S'__endp (S p) tr -> pReln_S'_ q tr (Preop x a) c -> pReln_S_ q (NAM x::tl ++ tr) c
| pReln_S__Paren_S'_ q tl a tlr bl tr c : pReln_S_ 1023 tl a -> pReln_N tlr bl -> pReln_S'_ q tr (Paren a bl) c -> pReln_S_ q (LPAREN::tl ++ tlr ++ RPAREN::tr) c
| pReln_S_Binder_U_ q x mtok vtl y yl tl a : q > 0 -> binder_midtok x = Some(mtok) -> pReln_Names vtl (y::yl) -> pReln_S_ 1010 tl a -> pReln_S_ q (NAM x::vtl ++ BinderMidTok mtok::tl) (Binder x mtok [(y::yl,None)] a)
| pReln_S_Binder_UT_ q x atok akd mtok vtl vl tr b tl a : q > 0 -> atok = AscKindTok akd -> binder_midtok x = Some(mtok) -> pReln_Names vtl vl -> pReln_S_ 1010 tr b -> pReln_S_ 1010 tl a -> pReln_S_ q (NAM x::vtl ++ atok::tr ++ BinderMidTok mtok::tl) (Binder x mtok [(vl,Some (akd,b))] a)
| pReln_S_Binder_T_ q x mtok vtl vll tl a : q > 0 -> binder_midtok x = Some(mtok) -> pReln_TVs vtl vll -> pReln_S_ 1010 tl a -> pReln_S_ q (NAM x::vtl ++ BinderMidTok mtok::tl) (Binder x mtok vll a)
| pReln_S_Let_U_ q x tl a tr c : q > 0 -> nam_p x -> pReln_S_ 1010 tl a -> pReln_S_ 1010 tr c -> pReln_S_ q (LET::NAM x::DEQ::tl ++ IN::tr) (LetL x None a c)
| pReln_S_Let_T_ q x atok akd tlb b tl a tr c : q > 0 -> atok = AscKindTok akd -> nam_p x -> pReln_S_ 1010 tlb b -> pReln_S_ 1010 tl a -> pReln_S_ 1010 tr c -> pReln_S_ q (LET::NAM x::atok::tlb ++ DEQ::tl ++ IN::tr) (LetL x (Some (akd,b)) a c)
| pReln_S_Sep_S'_ q x i itok tl a tlb b tr c : nam_p x -> itok = SetInfixTOK i
 -> pReln_S_ 500 tl a -> pReln_S_ 1010 tlb b -> pReln_S'_ q tr (SepL x i a b) c
 -> pReln_S_ q (LCBRACE::NAM x::itok::tl ++ VBAR::tlb ++ RCBRACE::tr) c
| pReln_S_Rep_S'_ q x i itok tl a tlb b tr c : nam_p x -> itok = SetInfixTOK i
 -> pReln_S_ 1010 tl a
 -> ~SetInfixOpL_p a
 -> pReln_S_ 500 tlb b -> pReln_S'_ q tr (RepL x i a b) c
 -> pReln_S_ q (LCBRACE::tl ++ VBAR::NAM x::itok::tlb ++ RCBRACE::tr) c
| pReln_S_SepRep_S'_ q x i itok tl a tlb b tlc c tr d : nam_p x -> itok = SetInfixTOK i
 -> pReln_S_ 1010 tl a
 -> ~SetInfixOpL_p a
 -> pReln_S_ 500 tlb b -> pReln_S_ 1010 tlc c -> pReln_S'_ q tr (SepRepL x i a b c) d
 -> pReln_S_ q (LCBRACE::tl ++ VBAR::NAM x::itok::tlb ++ COMMA::tlc ++ RCBRACE::tr) d
| pReln_S_SetEmpty_S'_ q tr c : pReln_S'_ q tr (SetEnumL LNil) c -> pReln_S_ q (LCBRACE::RCBRACE::tr) c
| pReln_S_SetEnum_S'_ q tl a tlr bl tr c : pReln_S_ 1023 tl a -> pReln_N tlr bl -> pReln_S'_ q tr (SetEnumL (LCons a bl)) c -> pReln_S_ q (LCBRACE::tl ++ tlr ++ RCBRACE::tr) c
| pReln_S_MTuple_S'_ q tl a tlr bl tr c : pReln_S_ 1023 tl a -> pReln_N tlr bl -> pReln_S'_ q tr (MTupleL a bl) c -> pReln_S_ q (LBRACK::tl ++ tlr ++ RBRACK::tr) c
| pReln_S_IfThenElse_ q tl1 a tl2 b tl3 c : q > 0 -> pReln_S_ 1010 tl1 a -> pReln_S_ 1010 tl2 b -> pReln_S_ 1010 tl3 c -> pReln_S_ q (IF_::tl1 ++ THEN::tl2 ++ ELSE::tl3) (IfThenElseL a b c)
with pReln_TVs : list TOKEN -> list (list string * option (AscKind * LTree)) -> Prop :=
| pReln_TVs_Nil : pReln_TVs [] []
| pReln_TVs_UNames_TVs vtl vl tl vll : pReln_Names vtl vl -> pReln_TVs tl vll -> pReln_TVs (LPAREN::vtl ++ RPAREN::tl) ((vl,None)::vll)
| pReln_TVs_TNames_TVs atok akd vtl vl tb b tl vll : atok = AscKindTok akd -> pReln_Names vtl vl -> pReln_S_ 1010 tb b -> pReln_TVs tl vll -> pReln_TVs (LPAREN::vtl ++ atok::tb ++ RPAREN::tl) ((vl,Some(akd,b))::vll)
with pReln_N : list TOKEN -> LTreeL -> Prop :=
| pReln_N_Nil : pReln_N [] LNil
| pReln_N_Cons tl a tlr bl : pReln_S_ 1023 tl a -> pReln_N tlr bl -> pReln_N (COMMA::tl ++ tlr) (LCons a bl)
.

Scheme pReln_S'__ind2 := Minimality for pReln_S'_ Sort Prop
with pReln_S__ind2 := Minimality for pReln_S_ Sort Prop
with pReln_TVs_ind2 := Minimality for pReln_TVs Sort Prop
with pReln_N_ind2 := Minimality for pReln_N Sort Prop.

Combined Scheme pRelnl_mutind from pReln_S'__ind2, pReln_S__ind2, pReln_TVs_ind2, pReln_N_ind2.

Lemma pReln_S'_S'_leq q q' tl a c :
q <= q' -> pReln_S'_ q tl a c -> pReln_S'_ q' tl a c.
Proof.
  intros Hq H. revert Hq. induction H.
  - intros Hq. apply pReln_S'__Empty.
  - intros Hq. apply (pReln_S'__Postop_S'_ _ q' x p); try tauto. omega.
  - intros Hq. apply (pReln_S'__InfixNone_S'_ a q' x p _ b); try tauto; try omega.
  - intros Hq. apply (pReln_S'__InfixLeft_S'_ _ q' x p _ b); try tauto; try omega.
  - intros Hq. apply (pReln_S'__InfixRight_S'_ _ q' x p _ b); try tauto; try omega.
  - intros Hq. apply (pReln_S'__InfixNone_B a q' x p _ b); try tauto; try omega.
  - intros Hq. apply (pReln_S'__InfixLeft_B _ q' x p _ b); try tauto; try omega.
  - intros Hq. apply (pReln_S'__InfixRight_B _ q' x p _ b); try tauto; try omega.
  - intros Hq. apply (pReln_S'__SetInfix_S'_ _ q' x itok tl b tr c); try tauto. omega.
  - intros Hq. apply (pReln_S'__SetInfix_B _ q' x itok tl b); try tauto. omega.
  - intros Hq. apply pReln_S'__Implicit_S'_ with (b := b); try assumption.
     + omega.
     + now apply IHpReln_S'_.
Qed.


Lemma pReln_S_S_leq q q' tl a :
q <= q' -> pReln_S_ q tl a -> pReln_S_ q' tl a.
Proof.
  intros Hq H. revert Hq. induction H; intros Hq.
  - apply (pReln_S__Nam_S'_ q' x tl c H); try assumption. now apply (pReln_S'_S'_leq q).
  - apply (pReln_S__Num_S'_ q' b n m); try assumption. revert H. now apply (pReln_S'_S'_leq q).
  - apply (pReln_S__Preop_B q' x p _ a); try assumption; try omega.
  - apply (pReln_S__Preop_S'_ q' x p _ a); try assumption; try omega. revert H4. apply pReln_S'_S'_leq. omega.
  - apply pReln_S__Paren_S'_ with (a := a) (bl := bl); try assumption. now apply (pReln_S'_S'_leq q).
  - apply pReln_S_Binder_U_; try assumption; try omega.
  - apply pReln_S_Binder_UT_ with (b := b); try assumption; try omega.
  - apply pReln_S_Binder_T_; try assumption; try omega.
  - apply pReln_S_Let_U_; try assumption; try omega.
  - apply pReln_S_Let_T_; try assumption; try omega.
  - apply pReln_S_Sep_S'_ with (i := i) (a := a) (b := b); try assumption; try omega. revert H3. now apply pReln_S'_S'_leq.
  - apply pReln_S_Rep_S'_ with (i := i) (a := a) (b := b); try assumption; try omega. revert H4. now apply pReln_S'_S'_leq.
  - apply pReln_S_SepRep_S'_ with (i := i) (a := a) (b := b) (c := c); try assumption; try omega. revert H5. apply pReln_S'_S'_leq. assumption.
  - apply pReln_S_SetEmpty_S'_; try assumption; try omega. revert H. now apply pReln_S'_S'_leq.
  - apply pReln_S_SetEnum_S'_ with (a := a) (bl := bl); try assumption; try omega. revert H1. now apply pReln_S'_S'_leq.
  - apply pReln_S_MTuple_S'_ with (a := a) (bl := bl); try assumption; try omega. revert H1. now apply pReln_S'_S'_leq.
  - apply pReln_S_IfThenElse_; try assumption. omega.
Qed.

Lemma S'__endp_preop_S p tr :
(exists x, preop_priority x = Some p) ->
S'__endp p tr -> S'__endp (S p) tr.

Proof.
  destruct tr.
  - intros _ _. exact I.
  - intros [x H1]. unfold S'__endp. destruct t; try tauto.
     + destruct p as [|p].
        * exfalso. exact (penv_Preop_nonzero _ H1).
        * { case_eq (penv s). intros [[p'|] [[q k]|]] ob; try tauto.
             - destruct (le_gt_dec (S p) q) as [Hpq|Hpq]; try tauto. intros K1 _.
                destruct (le_gt_dec (S (S p)) q) as [HSpq|HSpq]; try tauto.
                assert (L1:S p = q) by omega.
                destruct k.
                + generalize (penv_Preop_Postop x s (S p) q H1). unfold postinfop_info. rewrite K1. tauto.
                + generalize (penv_Preop_InfixNone x s (S p) q H1). unfold postinfop_info. rewrite K1. tauto.
                + generalize (penv_Preop_InfixLeft x s (S p) q H1). unfold postinfop_info. rewrite K1. tauto.
                + generalize (penv_Preop_InfixRight x s (S p) q H1). unfold postinfop_info. rewrite K1. tauto.
             - destruct (le_gt_dec (S p) q) as [Hpq|Hpq]; try tauto. intros K1 _.
                destruct (le_gt_dec (S (S p)) q) as [HSpq|HSpq]; try tauto.
                assert (L1:S p = q) by omega.
                destruct k.
                + generalize (penv_Preop_Postop x s (S p) q H1). unfold postinfop_info. rewrite K1. tauto.
                + generalize (penv_Preop_InfixNone x s (S p) q H1). unfold postinfop_info. rewrite K1. tauto.
                + generalize (penv_Preop_InfixLeft x s (S p) q H1). unfold postinfop_info. rewrite K1. tauto.
                + generalize (penv_Preop_InfixRight x s (S p) q H1). unfold postinfop_info. rewrite K1. tauto.
           }
     + destruct p; try tauto. intros _. revert H1. apply (penv_Preop_nonzero x).
     + destruct p; try tauto. intros _. revert H1. apply (penv_Preop_nonzero x).
     + destruct p.
        * destruct (le_gt_dec 1 500); try tauto; try omega.
        * destruct (le_gt_dec (S p) 500); try tauto.
           destruct (le_gt_dec (S (S p)) 500); try tauto.
           assert (S p = 500) by omega.
           exfalso. apply (penv_Preop_not500 _ _ H1). assumption.
     + destruct p.
        * destruct (le_gt_dec 1 500); try tauto; try omega.
        * destruct (le_gt_dec (S p) 500); try tauto.
           destruct (le_gt_dec (S (S p)) 500); try tauto.
           assert (S p = 500) by omega.
           exfalso. apply (penv_Preop_not500 _ _ H1). assumption.
     + destruct p; try tauto. exfalso. apply (penv_Preop_nonzero _ H1).
     + destruct p; try tauto. exfalso. apply (penv_Preop_nonzero _ H1).
Qed.

Lemma pReln_S'__S'__app q tl a b tr c :
  pReln_S'_ q tl a b ->
  Binderishp b = false ->
  forall q', q <= S q' ->
  S'__endp q' tr ->
  ~(exists z, postinfop_info z = Some(q',InfixRight)) ->
  pReln_S'_ (S q') tr b c ->
  pReln_S'_ (S q') (tl ++ tr) a c.
Proof.
  intros H. induction H.
  - simpl. tauto.
  - intros NB q' Hqq' H2' NIR H3.
     simpl. apply (pReln_S'__Postop_S'_ _ (S q') x p (tl ++ tr)).
     + assumption.
     + omega.
     + apply IHpReln_S'_; try assumption.
  - intros NB q' Hqq' K1 NIR K2.
     simpl. rewrite <- app_assoc.
     apply (pReln_S'__InfixNone_S'_ _ (S q') x p tl b (tr0 ++ tr)).
     + assumption.
     + omega.
     + assumption.
     + assumption.
     + apply S'__endp_app; try assumption. revert K1. apply S'__endp_leq. omega.
     + apply IHpReln_S'_; try assumption.
  - intros NB q' Hqq' K1 NIR K2.
     simpl. rewrite <- app_assoc.
     apply (pReln_S'__InfixLeft_S'_ _ (S q') x p tl b (tr0 ++ tr)).
     + assumption.
     + omega.
     + assumption.
     + assumption.
     + apply S'__endp_app; try assumption. revert K1. apply S'__endp_leq. omega.
     + apply IHpReln_S'_; try assumption.
  - intros NB q' Hqq' K1 NIR K2.
     simpl. rewrite <- app_assoc.
     apply (pReln_S'__InfixRight_S'_ _ (S q') x p tl b (tr0 ++ tr)).
     + assumption.
     + omega.
     + assumption.
     + assumption.
     + apply S'__endp_app; try assumption.
        assert (L1:q' = p \/ q' >= S p) by omega.
        destruct L1 as [La|La].
        * { revert K1. unfold S'__endp.
             destruct tr; try tauto.
             destruct q'.
             - exfalso. generalize (penv_PostInfop_nonzero _ _ _ H). congruence.
             - destruct t; try tauto.
                + case_eq (penv s).
                   intros [op'' [[q'' k']|]] ob; try tauto.
                   intros K3. 
                   destruct (le_gt_dec (S q') q''); try (destruct op''; tauto).
                   intros _.
                   destruct (le_gt_dec (S p) q''); try (destruct op''; tauto).
                   exfalso.
                   assert (L2:q'' = p) by omega.
                   subst q''.
                   assert (L3:postinfop_info s = Some(p,k')).
                   {
                     unfold postinfop_info. rewrite K3. reflexivity.
                   }
                   destruct k'.
                   * generalize (penv_InfixRight_Postop _ _ _ _ H L3). tauto.
                   * generalize (penv_InfixRight_InfixNone _ _ _ _ H L3). tauto.
                   * generalize (penv_InfixRight_InfixLeft _ _ _ _ H L3). tauto.
                   * apply NIR. exists s. now rewrite La.
                + destruct (le_gt_dec (S q') 500); destruct (le_gt_dec (S p) 500); try tauto. exfalso.
                   apply (penv_InfixRight_not500 _ _ H). omega.
                + destruct (le_gt_dec (S q') 500); destruct (le_gt_dec (S p) 500); try tauto. exfalso.
                   apply (penv_InfixRight_not500 _ _ H). omega.
           }
        * revert K1. apply S'__endp_leq. omega.
     + apply IHpReln_S'_; try assumption.
  - intros NB. exfalso. simpl in NB. rewrite NB in H2. discriminate.
  - intros NB. exfalso. simpl in NB. rewrite NB in H2. discriminate.
  - intros NB. exfalso. simpl in NB. rewrite NB in H2. discriminate.
  - intros NB q' Hq' Hr NIR K. simpl. rewrite <- app_assoc.
     apply (pReln_S'__SetInfix_S'_ _ (S q') x itok tl b (tr0 ++ tr)).
     + assumption.
     + omega.
     + assumption.
     + assumption.
     + apply S'__endp_app; try assumption. revert Hr. apply S'__endp_leq. omega.
     + apply IHpReln_S'_; try assumption.
  - intros NB q' Hq' Hr NIR K. simpl.
     apply (pReln_S'__SetInfix_S'_ _ (S q') x itok tl b).
     + assumption.
     + omega.
     + assumption.
     + assumption.
     + revert Hr. apply S'__endp_leq. omega.
     + assumption.
  - intros NB q' Hqq' Hq' NIR H3.
     rewrite <- app_assoc.
     apply pReln_S'__Implicit_S'_ with (b := b); try assumption; try omega.
     now apply IHpReln_S'_.
Qed.

Lemma pReln_S__S'__app q tl a tr b :
  pReln_S_ q tl a ->
  Binderishp a = false ->
  forall q', q <= S q' ->
  S'__endp q' tr ->
  ~(exists z, postinfop_info z = Some(q',InfixRight)) ->
  pReln_S'_ (S q') tr a b ->
  pReln_S_ (S q') (tl ++ tr) b.
Proof.
  intros H. induction H; intros NB q' K1 K2 NIR K3.
  - simpl. apply (pReln_S__Nam_S'_ (S q') x (tl ++ tr)); try assumption.
     apply pReln_S'__S'__app with (q := q) (b := c); try assumption.
  - simpl. apply (pReln_S__Num_S'_ (S q') b0 n m (tl ++ tr)); try assumption.
     apply pReln_S'__S'__app with (q := q) (b := c); try assumption.
  - simpl in NB. rewrite NB in H2. discriminate.
  - simpl. rewrite <- app_assoc. simpl.
     apply (pReln_S__Preop_S'_ (S q') x p tl a (tr0 ++ tr)); try assumption; try omega.
     + apply S'__endp_app; try assumption. revert K2.
        assert (L1:q' = p \/ q' > p) by omega.
        destruct L1 as [H5|H5].
        * subst q'. apply S'__endp_preop_S. exists x. assumption.
        * apply S'__endp_leq. omega.
     + apply pReln_S'__S'__app with (q := q) (b := c); try assumption. 
  - simpl. rewrite <- app_assoc. rewrite <- app_assoc.
     simpl. apply (pReln_S__Paren_S'_ (S q') tl a tlr bl (tr0 ++ tr)).
     + assumption.
     + assumption.
     + apply pReln_S'__S'__app with (q := q) (b := c); try assumption. 
  - simpl in NB. discriminate.
  - simpl in NB. discriminate.
  - simpl in NB. discriminate.
  - simpl in NB. discriminate.
  - simpl in NB. discriminate.
  - simpl. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl.
     apply pReln_S_Sep_S'_ with (i := i) (a := a) (b := b0); try assumption.
     apply pReln_S'__S'__app with (q := q) (b := c); try assumption.
  - simpl. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl.
     apply pReln_S_Rep_S'_ with (i := i) (a := a) (b := b0); try assumption.
     apply pReln_S'__S'__app with (q := q) (b := c); try assumption.
  - simpl. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl.
     apply pReln_S_SepRep_S'_ with (i := i) (a := a) (b := b0) (c := c); try assumption.
     apply pReln_S'__S'__app with (q := q) (b := d); try assumption.
  - simpl. apply pReln_S_SetEmpty_S'_.
     apply pReln_S'__S'__app with (q := q) (b := c); try assumption.
  - simpl. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl.
     apply (pReln_S_SetEnum_S'_ (S q') tl a tlr bl (tr0 ++ tr) b); try assumption.
     apply pReln_S'__S'__app with (q := q) (b := c); try assumption.
  - simpl. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl.
     apply (pReln_S_MTuple_S'_ (S q') tl a tlr bl (tr0 ++ tr) b); try assumption.
     apply pReln_S'__S'__app with (q := q) (b := c); try assumption.
  - simpl in NB. discriminate.
Qed.

Lemma pReln_S__Nam q x : nam_p x -> pReln_S_ q [NAM x] (Nam x).
Proof.
  intros H.
  apply (pReln_S__Nam_S'_ q x nil); try assumption.
  apply pReln_S'__Empty.
Qed.

Lemma pReln_S__Paren_Tuple q tl tlr a bl : pReln_S_ 1023 tl a -> pReln_N tlr bl -> pReln_S_ q (LPAREN::tl ++ tlr ++ [RPAREN]) (Paren a bl).
Proof.
  intros H1 H2.
  apply (pReln_S__Paren_S'_ q tl a tlr bl nil); try assumption.
  apply pReln_S'__Empty.
Qed.

Lemma pReln_S__Paren q tl a : pReln_S_ 1023 tl a -> pReln_S_ q (LPAREN::tl ++ [RPAREN]) (Paren a LNil).
Proof.
  intros H. apply (pReln_S__Paren_Tuple q tl nil a LNil H).
  apply pReln_N_Nil.
Qed.

Lemma pReln_S__Preop q x p tl a : preop_priority x = Some p -> p < q -> pReln_S_ (S p) tl a -> pReln_S_ q (NAM x::tl) (Preop x a).
Proof.
  intros H1 H2 H3.
  case_eq (Binderishp a); intros E.
  - apply (pReln_S__Preop_B q x p tl a); try assumption.
  - generalize (pReln_S__Preop_S'_ q x p tl a nil); try assumption.
     rewrite <- app_nil_end. intros H. apply H; try assumption.
     + exact I.
     + apply pReln_S'__Empty.
Qed.

Lemma pReln_S'__Postop q x p a : postinfop_info x = Some (p,Postfix)
 -> p < q -> pReln_S'_ q [NAM x] a (Postop x a).
Proof.
  intros H1 H2.
  apply (pReln_S'__Postop_S'_ _ q x p nil); try assumption.
  apply pReln_S'__Empty.
Qed.

Lemma pReln_S'__InfixNone q x p tl a b : postinfop_info x = Some (p,InfixNone)
 -> p < q -> 
 pReln_S_ p tl b ->
 pReln_S'_ q (NAM x::tl) a (Infop (InfNam x) a b).
Proof.
  intros H1 H2 H3.
  case_eq (Binderishp b); intros E.
  - apply pReln_S'__InfixNone_B with (p := p); try assumption.
  - generalize (pReln_S'__InfixNone_S'_ a q x p tl b nil (Infop (InfNam x) a b)).
     rewrite <- app_nil_end. intros G. apply G; try assumption.
     + destruct p; exact I.
     + apply pReln_S'__Empty.
Qed.

Lemma pReln_S'__InfixLeft q x p tl a b : postinfop_info x = Some (p,InfixLeft)
 -> p < q ->
 pReln_S_ p tl b ->
 pReln_S'_ q (NAM x::tl) a (Infop (InfNam x) a b).
Proof.
  intros H1 H2 H3.
  case_eq (Binderishp b); intros E.
  - apply pReln_S'__InfixLeft_B with (p := p); try assumption.
  - generalize (pReln_S'__InfixLeft_S'_ a q x p tl b nil (Infop (InfNam x) a b)).
     rewrite <- app_nil_end. intros G. apply G; try assumption.
     + destruct p; exact I.
     + apply pReln_S'__Empty.
Qed.

Lemma pReln_S'__InfixRight q x p tl a b : postinfop_info x = Some (p,InfixRight)
 -> p < q ->
 pReln_S_  (S p) tl b ->
 pReln_S'_ q (NAM x::tl) a (Infop (InfNam x) a b).
Proof.
  intros H1 H2 H3.
  case_eq (Binderishp b); intros E.
  - apply pReln_S'__InfixRight_B with (p := p); try assumption.
  - generalize (pReln_S'__InfixRight_S'_ a q x p tl b nil (Infop (InfNam x) a b)).
     rewrite <- app_nil_end. intros G. apply G; try assumption.
     + destruct p; exact I.
     + apply pReln_S'__Empty.
Qed.

Lemma pReln_S_Preop q x p tl a : preop_priority x = Some p -> 1010 <= q -> pReln_S_ (S p) tl a -> pReln_S_ q (NAM x::tl) (Preop x a).
Proof.
  intros H1 H2 H3. apply pReln_S__Preop with (p := p); try assumption.
  generalize (penv_Preop_max x p H1). omega.
Qed.

Lemma pReln_S'_Postop q x p a : postinfop_info x = Some (p,Postfix) -> 1010 <= q
 -> pReln_S'_ q [NAM x] a (Postop x a).
Proof.
  intros H1 H2. apply pReln_S'__Postop with (p := p); try assumption.
  generalize (penv_PostInfop_max x p Postfix H1). omega.
Qed.

Lemma pReln_S_S'_InfixRight_lem :
 (forall p tl a c,
   pReln_S'_ p tl a c ->
   Binderishp c = false ->
   forall y tr b,
   postinfop_info y = Some(p,InfixRight)
   -> pReln_S_ (S p) tr b
   -> pReln_S'_ (S p) (tl ++ NAM y :: tr) a (Infop (InfNam y) c b))
 /\
 (forall p tl a,
   pReln_S_ p tl a ->
   Binderishp a = false ->
   forall y tr b,
   postinfop_info y = Some(p,InfixRight)
   -> pReln_S_ (S p) tr b
   -> pReln_S_ (S p) (tl ++ NAM y :: tr) (Infop (InfNam y) a b))
 /\
 (forall vtl vl,
   pReln_TVs vtl vl ->
  True)
 /\
 (forall tll bl,
   pReln_N tll bl ->
  True)
.
Proof.
  apply pRelnl_mutind.
  - intros a q y tr b Hyq NB H1. simpl. apply pReln_S'__InfixRight with (p := q); try assumption; try omega.
  - intros a q x p tl c Hxp Hpq H1 IH1 NB y ts b Hyq H2. simpl.
     apply (pReln_S'__Postop_S'_ _ (S q) x p (tl ++ NAM y :: ts)).
     + assumption.
     + omega.
     + now apply IH1.
  - intros a q x p tl b tr d Hx Hpq H1 IH1 NBb Hr H2 IH2 NBd y ts c Hyq H3.
     simpl. rewrite <- app_assoc.
     apply (pReln_S'__InfixNone_S'_ _ (S q) x p tl b (tr ++ NAM y :: ts)).
     + assumption.
     + omega.
     + assumption.
     + assumption.
     + apply S'__endp_app; try assumption. destruct p; try exact I. simpl.
        revert Hyq. unfold postinfop_info. case_eq (penv y).
        intros [op' [[q' k']|]] ob'; try tauto; try discriminate.
        intros H4 H5. destruct (le_gt_dec (S p) q'); try (destruct op'; tauto). inversion H5. omega.
     + now apply IH2.
  - intros a q x p tl b tr d Hx Hpq H1 IH1 NBb Hr H2 IH2 NBd y ts c Hyq H3.
     simpl. rewrite <- app_assoc.
     apply (pReln_S'__InfixLeft_S'_ _ (S q) x p tl b (tr ++ NAM y :: ts)).
     + assumption.
     + omega.
     + assumption.
     + assumption.
     + apply S'__endp_app; try assumption. destruct p; try exact I. simpl.
        revert Hyq. unfold postinfop_info. case_eq (penv y).
        intros [op' [[q' k']|]] ob'; try (destruct op'; destruct ob'; tauto).
        * intros H4 H5. destruct (le_gt_dec (S p) q'); try (destruct op'; tauto).
           inversion H5. omega.
        * discriminate.
     + now apply IH2.
  - intros a q x p tl b tr d Hx NBb Hpq H1 IH1 Hr H2 IH2 NBd y ts c Hyq H3.
     simpl. rewrite <- app_assoc.
     apply (pReln_S'__InfixRight_S'_ _ (S q) x p tl b (tr ++ NAM y :: ts)).
     + assumption.
     + omega.
     + assumption.
     + assumption.
     + apply S'__endp_app; try assumption. simpl.
        revert Hyq. unfold postinfop_info. case_eq (penv y).
        intros [op' [[q' k']|]] ob'; try (destruct op'; destruct ob'; tauto).
        * intros H4 H5. destruct (le_gt_dec (S p) q'); try (destruct op'; tauto).
           inversion H5. omega.
        * discriminate.
     + now apply IH2.
  - intros a q x p tl b Hx Hpq H1 IH1 Bb NBab y ts c Hyq H3.
     simpl in NBab. rewrite NBab in Bb. discriminate.
  - intros a q x p tl b Hx Hpq H1 IH1 Bb NBab y ts c Hyq H3.
     simpl in NBab. rewrite NBab in Bb. discriminate.
  - intros a q x p tl b Hx Hpq H1 IH1 Bb NBab y ts c Hyq H3.
     simpl in NBab. rewrite NBab in Bb. discriminate.
  - intros a q x itok tl b tr c Hix Hq H1 IH1 NBb Hr H2 IH2 NBc y ts d Hy K1.
     simpl. rewrite <- app_assoc.
     apply pReln_S'__SetInfix_S'_ with (x := x) (b := b); try assumption; try omega.
     + apply S'__endp_app; try assumption. simpl. revert Hy. unfold postinfop_info.
        case_eq (penv y). intros [[p'|] [[q' k']|]] omtok; try discriminate; intros _ K2; inversion K2; destruct (le_gt_dec 500 q); try tauto; omega.
     + apply IH2; try assumption.
  - intros a q x itok tl b Hix Hq H1 IH1 Bb NBab. exfalso.
     simpl in NBab. rewrite Bb in NBab. discriminate.
  - intros a q tl b tr d Hq H1 IH1 H2 IH2 NBd y ts c Hyq H3.
     rewrite <- app_assoc.
     apply (pReln_S'__Implicit_S'_ _ (S q) tl b (tr ++ NAM y :: ts)).
     + omega.
     + assumption.
     + now apply IH2.
  - intros q x tl d Hx H1 IH1 NBd y ts c Hyq H3.
     simpl.
     apply (pReln_S__Nam_S'_ (S q) x (tl ++ NAM y :: ts)).
     + assumption.
     + now apply IH1.
  - intros q b' n m tl c H1 IH1 NBc y tr b Hy K1. simpl.
     apply pReln_S__Num_S'_.
     apply IH1; try assumption.
  - intros q x p tl a Hxp Hpq H1 IH1 NBa Ba. exfalso. simpl in Ba. rewrite NBa in Ba. discriminate.
  - intros q x p tl a tr c Hxp Hpq H1 IH1 NBa H2 H3 IH3 NBc y ts b Hyq H4.
     simpl. rewrite <- app_assoc.
     apply (pReln_S__Preop_S'_ (S q) x p tl a (tr ++ NAM y :: ts)).
     + assumption.
     + omega.
     + assumption.
     + assumption.
     + apply S'__endp_app; try assumption. simpl.
        revert Hyq. unfold postinfop_info. case_eq (penv y).
        intros [op' [[q' k']|]] ob'; try (destruct op'; destruct ob'; tauto).
        * intros H4' H5. destruct (le_gt_dec (S p) q'); try (destruct op'; tauto).
           inversion H5. omega.
        * discriminate.
     + now apply IH3.
  - intros q tl a tlr bl tr c H1 IH1 H2 _ H3 IH3 NBc y ts b Hyq H4.
     simpl. rewrite <- app_assoc. rewrite <- app_assoc. simpl.
     apply (pReln_S__Paren_S'_ (S q) tl a tlr bl (tr ++ NAM y :: ts)).
     + assumption.
     + assumption.
     + now apply IH3.
  - intros q x mtok vtl vl tl a Hq Hx H1 H2 IH2 NB. simpl in NB. discriminate.
  - intros q x mtok vtl vl tr b tl a Hq Hx H1 H2 IH2 H3 IH3 NB. simpl in NB. discriminate.
  - intros q x mtok vtl vl tl a Hq Hx H1 IH1 H2 IH2 NB. simpl in NB. discriminate.
  - intros q x tl a tr c Hq Hx H1 IH1 H2 IH2 NB. simpl in NB. discriminate.
  - intros q x tl a tr c Hq Hx H0 IH0 H1 IH1 H2 IH2 NB. simpl in NB. discriminate.
  - intros q x i itok tl a tlb b tr c Hx Hi H1 IH1 H2 IH2 H3 IH3 NBc y tu d Hy K1.
     simpl. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl.
     apply pReln_S_Sep_S'_ with (i := i) (a := a) (b := b); try assumption.
     apply IH3; try assumption.
  - intros q x i itok tl a tlb b tr c Hx Hi H1 IH1 Ka H2 IH2 H3 IH3 NBc y tu d Hy K1.
     simpl. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl.
     apply pReln_S_Rep_S'_ with (i := i) (a := a) (b := b); try assumption.
     apply IH3; try assumption.
  - intros q x i itok tl a tlb b tlc c tr e Hx Hi H1 IH1 Ka H2 IH2 H3 IH3 H4 IH4 NBc y tu d Hy K1.
     simpl. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl.
     apply pReln_S_SepRep_S'_ with (i := i) (a := a) (b := b) (c := c); try assumption.
     apply IH4; try assumption.
  - intros q tr c H1 IH1 NBc y ts e Hy K1. simpl.
     apply pReln_S_SetEmpty_S'_. apply IH1; try assumption.
  - intros q tl a tlr bl tr c H1 IH1 H2 _ H3 IH3 NBc y tu d Hy K1.
     simpl. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl.
     apply pReln_S_SetEnum_S'_ with (a := a) (bl := bl); try assumption.
     apply IH3; try assumption.
  - intros q tl a tlr bl tr c H1 IH1 H2 _ H3 IH3 NBc y tu d Hy K1.
     simpl. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl.
     apply pReln_S_MTuple_S'_ with (a := a) (bl := bl); try assumption.
     apply IH3; try assumption.
  - intros q tl1 a tl2 b tl3 c H1 IH1 H2 IH2 H3 IH3 NBc. simpl in NBc. discriminate.
  - tauto.
  - tauto.
  - tauto.
  - tauto.
  - tauto.
Qed.

Lemma pReln_S_InfixRight x p tl a tr b :
 postinfop_info x = Some(p,InfixRight) ->
 pReln_S_ p tl a -> pReln_S_ (S p) tr b ->
 Binderishp a = false ->
 pReln_S_ (S p) (tl ++ NAM x :: tr) (Infop (InfNam x) a b).
Proof.
  destruct pReln_S_S'_InfixRight_lem as [_ [L _]].
  intros H1 H2 H3 H4. now apply L.
Qed.

(*** Note that print_S does not depend on penv. ***)
Fixpoint print_S (a : LTree) : list TOKEN :=
match a with
| Nam x => [NAM x]
| Num b n m => [NUM b n m]
| LetL x None a c => LET::NAM x::DEQ::print_S a ++ IN::print_S c
| LetL x (Some (bkd,b)) a c => LET::NAM x::AscKindTok bkd::print_S b ++ DEQ::print_S a ++ IN::print_S c
| Binder x mtok [(y::yl,None)] a => NAM x::map NAM (y::yl) ++ BinderMidTok mtok::print_S a
| Binder x mtok [(yl,Some(bkd,b))] a => NAM x::map NAM yl ++ AscKindTok bkd::print_S b ++ BinderMidTok mtok::print_S a
| Binder x mtok vll a => NAM x::flat_map (fun xlob : (list string) * option (AscKind * LTree) => let (xl,ob) := xlob in LPAREN::map NAM xl ++ match ob with Some(bkd,b) => AscKindTok bkd::print_S b ++ [RPAREN] | None => [RPAREN] end) vll ++ BinderMidTok mtok::print_S a
| Preop x a => NAM x::print_S a
| Postop x a => print_S a ++ [NAM x]
| Infop (InfNam x) a b => print_S a ++ NAM x::print_S b
| Infop (InfSet i) a b => print_S a ++ SetInfixTOK i::print_S b
| ImplicitInfop a b => print_S a ++ print_S b
| SepL x i a b => LCBRACE::NAM x::SetInfixTOK i::print_S a ++ VBAR::print_S b ++ [RCBRACE]
| RepL x i a b => LCBRACE::print_S a ++ VBAR::NAM x::SetInfixTOK i::print_S b ++ [RCBRACE]
| SepRepL x i a b c => LCBRACE::print_S a ++ VBAR::NAM x::SetInfixTOK i::print_S b ++ COMMA::print_S c ++ [RCBRACE]
| SetEnumL LNil => [LCBRACE;RCBRACE]
| SetEnumL (LCons a bl) => LCBRACE::print_S a ++ print_SL bl ++ [RCBRACE]
| MTupleL a bl => LBRACK::print_S a ++ print_SL bl ++ [RBRACK]
| Paren a bl => LPAREN::print_S a ++ print_SL bl ++ [RPAREN]
| IfThenElseL a b c => IF_::print_S a ++ THEN::print_S b ++ ELSE::print_S c
end
with print_SL (bl:LTreeL) : list TOKEN :=
match bl with
| LNil => []
| LCons b br => COMMA::print_S b ++ print_SL br
end
.

Lemma pReln_Names_map yl : (forall y, In y yl -> nam_p y) -> pReln_Names (map NAM yl) yl.
Proof.
  induction yl.
  - simpl. intros _. apply pReln_Names_Nil.
  - simpl. intros H. apply pReln_Names_Cons.
    + apply H. now left.
    + apply IHyl. intros y H1. apply H. now right.
Qed.

Lemma print_S_Bindvars : forall vl : list (list string * option (AscKind * LTree)),
   (forall (zl : list string) (ob : option (AscKind * LTree)),
    In (zl, ob) vl ->
    forall z : string, In z zl -> nam_p z) ->
   (forall (zl : list string) (bkd : AscKind) (b : LTree),
    In (zl, Some (bkd,b)) vl -> suppL 1010 b) ->
   (forall (zl : list string) (bkd : AscKind) (b : LTree),
    In (zl, Some (bkd,b)) vl ->
    pReln_S_ 1010 (print_S b) b) ->
   pReln_TVs
     (flat_map
        (fun xlob : list string * option (AscKind * LTree) =>
         let (xl, ob) := xlob in
         LPAREN
         :: map NAM xl ++
            match ob with
            | Some (bkd,b) => AscKindTok bkd :: print_S b ++ [RPAREN]
            | None => [RPAREN]
            end) vl) vl.
Proof.
  intros vl. induction vl; intros K1 K2 K3.
  - simpl. apply pReln_TVs_Nil.
  - simpl. destruct a. destruct o.
     + destruct p. simpl. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl.
        apply pReln_TVs_TNames_TVs.
        * reflexivity.
        * apply pReln_Names_map. intros y Hy.
           apply (K1 l (Some (a,l0))); try assumption.
           now left.
        * apply (K3 l a l0). now left.
        * { apply IHvl.
             - intros zl ob K4. apply (K1 zl ob). now right.
             - intros zl bkd b K4. apply (K2 zl bkd b). now right.
             - intros zl bkd b K4. apply (K3 zl bkd b). now right.
           }
     + simpl. rewrite <- app_assoc. simpl.
        apply pReln_TVs_UNames_TVs.
        * apply pReln_Names_map. intros y Hy.
           apply (K1 l None); try assumption.
           now left.
        * { apply IHvl.
             - intros zl ob K4. apply (K1 zl ob). now right.
             - intros zl bkd b K4. apply (K2 zl bkd b). now right.
             - intros zl bkd b K4. apply (K3 zl bkd b). now right.
           }
Qed.

Lemma print_S__main :
(forall p a, suppL p a -> pReln_S_ p (print_S a) a)
/\
(forall al, suppLL al -> pReln_N (print_SL al) al /\ match al with LCons a bl => pReln_S_ 1023 (print_S a) a /\ pReln_N (print_SL bl) bl | LNil => True end)
.
Proof.
  apply suppL_mutind.
  - intros q x Hx. simpl. apply pReln_S__Nam; try assumption.
  - intros q b n m. simpl. apply pReln_S__Num_S'_. apply pReln_S'__Empty.
  - intros q x a c Hq Hx H1 IH1 H2 IH2. simpl.
     apply (pReln_S_Let_U_ q x (print_S a) a (print_S c) c); try assumption; try omega.
  - intros q x bkd b a c Hq Hx H1 IH1 H2 IH2 H3 IH3. simpl.
     apply pReln_S_Let_T_; try assumption; try omega.
     reflexivity.
  - intros q x mtok vl a Hx H0 H0' H1 IH1 H2 IH2. simpl.
     + destruct vl.
        * (** This is an unusual case in which the binder was given no variables to bind. It still works, but I could rule it out. ***)
           simpl. apply (pReln_S_Binder_T_ q x mtok nil nil (print_S a) a); try assumption.
           apply pReln_TVs_Nil.
        * { destruct vl.
 (*** Case with 1 list of bvars, so no need for parens. ***)
             - destruct p as [yl [[bkd b]|]].
                + (*** Case with type b for the vars. ***)
                   destruct yl as [|y yl]. (*** Artificial case split to make the match reduce. ***)
                   * { apply (pReln_S_Binder_UT_ q x (AscKindTok bkd) bkd mtok (map NAM nil) nil (print_S b) b (print_S a) a); try assumption.
                        - reflexivity.
                        - apply pReln_Names_map. apply (H0' nil (Some (bkd,b))). now left.
                        - apply (IH1 nil) with (akd := bkd). now left.
                      }
                   * { apply (pReln_S_Binder_UT_ q x (AscKindTok bkd) bkd mtok (map NAM (y::yl)) (y::yl) (print_S b) b (print_S a) a); try assumption.
                        - reflexivity.
                        - apply pReln_Names_map. apply (H0' (y::yl) (Some (bkd,b))). now left.
                        - apply (IH1 (y::yl)) with (akd := bkd). now left.
                      }
                + (*** Case with no type given for the vars. ***)
                   destruct yl as [|y yl]. (*** If no vars are given, then use T instead of U. Otherwise U and T would have a conflicting case. ***)
                   * { generalize (pReln_S_Binder_T_ q x mtok [LPAREN;RPAREN] [(nil,None)] (print_S a) a).
                        simpl. intros G. apply G.
                        - omega.
                        - assumption.
                        - generalize (pReln_TVs_UNames_TVs nil nil nil nil). simpl. intros G'. apply G'.
                           + apply pReln_Names_Nil.
                           + apply pReln_TVs_Nil.
                        - assumption.
                      }
                   * { generalize (pReln_S_Binder_U_ q x mtok (NAM y :: map NAM yl) y yl). simpl.
                        intros G. apply G.
                        - omega.
                        - assumption.
                        - change (pReln_Names (map NAM (y :: yl)) (y :: yl)).
                           apply pReln_Names_map. apply (H0' (y :: yl) None). now left.
                        - assumption.
                      }
             - (*** Case with several separated lists of vars, some of which may be ascribed different types. ***)
                destruct p. destruct o as [[bkd b]|].
                + assert (L1:(pReln_S_ q
     match l with
     | nil =>
         NAM x
         :: flat_map
              (fun xlob : list string * option (AscKind * LTree) =>
               let (xl, ob) := xlob in
               LPAREN
               :: map NAM xl ++
                  match ob with
                  | Some (bkd,b) => AscKindTok bkd :: print_S b ++ [RPAREN]
                  | None => [RPAREN]
                  end) ((l, Some (bkd,b)) :: p0 :: vl) ++ 
            BinderMidTok mtok :: print_S a
     | _ :: _ =>
         NAM x
         :: flat_map
              (fun xlob : list string * option (AscKind * LTree) =>
               let (xl, ob) := xlob in
               LPAREN
               :: map NAM xl ++
                  match ob with
                  | Some (bkd,b) => AscKindTok bkd :: print_S b ++ [RPAREN]
                  | None => [RPAREN]
                  end) ((l, Some (bkd,b)) :: p0 :: vl) ++ 
            BinderMidTok mtok :: print_S a
     end (Binder x mtok ((l, Some (bkd,b)) :: p0 :: vl) a)) =
pReln_S_ q
     (NAM x
         :: flat_map
              (fun xlob : list string * option (AscKind * LTree) =>
               let (xl, ob) := xlob in
               LPAREN
               :: map NAM xl ++
                  match ob with
                  | Some (bkd,b) => AscKindTok bkd :: print_S b ++ [RPAREN]
                  | None => [RPAREN]
                  end) ((l, Some (bkd,b)) :: p0 :: vl) ++ 
            BinderMidTok mtok :: print_S a)
     (Binder x mtok ((l, Some (bkd,b)) :: p0 :: vl) a)).
                {
                  destruct l; reflexivity.
                }
                rewrite L1.
                simpl. apply (pReln_S_Binder_T_ q x mtok
                                      (LPAREN:: ((map NAM l ++ AscKindTok bkd :: print_S b ++ [RPAREN]) ++
                                        (let (xl, ob) := p0 in
                                          LPAREN
                                          :: map NAM xl ++
                                          match ob with
                                            | Some (bkd0,b0) => AscKindTok bkd0 :: print_S b0 ++ [RPAREN]
                                            | None => [RPAREN]
                                          end) ++
                                        flat_map
                                        (fun xlob : list string * option (AscKind * LTree) =>
                                          let (xl, ob) := xlob in
                                            LPAREN
                                            :: map NAM xl ++
                                            match ob with
                                              | Some (bkd0,b0) => AscKindTok bkd0 :: print_S b0 ++ [RPAREN]
                                              | None => [RPAREN]
                                            end) vl))
                                      ((l, Some (bkd,b)) :: p0 :: vl)
                                      (print_S a) a); try assumption.
                   rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl.
                   apply (pReln_TVs_TNames_TVs (AscKindTok bkd) bkd (map NAM l) l (print_S b) b).
                   * reflexivity.
                   * { apply pReln_Names_map. intros y Hy.
                        apply (H0' l (Some (bkd,b))).
                        - now left.
                        - assumption.
                      }
                   * apply (IH1 l bkd b). now left.
                   * { destruct p0. destruct o as [[ckd c]|].
                        - simpl. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl.
                           apply (pReln_TVs_TNames_TVs (AscKindTok ckd) ckd (map NAM l0) l0 (print_S c) c).
                           + reflexivity.
                           + apply pReln_Names_map. intros y Hy.
                              apply (H0' l0 (Some (ckd,c))); try assumption.
                              right. now left.
                           + apply (IH1 l0 ckd c). right. now left.
                           + apply print_S_Bindvars.
                              * intros zl ob K1. apply (H0' zl ob). right. now right.
                              * intros zl dkd d K1. apply (H1 zl dkd d). right. now right.
                              * intros zl dkd d K1. apply (IH1 zl dkd d). right. now right.
                        - simpl. rewrite <- app_assoc. simpl.
                           apply (pReln_TVs_UNames_TVs (map NAM l0) l0).
                           + apply pReln_Names_map. intros y Hy.
                              apply (H0' l0 None); try assumption.
                              right. now left.
                           + apply print_S_Bindvars.
                              * intros zl ob K1. apply (H0' zl ob). right. now right.
                              * intros zl dkd d K1. apply (H1 zl dkd d). right. now right.
                              * intros zl dkd d K1. apply (IH1 zl dkd d). right. now right.
                     }
                + assert (L1:(match l with
     | nil =>
         NAM x
         :: flat_map
              (fun xlob : list string * option (AscKind * LTree) =>
               let (xl, ob) := xlob in
               LPAREN
               :: map NAM xl ++
                  match ob with
                  | Some (bkd,b) => AscKindTok bkd :: print_S b ++ [RPAREN]
                  | None => [RPAREN]
                  end) ((l, None) :: p0 :: vl) ++ BinderMidTok mtok :: print_S a
     | _ :: _ =>
         NAM x
         :: flat_map
              (fun xlob : list string * option (AscKind * LTree) =>
               let (xl, ob) := xlob in
               LPAREN
               :: map NAM xl ++
                  match ob with
                  | Some (bkd,b) => AscKindTok bkd :: print_S b ++ [RPAREN]
                  | None => [RPAREN]
                  end) ((l, None) :: p0 :: vl) ++ BinderMidTok mtok :: print_S a
     end
                = (NAM x
                  :: flat_map
              (fun xlob : list string * option (AscKind * LTree) =>
               let (xl, ob) := xlob in
               LPAREN
               :: map NAM xl ++
                  match ob with
                  | Some (bkd,b) => AscKindTok bkd :: print_S b ++ [RPAREN]
                  | None => [RPAREN]
                  end) ((l, None) :: p0 :: vl) ++ BinderMidTok mtok :: print_S a))).
                   {
                     destruct l; reflexivity.
                   }
                   rewrite L1.
                   simpl. apply (pReln_S_Binder_T_ q x mtok
                                      (LPAREN:: ((map NAM l ++ [RPAREN]) ++
                                        (let (xl, ob) := p0 in
                                          LPAREN
                                          :: map NAM xl ++
                                          match ob with
                                            | Some (bkd,b) => AscKindTok bkd :: print_S b ++ [RPAREN]
                                            | None => [RPAREN]
                                          end) ++
                                        flat_map
                                        (fun xlob : list string * option (AscKind * LTree) =>
                                          let (xl, ob) := xlob in
                                            LPAREN
                                            :: map NAM xl ++
                                            match ob with
                                              | Some (bkd,b) => AscKindTok bkd :: print_S b ++ [RPAREN]
                                              | None => [RPAREN]
                                            end) vl))
                                      ((l, None) :: p0 :: vl)
                                      (print_S a) a); try assumption.
                   simpl. rewrite <- app_assoc. simpl.
                   apply (pReln_TVs_UNames_TVs (map NAM l) l).
                   * { apply pReln_Names_map. intros y Hy.
                        apply (H0' l None).
                        - now left.
                        - assumption.
                      }
                   * { destruct p0. destruct o as [[bkd b]|].
                        - simpl. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl.
                           apply (pReln_TVs_TNames_TVs (AscKindTok bkd) bkd (map NAM l0) l0 (print_S b) b).
                           + reflexivity.
                           + apply pReln_Names_map. intros y Hy.
                              apply (H0' l0 (Some (bkd,b))); try assumption.
                              right. now left.
                           + apply (IH1 l0 bkd b). right. now left.
                           + apply print_S_Bindvars.
                              * intros zl ob K1. apply (H0' zl ob). right. now right.
                              * intros zl dkd d K1. apply (H1 zl dkd d). right. now right.
                              * intros zl dkd d K1. apply (IH1 zl dkd d). right. now right.
                        - simpl. rewrite <- app_assoc. simpl.
                           apply (pReln_TVs_UNames_TVs (map NAM l0) l0).
                           + apply pReln_Names_map. intros y Hy.
                              apply (H0' l0 None); try assumption.
                              right. now left.
                           + apply print_S_Bindvars.
                              * intros zl ob K1. apply (H0' zl ob). right. now right.
                              * intros zl dkd d K1. apply (H1 zl dkd d). right. now right.
                              * intros zl dkd d K1. apply (IH1 zl dkd d). right. now right.
                     }
            }
  - intros q x p a Hx Hpq H1 IH1. simpl.
        apply pReln_S__Preop with (p := p); try assumption; try omega.
  - intros q x p a Hx Hpq H1 IH1 NB. simpl.
        apply (pReln_S_S_leq (S p)); try omega.
        apply pReln_S__S'__app with (q := (S p)) (a := a); try assumption; try omega.
        * { unfold S'__endp. destruct p; try tauto. revert Hx. unfold postinfop_info.
             case_eq (penv x).
             intros [op' [[p'' k]|]]; try tauto; try discriminate.
             intros omtok' K1 K2. inversion K2.
             destruct op'; destruct (le_gt_dec (S p) (S p)) as [Hpp|Hpp]; try tauto; omega.
           }
        * intros [z IR]. generalize (penv_InfixRight_Postop _ _ _ _ IR Hx). tauto.
        * apply pReln_S'__Postop with (p := p); try assumption; omega.
  - intros q x p a b Hx Hpq H1 IH1 H2 IH2 NB. simpl.
        apply (pReln_S_S_leq (S p)); try omega.
        apply (pReln_S__S'__app (S p) (print_S a) a (NAM x :: print_S b)); try assumption; try omega.
        * revert IH1. apply pReln_S_S_leq. omega.
        * { unfold S'__endp. destruct p; try tauto. revert Hx. unfold postinfop_info.
             case_eq (penv x).
             intros [op' [[p'' k]|]]; try tauto; try discriminate.
             intros omtok' K1 K2. inversion K2.
             destruct op'; destruct (le_gt_dec (S p) (S p)) as [Hpp|Hpp]; try tauto; omega.
           }
        * intros [z IR]. generalize (penv_InfixRight_InfixNone _ _ _ _ IR Hx). tauto.
        * apply pReln_S'__InfixNone with (p := p); try assumption. omega.
  - intros q x p a b Hx Hpq H1 IH1 H2 IH2 NB. simpl.
        apply (pReln_S_S_leq (S p)); try omega.
        apply (pReln_S__S'__app (S p) (print_S a) a (NAM x :: print_S b)); try assumption; try omega.
        * { unfold S'__endp. destruct p; try tauto. revert Hx. unfold postinfop_info.
             case_eq (penv x).
             intros [op' [[p'' k]|]]; try tauto; try discriminate.
             intros omtok' K1 K2. inversion K2.
             destruct op'; destruct (le_gt_dec (S p) (S p)) as [Hpp|Hpp]; try tauto; omega.
           }
        * intros [z IR]. generalize (penv_InfixRight_InfixLeft _ _ _ _ IR Hx). tauto.
        * apply pReln_S'__InfixLeft with (p := p); try assumption. omega.
  - intros q x p a b Hx Hpq H1 IH1 H2 IH2 NB. simpl.
        apply (pReln_S_S_leq (S p)); try omega.
        apply pReln_S_InfixRight.
        * assumption.
        * apply IH1.
        * apply IH2.
        * assumption.
  - intros q x a b Hq H1 IH1 H2 IH2 NB. simpl.
        apply (pReln_S_S_leq 501); try omega.
        apply (pReln_S__S'__app 501 (print_S a) a (SetInfixTOK x :: print_S b)); try assumption; try omega.
        * apply (pReln_S_S_leq 500); try assumption; try omega.
        * unfold S'__endp. destruct x; simpl; destruct (le_gt_dec 500 500); try tauto; omega.
        * intros [z IR]. generalize (penv_InfixRight_not500 _ _ IR). tauto.
        * { case_eq (Binderishp b); intros Hb.
             - apply pReln_S'__SetInfix_B; try reflexivity; try assumption; try omega.
             - generalize (pReln_S'__SetInfix_S'_ a 501 x (SetInfixTOK x) (print_S b) b nil).
                rewrite <- app_nil_end. intros G. apply G; try reflexivity; try assumption; try omega.
                apply pReln_S'__Empty.
           }
  - intros [|q] a b Hq H1 IH1 H2 IH2 NB; try omega.
        simpl. apply (pReln_S_S_leq 1); try omega.
        apply (pReln_S__S'__app 1) with (a := a); try assumption; try omega.
        * apply S'__endp_0.
        * intros [z IR]. generalize (penv_PostInfop_nonzero _ _ _ IR). tauto.
        * { generalize (pReln_S'__Implicit_S'_ a 1 (print_S b) b nil). rewrite <- app_nil_end.
             intros G. apply G; try assumption; try omega.
             apply pReln_S'__Empty.
           }
  - intros q x i a b Hx H1 IH1 H2 IH2. simpl.
     apply (pReln_S_Sep_S'_ q x i (SetInfixTOK i) (print_S a) a (print_S b) b nil (SepL x i a b)); try assumption.
     + reflexivity.
     + apply pReln_S'__Empty.
  - intros q x i a b Hx H1 IH1 Ka H2 IH2. simpl.
     apply (pReln_S_Rep_S'_ q x i (SetInfixTOK i) (print_S a) a (print_S b) b nil (RepL x i a b)); try assumption.
     + reflexivity.
     + apply pReln_S'__Empty.
  - intros q x i a b c Hx H1 IH1 Ka H2 IH2 H3 IH3. simpl.
     apply (pReln_S_SepRep_S'_ q x i (SetInfixTOK i) (print_S a) a (print_S b) b (print_S c) c nil (SepRepL x i a b c)); try assumption.
     + reflexivity.
     + apply pReln_S'__Empty.
  - intros q cl H1 IH1. simpl. destruct cl as [|a bl].
     + apply pReln_S_SetEmpty_S'_. apply pReln_S'__Empty.
     + destruct IH1 as [_ [IH1a IH1bl]].
        apply pReln_S_SetEnum_S'_ with (a := a) (bl := bl); try assumption.
        apply pReln_S'__Empty.
  - intros q a bl H1 IH1 H2 [IH2 _].
     simpl. apply pReln_S_MTuple_S'_ with (a := a) (bl := bl).
     + assumption.
     + assumption.
     + apply pReln_S'__Empty.
  - intros q a bl H1 IH1 H2 [IH2 _]. simpl.
     now apply (pReln_S__Paren_Tuple q (print_S a) (print_SL bl) a bl).
  - intros q a b c Hq H1 IH1 H2 IH2 H3 IH3. simpl.
     now apply (pReln_S_IfThenElse_ q (print_S a) a (print_S b) b (print_S c) c).
  - split; try tauto. simpl. apply pReln_N_Nil.
  - intros a bl H1 IH1 H2 [IH2 _]. simpl. split.
     + now apply pReln_N_Cons.
     + split; assumption.
Qed.

Lemma print_S__thm (p : nat) (a : LTree) : suppL p a -> forall q, p <= q -> pReln_S_ q (print_S a) a.

Proof.
  intros H1 q H2. apply print_S__main; try assumption. revert H2. now apply suppL_leq.
Qed.

Fixpoint parse_Names (tl : list TOKEN) : list string * list TOKEN :=
match tl with
    | (NAM x::tr) =>
    match penv x with
      | (None,None,None) =>
        match parse_Names tr with
          | (yl,tu) => (x::yl,tu)
        end
      | _ => ([],tl)
    end
    | _ => ([],tl)
end.

Definition NAMORASCTOKb (tr : list TOKEN) : bool :=
match tr with
  | NAM x::_ => true
  | COLON::_ => true
  | MEM::_ => true
  | SUBEQ::_ => true
  | _ => false
end.

Definition parse_S'_Infix (q p pr:nat) (i:InfixOp) (a:LTree) (tl tr:list TOKEN)
 (fS' : nat -> LTree -> list TOKEN -> option (LTree * list TOKEN))
 (fS : nat -> list TOKEN -> option (LTree * list TOKEN)) : option (LTree * list TOKEN) :=
 if le_gt_dec q p
   then Some(a,tl)
   else
     match fS pr tr with
       | Some(b,ts) =>
         if (Binderishp b)
           then Some(Infop i a b,ts)
           else fS' q (Infop i a b) ts
       | None => None
     end.

Definition parse_TVs_ascr
 (xl:list string) (akd : AscKind) (ts : list TOKEN)
 (fS : list TOKEN -> option (LTree * list TOKEN))
 (fTVs : list TOKEN -> option ((list (list string * option (AscKind * LTree))) * (list TOKEN)))
 : option ((list (list string * option (AscKind * LTree))) * (list TOKEN)) :=
 match fS ts with
   | Some(b,RPAREN::tu) =>
     match fTVs tu with
       | Some(vll,tv) => Some((xl,Some (akd,b))::vll,tv)
       | _ => None
     end
   | _ => None
 end.

Definition parse_Binder_ascr 
 (x:string) (xl:list string) (tok:BinderMid) (akd:AscKind) (ts : list TOKEN)
 (fS : list TOKEN -> option (LTree * list TOKEN))
 : option (LTree * list TOKEN) :=
 match fS ts with
   | Some(b,tok1::tu) =>
     if (dec_eq_tok (BinderMidTok tok) tok1) then
       match fS tu with
         | Some(a,tv) => Some(Binder x tok [(xl,Some (akd,b))] a,tv)
         | None => None
       end
       else None
   | _ => None
 end.

Definition parse_Let_ascr
  (x:string) (akd:AscKind) (tr : list TOKEN)
  (fS : list TOKEN -> option (LTree * list TOKEN)) : option (LTree * list TOKEN) :=
  match fS tr with
    | Some(b,DEQ::ts) =>
      match fS ts with
        | Some(a,IN::tu) =>
          match fS tu with
            | Some(c,tv) => Some(LetL x (Some (akd,b)) a c,tv)
            | _ => None
          end
        | _ => None
      end
    | _ => None
  end.

Definition parse_S_SetBraces
 (q:nat) (tr:list TOKEN)
 (g:LTree -> LTree)
 (fS' : nat -> LTree -> list TOKEN -> option (LTree * list TOKEN))
 (fS : nat -> list TOKEN -> option (LTree * list TOKEN))
 (fN : list TOKEN -> option (LTreeL * list TOKEN)) : option (LTree * list TOKEN) :=
 match fS 1023 tr with
   | Some(Infop(InfSet i) (Nam x) a,VBAR::ts) => (*** Sep ***)
     match fS 1023 ts with
       | Some(b,RCBRACE::tu) => fS' q (g (SepL x i a b)) tu
       | _ => None
     end
   | Some(a,VBAR::NAM x::MEM::ts) => (*** Rep or SepRep ***)
     match fS 1023 ts with
       | Some(b,RCBRACE::tu) => fS' q (g (RepL x InfMem a b)) tu
       | Some(b,COMMA::tu) =>
         match fS 1023 (tsubl tr tu) with
           | Some(c,RCBRACE::tv) => fS' q (g (SepRepL x InfMem a b c)) tv
           | _ => None
         end
       | _ => None
     end
   | Some(a,VBAR::NAM x::SUBEQ::ts) => (*** Rep or SepRep ***)
     match fS 1023 ts with
       | Some(b,RCBRACE::tu) => fS' q (g (RepL x InfSubq a b)) tu
       | Some(b,COMMA::tu) =>
         match fS 1023 tu with
           | Some(c,RCBRACE::tv) => fS' q (g (SepRepL x InfSubq a b c)) tv
           | _ => None
         end
       | _ => None
     end
   | Some(a,ts) => (*** Finally, assume it's a SetEnum (in which case ts starts with , or }) ***)
     match fN ts with
       | Some(bl,RCBRACE::tu) =>
         fS' q (g (SetEnumL (LCons a bl))) tu
       | _ => None
     end
   | _ => None
 end.

Fixpoint parse_S'_ (q:nat) (a:LTree) (tl : list TOKEN) {struct tl} : option (LTree * list TOKEN) :=
  match q with
    | 0 => Some(a,tl)
    | S _ =>
      match tl with
        | (MEM::tr) =>
          parse_S'_Infix q 500 500 (InfSet InfMem) a tl tr (fun q a ts => parse_S'_ q a (tsubl tr ts)) (fun q ts => parse_S_ q (tsubl tr ts))
        | (SUBEQ::tr) =>
          parse_S'_Infix q 500 500 (InfSet InfSubq) a tl tr (fun q a ts => parse_S'_ q a (tsubl tr ts)) (fun q ts => parse_S_ q (tsubl tr ts))
        | (NAM x::tr) =>
          match penv x with
            | (_,Some (p,Postfix),_) =>
              if le_gt_dec q p
                then Some(a,tl)
                else
                  parse_S'_ q (Postop x a) tr
            | (_,Some (p,InfixNone),_) =>
              parse_S'_Infix q p p (InfNam x) a tl tr (fun q a ts => parse_S'_ q a (tsubl tr ts)) (fun q ts => parse_S_ q (tsubl tr ts))
            | (_,Some (p,InfixLeft),_) =>
              parse_S'_Infix q p p (InfNam x) a tl tr (fun q a ts => parse_S'_ q a (tsubl tr ts)) (fun q ts => parse_S_ q (tsubl tr ts))
            | (_,Some (p,InfixRight),_) =>
              parse_S'_Infix q p (S p) (InfNam x) a tl tr (fun q a ts => parse_S'_ q a (tsubl tr ts)) (fun q ts => parse_S_ q (tsubl tr ts))
            | (None,None,None) =>
              parse_S'_ q (ImplicitInfop a (Nam x)) tr
            | (_,_,_) => Some(a,tl)
          end
        | (NUM b n m::tr) => parse_S'_ q (ImplicitInfop a (Num b n m)) tr
        | LPAREN::tr =>
          match parse_S_ 1023 tr with
            | Some(b,ts) =>
              match parse_N (tsubl tr ts) with
                | Some(cl,RPAREN::tu) =>
                  parse_S'_ q (ImplicitInfop a (Paren b cl)) (tsubl tr tu)
                | _ => None
              end
            | _ => None
          end
        | LCBRACE::RCBRACE::tr =>
          parse_S'_ q (ImplicitInfop a (SetEnumL LNil)) tr
        | LCBRACE::tr =>
          parse_S_SetBraces q tr (fun b => (ImplicitInfop a b)) (fun q a ts => parse_S'_ q a (tsubl tr ts)) (fun q ts => parse_S_ q (tsubl tr ts)) (fun ts => parse_N (tsubl tr ts))
        | (LBRACK::tr) =>
          match parse_S_ 1023 tr with
            | Some(c,ts) =>
              match parse_N (tsubl tr ts) with
                | Some(bl,RBRACK::tu) =>
                  parse_S'_ q (ImplicitInfop a (MTupleL c bl)) (tsubl tr tu)
                | _ => None
              end
            | _ => None
          end
        | _ => Some(a,tl)
      end
  end
with parse_S_ (q : nat) (tl : list TOKEN) {struct tl} :=
  match tl with
    | (NAM x::tr) =>
      match penv x with
        | (None,None,None) => (*** Ordinary Name ***)
          parse_S'_ q (Nam x) tr
        | (Some p,_,_) => (*** Prefix Operator ***)
          if le_gt_dec q p
            then None
            else
              match parse_S_ (S p) tr with
                | Some(a,ts) =>
                  if (Binderishp a)
                    then Some(Preop x a,ts)
                    else parse_S'_ q (Preop x a) (tsubl tr ts)
                | None => None
              end
        | (_,_,Some tok) => (*** Binder ***)
          if NAMORASCTOKb tr then
              match parse_Names tr with
                | (xl,COLON::ts) =>
                  parse_Binder_ascr x xl tok AscTp ts (fun ts => parse_S_ 1010 (tsubl tr ts))
                | (xl,MEM::ts) =>
                  parse_Binder_ascr x xl tok AscSet ts (fun ts => parse_S_ 1010 (tsubl tr ts))
                | (xl,SUBEQ::ts) =>
                  parse_Binder_ascr x xl tok AscSubeq ts (fun ts => parse_S_ 1010 (tsubl tr ts))
                | (xl,tok1::ts) =>
                  if (dec_eq_tok (BinderMidTok tok) tok1) then
                    match parse_S_ 1010 (tsubl tr ts) with
                      | Some(a,tu) => Some(Binder x tok [(xl,None)] a,tu)
                      | None => None
                    end
                    else None
                | _ => None
              end
            else
              match parse_TVs tr with
                | Some(vll,tok1::ts) =>
                  if (dec_eq_tok (BinderMidTok tok) tok1) then
                    match parse_S_ 1010 (tsubl tr ts) with
                      | Some(a,tu) => Some(Binder x tok vll a,tu)
                      | None => None
                    end
                    else None
                | _ => None
              end
        | _ => None
      end
    | (LET::NAM x::DEQ::tr) =>
      match parse_S_ 1010 tr with
        | Some(a,IN::tu) =>
          match parse_S_ 1010 (tsubl tr tu) with
            | Some(c,tv) => Some(LetL x None a c,tv)
            | _ => None
          end
        | _ => None
      end
    | (LET::NAM x::COLON::tr) =>
      parse_Let_ascr x AscTp tr (fun ts => parse_S_ 1010 (tsubl tr ts))
    | (LET::NAM x::MEM::tr) =>
      parse_Let_ascr x AscSet tr (fun ts => parse_S_ 1010 (tsubl tr ts))
    | (LET::NAM x::SUBEQ::tr) =>
      parse_Let_ascr x AscSubeq tr (fun ts => parse_S_ 1010 (tsubl tr ts))
    | (LPAREN::tr) =>
      match parse_S_ 1023 tr with
        | Some(a,ts) =>
          match parse_N (tsubl tr ts) with
            | Some(bl,RPAREN::tu) =>
              parse_S'_ q (Paren a bl) (tsubl tr tu)
            | _ => None
          end
        | _ => None
      end
    | (NUM b n m::tr) =>
      parse_S'_ q (Num b n m) tr
    | (LBRACK::tr) =>
      match parse_S_ 1023 tr with
        | Some(a,ts) =>
          match parse_N (tsubl tr ts) with
            | Some(bl,RBRACK::tu) =>
              parse_S'_ q (MTupleL a bl) (tsubl tr tu)
            | _ => None
          end
        | _ => None
      end
    | (LCBRACE::RCBRACE::tr) => parse_S'_ q (SetEnumL LNil) tr
    | (LCBRACE::tr) => (*** A lot can happen here. It might be {a,..,b} (SetEnum) or {x :e a | b} (Sep) or {a | x :e b} (Rep) or {a | x :e b, c} (SepRep) ***)
      parse_S_SetBraces q tr (fun a => a) (fun q a ts => parse_S'_ q a (tsubl tr ts)) (fun q ts => parse_S_ q (tsubl tr ts)) (fun ts => parse_N (tsubl tr ts))
    | (IF_::tr) =>
      match parse_S_ 1010 tr with
        | Some(a,THEN::ts) =>
          match parse_S_ 1010 (tsubl tr ts) with
            | Some(b,ELSE::tu) =>
              match parse_S_ 1010 (tsubl tr tu) with
                | Some(c,tv) => Some(IfThenElseL a b c,tv)
                | _ => None
              end
            | _ => None
          end
        | _ => None
      end
    | _ => None
  end
with parse_TVs (tl : list TOKEN) : option ((list (list string * option (AscKind * LTree))) * (list TOKEN)) :=
  match tl with
    | LPAREN::tr =>
      match parse_Names tr with
        | (xl,RPAREN::ts) =>
          match parse_TVs (tsubl tr ts) with
            | Some(vll,tu) => Some((xl,None)::vll,tu)
            | _ => None
          end
        | (xl,COLON::ts) =>
          parse_TVs_ascr xl AscTp ts (fun ts => parse_S_ 1010 (tsubl tr ts)) (fun tu => parse_TVs (tsubl tr tu))
        | (xl,MEM::ts) =>
          parse_TVs_ascr xl AscSet ts (fun ts => parse_S_ 1010 (tsubl tr ts)) (fun tu => parse_TVs (tsubl tr tu))
        | (xl,SUBEQ::ts) =>
          parse_TVs_ascr xl AscSubeq ts (fun ts => parse_S_ 1010 (tsubl tr ts)) (fun tu => parse_TVs (tsubl tr tu))
        | _ => None
      end
    | _ => Some(nil,tl)
  end
with parse_N (tl : list TOKEN) : option (LTreeL * (list TOKEN)) :=
  match tl with
    | COMMA::tr =>
      match parse_S_ 1023 tr with
        | Some(a,ts) =>
          match parse_N (tsubl tr ts) with
            | Some(bl,tu) => Some(LCons a bl,tu)
            | None => None
          end
        | None => None
      end
    | _ => Some(LNil,tl)
  end.

Definition NAMp (tr : list TOKEN) : Prop :=
match tr with
  | (NAM x::_) => nam_p x
  | _ => False
end.

Lemma parse_Names_lem (tl : list TOKEN) (xl : list string) :
 pReln_Names tl xl -> forall tr, ~NAMp tr -> parse_Names (tl ++ tr) = (xl,tr).
Proof.
  intros H. induction H.
  - intros tr H1. simpl. destruct tr; try reflexivity. destruct t; try reflexivity.
     simpl. case_eq (penv s).
     intros [[p|] [[q k]|]] [mtok|] E; try reflexivity.
     exfalso. apply H1. simpl. unfold nam_p. rewrite E. exact I.
  - intros tr H1. simpl. revert H. unfold nam_p. case_eq (penv x).
     intros [[p|] [[q k]|]] [mtok|] E; try tauto.
     intros _. 
     rewrite (IHpReln_Names tr H1). reflexivity.
Qed.

Definition LPARENp (tr : list TOKEN) : Prop :=
match tr with
  | (LPAREN::_) => True
  | _ => False
end.

Definition COMMAp (tr : list TOKEN) : Prop :=
match tr with
  | (COMMA::_) => True
  | _ => False
end.

Lemma pReln_S'_0 tl a c : pReln_S'_ 0 tl a c -> tl = nil /\ a = c.
Proof.
  intros H. inversion H; try omega. split; reflexivity.
Qed.

Lemma pReln_S_0_notBinderishp tl a : pReln_S_ 0 tl a -> Binderishp a = false.
Proof.
  intros H. inversion H; try omega.
  - apply pReln_S'_0 in H1. destruct H1. subst a. simpl. reflexivity.
  - apply pReln_S'_0 in H0. destruct H0. subst a. simpl. reflexivity.
  - apply pReln_S'_0 in H2. destruct H2. subst a. simpl. reflexivity.
  - apply pReln_S'_0 in H4. destruct H4. subst a. simpl. reflexivity.
  - apply pReln_S'_0 in H5. destruct H5. subst a. simpl. reflexivity.
  - apply pReln_S'_0 in H6. destruct H6. subst a. simpl. reflexivity.
  - apply pReln_S'_0 in H0. destruct H0. subst a. simpl. reflexivity.
  - apply pReln_S'_0 in H2. destruct H2. subst a. simpl. reflexivity.
  - apply pReln_S'_0 in H2. destruct H2. subst a. simpl. reflexivity.
Qed.

Lemma parse_S'_0_eq tl a : parse_S'_ 0 a tl = Some(a,tl).
Proof.
  destruct tl; try reflexivity.
Qed.

Lemma parse_S'_end p tl a :
  S'__endp p tl -> parse_S'_ p a tl = Some(a,tl).
Proof.
  intros H. destruct tl; simpl.
  - destruct p; reflexivity.
  - destruct p; try reflexivity.
     destruct t; try reflexivity.
     + revert H. simpl. case_eq (penv s). intros [[p'|] [[q' k']|]] [mtok'|]; try tauto.
        * unfold parse_S'_Infix. destruct (le_gt_dec (S p) q') as [Hpq|Hpq]; try tauto. destruct k'; tauto.
        * unfold parse_S'_Infix. destruct (le_gt_dec (S p) q') as [Hpq|Hpq]; try tauto. destruct k'; tauto.
        * unfold parse_S'_Infix. destruct (le_gt_dec (S p) q') as [Hpq|Hpq]; try tauto. destruct k'; tauto.
        * unfold parse_S'_Infix. destruct (le_gt_dec (S p) q') as [Hpq|Hpq]; try tauto. destruct k'; tauto.
     + simpl in H. contradiction H.
     + simpl in H. contradiction H.
     + simpl in H. revert H. destruct (le_gt_dec (S p) 500) as [Hpq|Hpq]; try tauto. intros _.
        unfold parse_S'_Infix. destruct (le_gt_dec (S p) 500) as [HSpq|HSpq]; try tauto. omega.
     + simpl in H. revert H. destruct (le_gt_dec (S p) 500) as [Hpq|Hpq]; try tauto. intros _.
        unfold parse_S'_Infix. destruct (le_gt_dec (S p) 500) as [HSpq|HSpq]; try tauto. omega.
     + simpl in H. contradiction H.
     + simpl in H. contradiction H.
Qed.

Definition hardendp (tl:list TOKEN) : Prop :=
match tl with
| nil => True
| COLON::_ => True
| COMMA::_ => True
| DARR::_ => True
| RPAREN::_ => True
| IN::_ => True
| DEQ::_ => True
| VBAR::_ => True
| RCBRACE::_ => True
| RBRACK::_ => True
| THEN::_ => True
| ELSE::_ => True
| _ => False
end.

Lemma hardendp__S'__endp q tl : hardendp tl -> S'__endp q tl.
Proof.
  destruct tl; destruct q; simpl; try tauto; destruct t; try tauto.
Qed.
