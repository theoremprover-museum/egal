Require Export ParsePrintFull3a.

Opaque le_gt_dec.

(***
  These lemmas correspond to cases in the proof of parse_S_lem.
  I only created them because Coq (with Proof General) kept dying
  while I was trying to finish the proof. My hope is/was that
  separating out these cases as lemmas would prevent death.
 ***)
Lemma parse_S_lem_1 : forall (a : LTree) (q : nat),
   (forall (q' : nat) (tr : list TOKEN),
    q <= q' -> hardendp tr -> parse_S'_ q' a ([] ++ tr) = Some (a, tr)) /\
   (Binderishp a = false ->
    Binderishp a = false ->
    forall (q' : nat) (tr : list TOKEN),
    q <= q' -> S'__endp q' tr -> parse_S'_ q' a ([] ++ tr) = Some (a, tr)).
Proof.
  intros a q. split.
     + intros q' tr H1' Hr. simpl.
        destruct tr.
        * destruct q'; try reflexivity.
        * destruct t; try contradiction Hr; destruct q'; try reflexivity.
     + intros NBa Ba q' tr Hq' H1. simpl. (* S'_Empty *)
        destruct tr as [|tok tr].
        * simpl. destruct q'; reflexivity.
        * { simpl. destruct q'.
             - destruct tok; try reflexivity.
             - destruct tok; try reflexivity.
                + revert H1. unfold S'__endp.
                   case_eq (penv s); try reflexivity.
                   intros [op' [[q'' k']|]] ob; try tauto.
                   * unfold parse_S'_Infix. destruct (le_gt_dec (S q') q'') as [Hqq|Hqq]; destruct k'; destruct op'; try tauto.
                   * destruct op' as [p'|]; try tauto. destruct ob as [mtok'|]; try tauto.
                + simpl in H1. contradiction H1.
                + simpl in H1. unfold parse_S'_Infix. revert H1.
                   destruct (le_gt_dec (S q') 500); try tauto.
                + simpl in H1. unfold parse_S'_Infix. revert H1.
                   destruct (le_gt_dec (S q') 500); try tauto.
                + simpl in H1. unfold parse_S'_Infix. revert H1.
                   destruct (le_gt_dec (S q') 500); try tauto.
                + contradiction H1.
                + contradiction H1.
           }
Qed.

Lemma parse_S_lem_2 : 
   forall (a : LTree) (q : nat) (x : string) (p : nat) 
     (tl : list TOKEN) (c : LTree),
   postinfop_info x = Some (p, Postfix) ->
   p < q ->
   pReln_S'_ q tl (Postop x a) c ->
   (forall (q' : nat) (tr : list TOKEN),
    q <= q' ->
    hardendp tr -> parse_S'_ q' (Postop x a) (tl ++ tr) = Some (c, tr)) /\
   (Binderishp (Postop x a) = false ->
    Binderishp c = false ->
    forall (q' : nat) (tr : list TOKEN),
    q <= q' ->
    S'__endp q' tr -> parse_S'_ q' (Postop x a) (tl ++ tr) = Some (c, tr)) ->
   (forall (q' : nat) (tr : list TOKEN),
    q <= q' ->
    hardendp tr -> parse_S'_ q' a ((NAM x :: tl) ++ tr) = Some (c, tr)) /\
   (Binderishp a = false ->
    Binderishp c = false ->
    forall (q' : nat) (tr : list TOKEN),
    q <= q' ->
    S'__endp q' tr -> parse_S'_ q' a ((NAM x :: tl) ++ tr) = Some (c, tr)).
Proof.
  - intros a q x p tl c Hxp Hpq H1 [IH1a IH1b]. split. (* S'_Postop *)
     + intros q' tr Hq' Hr. simpl. destruct q'; try omega.
        revert Hxp. unfold postinfop_info.
        case_eq (penv x). intros [[p'|] [q''|]] ob; try discriminate.
        * intros _ K1. inversion K1. destruct (le_gt_dec (S q') p) as [Hqp|Hqp]; try omega.
           apply IH1a; try assumption.
        * intros _ K1. inversion K1. destruct (le_gt_dec (S q') p) as [Hqp|Hqp]; try omega.
           apply IH1a; try assumption.
     + intros NBa NBc [|q'] Hq' tr Hr; try (exfalso; omega).
        simpl.
        revert Hxp. unfold postinfop_info.
        case_eq (penv x). intros [[p'|] [q''|]] ob; try discriminate.
        * intros _ H2. inversion H2.
           destruct (le_gt_dec (S q') p); try omega.
           now rewrite IH1b.
        * intros _ H2. inversion H2.
           destruct (le_gt_dec (S q') p); try omega.
           now rewrite IH1b.
Qed.

Lemma parse_S_lem_3 : 
   forall (a : LTree) (q : nat) (x : string) (p : nat) 
     (tl : list TOKEN) (b : LTree) (tr : list TOKEN) 
     (c : LTree),
   postinfop_info x = Some (p, InfixNone) ->
   p < q ->
   pReln_S_ p tl b ->
   (forall (q' : nat) (tr0 : list TOKEN),
    p <= q' -> hardendp tr0 -> parse_S_ q' (tl ++ tr0) = Some (b, tr0)) /\
   (Binderishp b = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    p <= q' -> S'__endp q' tr0 -> parse_S_ q' (tl ++ tr0) = Some (b, tr0)) /\
   (p = 0 ->
    forall (tr0 : list TOKEN) (q0 : nat) (b0 d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b0 b) tr0 = Some (d, tu) ->
    parse_S'_ q0 b0 (tl ++ tr0) = Some (d, tu)) ->
   Binderishp b = false ->
   S'__endp p tr ->
   pReln_S'_ q tr (Infop (InfNam x) a b) c ->
   (forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    hardendp tr0 ->
    parse_S'_ q' (Infop (InfNam x) a b) (tr ++ tr0) = Some (c, tr0)) /\
   (Binderishp (Infop (InfNam x) a b) = false ->
    Binderishp c = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    S'__endp q' tr0 ->
    parse_S'_ q' (Infop (InfNam x) a b) (tr ++ tr0) = Some (c, tr0)) ->
   (forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    hardendp tr0 ->
    parse_S'_ q' a ((NAM x :: tl ++ tr) ++ tr0) = Some (c, tr0)) /\
   (Binderishp a = false ->
    Binderishp c = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    S'__endp q' tr0 ->
    parse_S'_ q' a ((NAM x :: tl ++ tr) ++ tr0) = Some (c, tr0)).
Proof.
  - intros a q x p tl b tr c Hxp Hpq H1 [IH1a [IH1b IH1c]] NBb Hr H2 [IH2a IH2b]. split. (* S'_InfixNone_S' *)
     + intros q' ts H1' Hs.
        simpl. destruct q'; try omega.
        revert Hxp. unfold postinfop_info.
        case_eq (penv x). intros [[p'|] o'] ob K1 K2; subst o'.
        * { unfold parse_S'_Infix. destruct (le_gt_dec (S q') p); try omega.
             rewrite tsubl_ref.
             rewrite <- app_assoc.
             rewrite (IH1b NBb p (tr ++ ts)).
             + rewrite NBb. rewrite tsubl_app_eq.
                apply IH2a; try assumption.
             + omega.
             + apply S'__endp_app; try assumption. now apply hardendp__S'__endp.
           }
        * { unfold parse_S'_Infix. destruct (le_gt_dec (S q') p); try omega.
             rewrite tsubl_ref.
             rewrite <- app_assoc.
             rewrite (IH1b NBb p (tr ++ ts)).
             + rewrite NBb. rewrite tsubl_app_eq.
                apply IH2a; try assumption.
             + omega.
             + apply S'__endp_app; try assumption. revert Hs. apply hardendp__S'__endp.
           }
     + intros NBa NBc q' ts Hq' Hs.
        simpl. destruct q'; try omega.
        revert Hxp. unfold postinfop_info.
        case_eq (penv x). intros [[p'|] o'] ob K1 K2; subst o'.
        * { unfold parse_S'_Infix. destruct (le_gt_dec (S q') p); try omega.
             rewrite tsubl_ref.
             rewrite <- app_assoc.
             rewrite (IH1b NBb p (tr ++ ts)).
             + rewrite NBb. rewrite tsubl_app_eq.
                apply IH2b; try assumption.
             + omega.
             + apply S'__endp_app; try assumption. revert Hs. apply S'__endp_leq. omega.
           }
        * { unfold parse_S'_Infix. destruct (le_gt_dec (S q') p); try omega.
             rewrite tsubl_ref.
             rewrite <- app_assoc.
             rewrite (IH1b NBb p (tr ++ ts)).
             + rewrite NBb. rewrite tsubl_app_eq.
                apply IH2b; try assumption.
             + omega.
             + apply S'__endp_app; try assumption. revert Hs. apply S'__endp_leq. omega.
           }
Qed.

Lemma parse_S_lem_4 :
   forall (a : LTree) (q : nat) (x : string) (p : nat) 
     (tl : list TOKEN) (b : LTree) (tr : list TOKEN) 
     (c : LTree),
   postinfop_info x = Some (p, InfixLeft) ->
   p < q ->
   pReln_S_ p tl b ->
   (forall (q' : nat) (tr0 : list TOKEN),
    p <= q' -> hardendp tr0 -> parse_S_ q' (tl ++ tr0) = Some (b, tr0)) /\
   (Binderishp b = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    p <= q' -> S'__endp q' tr0 -> parse_S_ q' (tl ++ tr0) = Some (b, tr0)) /\
   (p = 0 ->
    forall (tr0 : list TOKEN) (q0 : nat) (b0 d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b0 b) tr0 = Some (d, tu) ->
    parse_S'_ q0 b0 (tl ++ tr0) = Some (d, tu)) ->
   Binderishp b = false ->
   S'__endp p tr ->
   pReln_S'_ q tr (Infop (InfNam x) a b) c ->
   (forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    hardendp tr0 ->
    parse_S'_ q' (Infop (InfNam x) a b) (tr ++ tr0) = Some (c, tr0)) /\
   (Binderishp (Infop (InfNam x) a b) = false ->
    Binderishp c = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    S'__endp q' tr0 ->
    parse_S'_ q' (Infop (InfNam x) a b) (tr ++ tr0) = Some (c, tr0)) ->
   (forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    hardendp tr0 ->
    parse_S'_ q' a ((NAM x :: tl ++ tr) ++ tr0) = Some (c, tr0)) /\
   (Binderishp a = false ->
    Binderishp c = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    S'__endp q' tr0 ->
    parse_S'_ q' a ((NAM x :: tl ++ tr) ++ tr0) = Some (c, tr0)).
Proof.
  - intros a q x p tl b tr c Hxp Hpq H1 [IH1a [IH1b IH1c]] NBb Hr H2 [IH2a IH2b]. split. (* S'_InfixLeft_S' *)
     + intros q' ts H1' Hs.
        simpl. destruct q'; try omega.
        revert Hxp. unfold postinfop_info.
        case_eq (penv x). intros [[p'|] o'] ob K1 K2; subst o'.
        * { unfold parse_S'_Infix. destruct (le_gt_dec (S q') p); try omega.
             rewrite tsubl_ref.
             rewrite <- app_assoc.
             rewrite (IH1b NBb p (tr ++ ts)).
             + rewrite NBb. rewrite tsubl_app_eq.
                apply IH2a; try assumption.
             + omega.
             + apply S'__endp_app; try assumption. now apply hardendp__S'__endp.
           }
        * { unfold parse_S'_Infix. destruct (le_gt_dec (S q') p); try omega.
             rewrite tsubl_ref.
             rewrite <- app_assoc.
             rewrite (IH1b NBb p (tr ++ ts)).
             + rewrite NBb. rewrite tsubl_app_eq.
                apply IH2a; try assumption.
             + omega.
             + apply S'__endp_app; try assumption. revert Hs. apply hardendp__S'__endp.
           }
     + intros NBa NBc q' ts Hq' Hs.
        simpl. destruct q'; try omega.
        revert Hxp. unfold postinfop_info.
        case_eq (penv x). intros [[p'|] o'] ob K1 K2; subst o'.
        * { unfold parse_S'_Infix. destruct (le_gt_dec (S q') p); try omega.
             rewrite tsubl_ref.
             rewrite <- app_assoc.
             rewrite (IH1b NBb p (tr ++ ts)).
             + rewrite NBb. rewrite tsubl_app_eq.
                apply IH2b; try assumption.
             + omega.
             + apply S'__endp_app; try assumption. revert Hs. apply S'__endp_leq. omega.
           }
        * { unfold parse_S'_Infix. destruct (le_gt_dec (S q') p); try omega.
             rewrite tsubl_ref.
             rewrite <- app_assoc.
             rewrite (IH1b NBb p (tr ++ ts)).
             + rewrite NBb. rewrite tsubl_app_eq.
                apply IH2b; try assumption.
             + omega.
             + apply S'__endp_app; try assumption. revert Hs. apply S'__endp_leq. omega.
           }
Qed.

Lemma parse_S_lem_5 :
   forall (a : LTree) (q : nat) (x : string) (p : nat) 
     (tl : list TOKEN) (b : LTree) (tr : list TOKEN) 
     (c : LTree),
   postinfop_info x = Some (p, InfixRight) ->
   p < q ->
   pReln_S_ (S p) tl b ->
   (forall (q' : nat) (tr0 : list TOKEN),
    S p <= q' -> hardendp tr0 -> parse_S_ q' (tl ++ tr0) = Some (b, tr0)) /\
   (Binderishp b = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    S p <= q' -> S'__endp q' tr0 -> parse_S_ q' (tl ++ tr0) = Some (b, tr0)) /\
   (S p = 0 ->
    forall (tr0 : list TOKEN) (q0 : nat) (b0 d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b0 b) tr0 = Some (d, tu) ->
    parse_S'_ q0 b0 (tl ++ tr0) = Some (d, tu)) ->
   Binderishp b = false ->
   S'__endp (S p) tr ->
   pReln_S'_ q tr (Infop (InfNam x) a b) c ->
   (forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    hardendp tr0 ->
    parse_S'_ q' (Infop (InfNam x) a b) (tr ++ tr0) = Some (c, tr0)) /\
   (Binderishp (Infop (InfNam x) a b) = false ->
    Binderishp c = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    S'__endp q' tr0 ->
    parse_S'_ q' (Infop (InfNam x) a b) (tr ++ tr0) = Some (c, tr0)) ->
   (forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    hardendp tr0 ->
    parse_S'_ q' a ((NAM x :: tl ++ tr) ++ tr0) = Some (c, tr0)) /\
   (Binderishp a = false ->
    Binderishp c = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    S'__endp q' tr0 ->
    parse_S'_ q' a ((NAM x :: tl ++ tr) ++ tr0) = Some (c, tr0)).
Proof.
  - intros a q x p tl b tr c Hxp Hpq H1 [IH1a [IH1b IH1c]] NBb Hr H2 [IH2a IH2b]. split. (* S'_InfixRight_S' *)
     + intros q' ts H1' Hs.
        simpl. destruct q'; try omega.
        revert Hxp. unfold postinfop_info.
        case_eq (penv x). intros [[p'|] o'] ob K1 K2; subst o'.
        * { unfold parse_S'_Infix. destruct (le_gt_dec (S q') p); try omega.
             rewrite tsubl_ref.
             rewrite <- app_assoc.
             rewrite (IH1b NBb (S p) (tr ++ ts)).
             + rewrite NBb. rewrite tsubl_app_eq.
                apply IH2a; try assumption.
             + omega.
             + apply S'__endp_app; try assumption. now apply hardendp__S'__endp.
           }
        * { unfold parse_S'_Infix. destruct (le_gt_dec (S q') p); try omega.
             rewrite tsubl_ref.
             rewrite <- app_assoc.
             rewrite (IH1b NBb (S p) (tr ++ ts)).
             + rewrite NBb. rewrite tsubl_app_eq.
                apply IH2a; try assumption.
             + omega.
             + apply S'__endp_app; try assumption. revert Hs. apply hardendp__S'__endp.
           }
     + intros NBa NBc q' ts Hq' Hs.
        simpl. destruct q'; try omega.
        revert Hxp. unfold postinfop_info.
        case_eq (penv x). intros [[p'|] o'] ob K1 K2; subst o'.
        * { unfold parse_S'_Infix. destruct (le_gt_dec (S q') p); try omega.
             rewrite tsubl_ref.
             rewrite <- app_assoc.
             rewrite (IH1b NBb (S p) (tr ++ ts)).
             + rewrite NBb. rewrite tsubl_app_eq.
                apply IH2b; try assumption.
             + omega.
             + apply S'__endp_app; try assumption. revert Hs. apply S'__endp_leq. omega.
           }
        * { unfold parse_S'_Infix. destruct (le_gt_dec (S q') p); try omega.
             rewrite tsubl_ref.
             rewrite <- app_assoc.
             rewrite (IH1b NBb (S p) (tr ++ ts)).
             + rewrite NBb. rewrite tsubl_app_eq.
                apply IH2b; try assumption.
             + omega.
             + apply S'__endp_app; try assumption. revert Hs. apply S'__endp_leq. omega.
           }
Qed.

Lemma parse_S_lem_6 :
   forall (a : LTree) (q : nat) (x : string) (p : nat) 
     (tl : list TOKEN) (b : LTree),
   postinfop_info x = Some (p, InfixNone) ->
   p < q ->
   pReln_S_ p tl b ->
   (forall (q' : nat) (tr : list TOKEN),
    p <= q' -> hardendp tr -> parse_S_ q' (tl ++ tr) = Some (b, tr)) /\
   (Binderishp b = false ->
    forall (q' : nat) (tr : list TOKEN),
    p <= q' -> S'__endp q' tr -> parse_S_ q' (tl ++ tr) = Some (b, tr)) /\
   (p = 0 ->
    forall (tr : list TOKEN) (q0 : nat) (b0 d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b0 b) tr = Some (d, tu) ->
    parse_S'_ q0 b0 (tl ++ tr) = Some (d, tu)) ->
   Binderishp b = true ->
   (forall (q' : nat) (tr : list TOKEN),
    q <= q' ->
    hardendp tr ->
    parse_S'_ q' a ((NAM x :: tl) ++ tr) = Some (Infop (InfNam x) a b, tr)) /\
   (Binderishp a = false ->
    Binderishp (Infop (InfNam x) a b) = false ->
    forall (q' : nat) (tr : list TOKEN),
    q <= q' ->
    S'__endp q' tr ->
    parse_S'_ q' a ((NAM x :: tl) ++ tr) = Some (Infop (InfNam x) a b, tr)).
Proof.
  - intros a q x p tl b Hxp Hpq H1 [IH1a [IH1b IH1c]] Bb. split. (*** S'_InfixNone_B ***)
     + intros q' ts H1' Hs.
        simpl. destruct q'; try omega.
        revert Hxp. unfold postinfop_info.
        case_eq (penv x). intros [[p'|] o'] ob K1 K2; subst o'.
        * { unfold parse_S'_Infix. destruct (le_gt_dec (S q') p); try omega.
             rewrite tsubl_ref.
             rewrite IH1a.
             + rewrite Bb. reflexivity.
             + omega.
             + assumption.
           }
        * { unfold parse_S'_Infix. destruct (le_gt_dec (S q') p); try omega.
             rewrite tsubl_ref.
             rewrite IH1a.
             + rewrite Bb. reflexivity.
             + omega.
             + assumption.
           }
     + intros NBa NBb. exfalso. simpl in NBb. rewrite Bb in NBb. discriminate.
Qed.

Lemma parse_S_lem_7 :
   forall (a : LTree) (q : nat) (x : string) (p : nat) 
     (tl : list TOKEN) (b : LTree),
   postinfop_info x = Some (p, InfixLeft) ->
   p < q ->
   pReln_S_ p tl b ->
   (forall (q' : nat) (tr : list TOKEN),
    p <= q' -> hardendp tr -> parse_S_ q' (tl ++ tr) = Some (b, tr)) /\
   (Binderishp b = false ->
    forall (q' : nat) (tr : list TOKEN),
    p <= q' -> S'__endp q' tr -> parse_S_ q' (tl ++ tr) = Some (b, tr)) /\
   (p = 0 ->
    forall (tr : list TOKEN) (q0 : nat) (b0 d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b0 b) tr = Some (d, tu) ->
    parse_S'_ q0 b0 (tl ++ tr) = Some (d, tu)) ->
   Binderishp b = true ->
   (forall (q' : nat) (tr : list TOKEN),
    q <= q' ->
    hardendp tr ->
    parse_S'_ q' a ((NAM x :: tl) ++ tr) = Some (Infop (InfNam x) a b, tr)) /\
   (Binderishp a = false ->
    Binderishp (Infop (InfNam x) a b) = false ->
    forall (q' : nat) (tr : list TOKEN),
    q <= q' ->
    S'__endp q' tr ->
    parse_S'_ q' a ((NAM x :: tl) ++ tr) = Some (Infop (InfNam x) a b, tr)).
Proof.
  - intros a q x p tl b Hxp Hpq H1 [IH1a [IH1b IH1c]] Bb. split. (*** S'_InfixLeft_B ***)
     + intros q' ts H1' Hs.
        simpl. destruct q'; try omega.
        revert Hxp. unfold postinfop_info.
        case_eq (penv x). intros [[p'|] o'] ob K1 K2; subst o'.
        * { unfold parse_S'_Infix. destruct (le_gt_dec (S q') p); try omega.
             rewrite tsubl_ref.
             rewrite IH1a.
             + rewrite Bb. reflexivity.
             + omega.
             + assumption.
           }
        * { unfold parse_S'_Infix. destruct (le_gt_dec (S q') p); try omega.
             rewrite tsubl_ref.
             rewrite IH1a.
             + rewrite Bb. reflexivity.
             + omega.
             + assumption.
           }
     + intros NBa NBb. exfalso. simpl in NBb. rewrite Bb in NBb. discriminate.
Qed.

Lemma parse_S_lem_8 :
   forall (a : LTree) (q : nat) (x : string) (p : nat) 
     (tl : list TOKEN) (b : LTree),
   postinfop_info x = Some (p, InfixRight) ->
   p < q ->
   pReln_S_ (S p) tl b ->
   (forall (q' : nat) (tr : list TOKEN),
    S p <= q' -> hardendp tr -> parse_S_ q' (tl ++ tr) = Some (b, tr)) /\
   (Binderishp b = false ->
    forall (q' : nat) (tr : list TOKEN),
    S p <= q' -> S'__endp q' tr -> parse_S_ q' (tl ++ tr) = Some (b, tr)) /\
   (S p = 0 ->
    forall (tr : list TOKEN) (q0 : nat) (b0 d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b0 b) tr = Some (d, tu) ->
    parse_S'_ q0 b0 (tl ++ tr) = Some (d, tu)) ->
   Binderishp b = true ->
   (forall (q' : nat) (tr : list TOKEN),
    q <= q' ->
    hardendp tr ->
    parse_S'_ q' a ((NAM x :: tl) ++ tr) = Some (Infop (InfNam x) a b, tr)) /\
   (Binderishp a = false ->
    Binderishp (Infop (InfNam x) a b) = false ->
    forall (q' : nat) (tr : list TOKEN),
    q <= q' ->
    S'__endp q' tr ->
    parse_S'_ q' a ((NAM x :: tl) ++ tr) = Some (Infop (InfNam x) a b, tr)).
Proof.
  - intros a q x p tl b Hxp Hpq H1 [IH1a [IH1b IH1c]] Bb. split. (*** S'_InfixRight_B ***)
     + intros q' ts H1' Hs.
        simpl. destruct q'; try omega.
        revert Hxp. unfold postinfop_info.
        case_eq (penv x). intros [[p'|] o'] ob K1 K2; subst o'.
        * { unfold parse_S'_Infix. destruct (le_gt_dec (S q') p); try omega.
             rewrite tsubl_ref.
             rewrite IH1a.
             + rewrite Bb. reflexivity.
             + omega.
             + assumption.
           }
        * { unfold parse_S'_Infix. destruct (le_gt_dec (S q') p); try omega.
             rewrite tsubl_ref.
             rewrite IH1a.
             + rewrite Bb. reflexivity.
             + omega.
             + assumption.
           }
     + intros NBa NBb. exfalso. simpl in NBb. rewrite Bb in NBb. discriminate.
Qed.

Lemma parse_S_lem_9 :
   forall (a : LTree) (q : nat) (x : SetInfixOp) (itok : TOKEN)
     (tl : list TOKEN) (b : LTree) (tr : list TOKEN) 
     (c : LTree),
   itok = SetInfixTOK x ->
   500 < q ->
   pReln_S_ 500 tl b ->
   (forall (q' : nat) (tr0 : list TOKEN),
    500 <= q' -> hardendp tr0 -> parse_S_ q' (tl ++ tr0) = Some (b, tr0)) /\
   (Binderishp b = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    500 <= q' -> S'__endp q' tr0 -> parse_S_ q' (tl ++ tr0) = Some (b, tr0)) /\
   (500 = 0 ->
    forall (tr0 : list TOKEN) (q0 : nat) (b0 d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b0 b) tr0 = Some (d, tu) ->
    parse_S'_ q0 b0 (tl ++ tr0) = Some (d, tu)) ->
   Binderishp b = false ->
   S'__endp 500 tr ->
   pReln_S'_ q tr (Infop (InfSet x) a b) c ->
   (forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    hardendp tr0 ->
    parse_S'_ q' (Infop (InfSet x) a b) (tr ++ tr0) = Some (c, tr0)) /\
   (Binderishp (Infop (InfSet x) a b) = false ->
    Binderishp c = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    S'__endp q' tr0 ->
    parse_S'_ q' (Infop (InfSet x) a b) (tr ++ tr0) = Some (c, tr0)) ->
   (forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    hardendp tr0 ->
    parse_S'_ q' a ((itok :: tl ++ tr) ++ tr0) = Some (c, tr0)) /\
   (Binderishp a = false ->
    Binderishp c = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    S'__endp q' tr0 ->
    parse_S'_ q' a ((itok :: tl ++ tr) ++ tr0) = Some (c, tr0)).
Proof.
  - intros a q [|] itok tl b tr c Hix Hq H1 [IH1a [IH1b IH1c]] NBb Hr H2 [IH2a IH2b]; simpl; subst itok; split. (*** S'_SetInfix_S'_ ***)
     + intros q' ts Hq' Hs. destruct q'; try (exfalso; omega); simpl.
        unfold parse_S'_Infix. destruct (le_gt_dec (S q') 500); try (exfalso; omega).
        rewrite tsubl_ref. rewrite <- app_assoc.
        rewrite IH1b.
        * rewrite NBb. rewrite tsubl_app_eq. now apply IH2a.
        * assumption.
        * omega.
        * apply S'__endp_app; try assumption. now apply hardendp__S'__endp.
     + intros NBa NBc q' ts Hq' Hs. destruct q'; try (exfalso; omega). simpl.
        unfold parse_S'_Infix. destruct (le_gt_dec (S q') 500); try (exfalso; omega).
        rewrite tsubl_ref. rewrite <- app_assoc.
        rewrite IH1b.
        * rewrite NBb. rewrite tsubl_app_eq. now apply IH2b.
        * assumption.
        * omega.
        * apply S'__endp_app; try assumption. revert Hs. apply S'__endp_leq. omega.
     + intros q' ts Hq' Hs. destruct q'; try (exfalso; omega); simpl.
        unfold parse_S'_Infix. destruct (le_gt_dec (S q') 500); try (exfalso; omega).
        rewrite tsubl_ref. rewrite <- app_assoc.
        rewrite IH1b.
        * rewrite NBb. rewrite tsubl_app_eq. now apply IH2a.
        * assumption.
        * omega.
        * apply S'__endp_app; try assumption. now apply hardendp__S'__endp.
     + intros NBa NBc q' ts Hq' Hs. destruct q'; try (exfalso; omega). simpl.
        unfold parse_S'_Infix. destruct (le_gt_dec (S q') 500); try (exfalso; omega).
        rewrite tsubl_ref. rewrite <- app_assoc.
        rewrite IH1b.
        * rewrite NBb. rewrite tsubl_app_eq. now apply IH2b.
        * assumption.
        * omega.
        * apply S'__endp_app; try assumption. revert Hs. apply S'__endp_leq. omega.
Qed.

Lemma parse_S_lem_10 :
   forall (a : LTree) (q : nat) (x : SetInfixOp) (itok : TOKEN)
     (tl : list TOKEN) (b : LTree),
   itok = SetInfixTOK x ->
   500 < q ->
   pReln_S_ 500 tl b ->
   (forall (q' : nat) (tr : list TOKEN),
    500 <= q' -> hardendp tr -> parse_S_ q' (tl ++ tr) = Some (b, tr)) /\
   (Binderishp b = false ->
    forall (q' : nat) (tr : list TOKEN),
    500 <= q' -> S'__endp q' tr -> parse_S_ q' (tl ++ tr) = Some (b, tr)) /\
   (500 = 0 ->
    forall (tr : list TOKEN) (q0 : nat) (b0 d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b0 b) tr = Some (d, tu) ->
    parse_S'_ q0 b0 (tl ++ tr) = Some (d, tu)) ->
   Binderishp b = true ->
   (forall (q' : nat) (tr : list TOKEN),
    q <= q' ->
    hardendp tr ->
    parse_S'_ q' a ((itok :: tl) ++ tr) = Some (Infop (InfSet x) a b, tr)) /\
   (Binderishp a = false ->
    Binderishp (Infop (InfSet x) a b) = false ->
    forall (q' : nat) (tr : list TOKEN),
    q <= q' ->
    S'__endp q' tr ->
    parse_S'_ q' a ((itok :: tl) ++ tr) = Some (Infop (InfSet x) a b, tr)).
Proof.
  - intros a q [|] itok tl b Hix Hq H1 [IH1a [IH1b IH1c]] Bb; simpl; subst itok; split. (*** S'_SetInfix_B ***)
     + intros q' ts Hq' Hs. destruct q'; try (exfalso; omega); simpl.
        unfold parse_S'_Infix. destruct (le_gt_dec (S q') 500); try (exfalso; omega).
        rewrite tsubl_ref.
        rewrite IH1a.
        * rewrite Bb. reflexivity.
        * omega.
        * assumption.
     + intros NBa NBb. exfalso. rewrite Bb in NBb. discriminate.
     + intros q' ts Hq' Hs. destruct q'; try (exfalso; omega); simpl.
        unfold parse_S'_Infix. destruct (le_gt_dec (S q') 500); try (exfalso; omega).
        rewrite tsubl_ref.
        rewrite IH1a.
        * rewrite Bb. reflexivity.
        * omega.
        * assumption.
     + intros NBa NBb. exfalso. rewrite Bb in NBb. discriminate.
Qed.

Lemma parse_S_lem_11 :
   forall (a : LTree) (q : nat) (tl : list TOKEN) (b : LTree)
     (tr : list TOKEN) (c : LTree),
   q > 0 ->
   pReln_S_ 0 tl b ->
   (forall (q' : nat) (tr0 : list TOKEN),
    0 <= q' -> hardendp tr0 -> parse_S_ q' (tl ++ tr0) = Some (b, tr0)) /\
   (Binderishp b = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    0 <= q' -> S'__endp q' tr0 -> parse_S_ q' (tl ++ tr0) = Some (b, tr0)) /\
   (0 = 0 ->
    forall (tr0 : list TOKEN) (q0 : nat) (b0 d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b0 b) tr0 = Some (d, tu) ->
    parse_S'_ q0 b0 (tl ++ tr0) = Some (d, tu)) ->
   pReln_S'_ q tr (ImplicitInfop a b) c ->
   (forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    hardendp tr0 ->
    parse_S'_ q' (ImplicitInfop a b) (tr ++ tr0) = Some (c, tr0)) /\
   (Binderishp (ImplicitInfop a b) = false ->
    Binderishp c = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    S'__endp q' tr0 ->
    parse_S'_ q' (ImplicitInfop a b) (tr ++ tr0) = Some (c, tr0)) ->
   (forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    hardendp tr0 -> parse_S'_ q' a ((tl ++ tr) ++ tr0) = Some (c, tr0)) /\
   (Binderishp a = false ->
    Binderishp c = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    S'__endp q' tr0 -> parse_S'_ q' a ((tl ++ tr) ++ tr0) = Some (c, tr0)).
Proof.
  - intros a q tl b tr c Hq H1 [IH1a [IH1b IH1c]] H2 [IH2a IH2b]. split. (*** S'__Implicit ***)
     + intros q' ts Hq' Hr. rewrite <- app_assoc.
        apply IH1c; try omega.
        apply IH2a.
        * assumption.
        * assumption.
     + intros NBa NBc q' ts Hq' Hs.
        assert (L1:Binderishp b = false).
        { 
          apply pReln_S_0_notBinderishp in H1. assumption.
        }
        rewrite <- app_assoc.
        assert (L2:parse_S_ 0 (tl ++ tr ++ ts) = Some (b, tr ++ ts)).
        {
          apply (IH1b L1 0 (tr ++ ts)).
          - omega.
          - exact I.
        }
        generalize (IH2b (eq_refl false) NBc q' ts Hq' Hs).
        apply (IH1c (eq_refl 0) (tr ++ ts) q' a c ts). omega.
Qed.

Lemma parse_S_lem_12 :
   forall (q : nat) (x : string) (tl : list TOKEN) (c : LTree),
   nam_p x ->
   pReln_S'_ q tl (Nam x) c ->
   (forall (q' : nat) (tr : list TOKEN),
    q <= q' -> hardendp tr -> parse_S'_ q' (Nam x) (tl ++ tr) = Some (c, tr)) /\
   (Binderishp (Nam x) = false ->
    Binderishp c = false ->
    forall (q' : nat) (tr : list TOKEN),
    q <= q' ->
    S'__endp q' tr -> parse_S'_ q' (Nam x) (tl ++ tr) = Some (c, tr)) ->
   (forall (q' : nat) (tr : list TOKEN),
    q <= q' ->
    hardendp tr -> parse_S_ q' ((NAM x :: tl) ++ tr) = Some (c, tr)) /\
   (Binderishp c = false ->
    forall (q' : nat) (tr : list TOKEN),
    q <= q' ->
    S'__endp q' tr -> parse_S_ q' ((NAM x :: tl) ++ tr) = Some (c, tr)) /\
   (q = 0 ->
    forall (tr : list TOKEN) (q0 : nat) (b d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b c) tr = Some (d, tu) ->
    parse_S'_ q0 b ((NAM x :: tl) ++ tr) = Some (d, tu)).
Proof.
  - intros q x tl c Hx H1 [IH1a IH1b]. repeat split. (*** S_Nam ***)
     + intros q' tr Hq' Hr. revert Hx. unfold nam_p. simpl.
        case_eq (penv x). intros [[p'|] [[q'' k']|]] [mtok'|]; try tauto.
        intros _ _. apply IH1a; try assumption.
     + intros NBc q' tr Hq'. revert Hx. unfold nam_p. simpl.
        case_eq (penv x). intros [[p'|] [[q'' k']|]] [mtok'|]; try tauto.
        intros _ _. f_equal. apply IH1b; try assumption; try omega.
        reflexivity.
     + intros Hq0 tr q' b d tu Hq' K1. simpl. destruct q'; try omega.
        revert Hx. unfold nam_p. simpl.
        case_eq (penv x). intros [[p'|] [[q'' k']|]] [mtok'|]; try tauto.
        intros _ _. subst q. apply pReln_S'_0 in H1. destruct H1. subst tl. subst c. exact K1.
Qed.

Lemma parse_S_lem_13 :
   forall (q : nat) (b : bool) (n m : nat) (tl : list TOKEN) (c : LTree),
   pReln_S'_ q tl (Num b n m) c ->
   (forall (q' : nat) (tr : list TOKEN),
    q <= q' ->
    hardendp tr -> parse_S'_ q' (Num b n m) (tl ++ tr) = Some (c, tr)) /\
   (Binderishp (Num b n m) = false ->
    Binderishp c = false ->
    forall (q' : nat) (tr : list TOKEN),
    q <= q' ->
    S'__endp q' tr -> parse_S'_ q' (Num b n m) (tl ++ tr) = Some (c, tr)) ->
   (forall (q' : nat) (tr : list TOKEN),
    q <= q' ->
    hardendp tr -> parse_S_ q' ((NUM b n m :: tl) ++ tr) = Some (c, tr)) /\
   (Binderishp c = false ->
    forall (q' : nat) (tr : list TOKEN),
    q <= q' ->
    S'__endp q' tr -> parse_S_ q' ((NUM b n m :: tl) ++ tr) = Some (c, tr)) /\
   (q = 0 ->
    forall (tr : list TOKEN) (q0 : nat) (b0 d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b0 c) tr = Some (d, tu) ->
    parse_S'_ q0 b0 ((NUM b n m :: tl) ++ tr) = Some (d, tu)).
Proof.
  - intros q b n m tl c H1 [IH1a IH1b]. repeat split. (*** S_Num ***)
     + intros q' tr Hq' Hr. simpl. now apply IH1a.
     + intros NBc q' tr Hq' Hr. simpl. now apply IH1b.
     + intros Hq0 tr q' b' d tu Hq' K1. simpl. destruct q'; try omega.
        rewrite Hq0 in H1. apply pReln_S'_0 in H1. destruct H1. subst tl. subst c. exact K1.
Qed.

Lemma parse_S_lem_14 :
   forall (q : nat) (x : string) (p : nat) (tl : list TOKEN) (a : LTree),
   preop_priority x = Some p ->
   p < q ->
   pReln_S_ (S p) tl a ->
   (forall (q' : nat) (tr : list TOKEN),
    S p <= q' -> hardendp tr -> parse_S_ q' (tl ++ tr) = Some (a, tr)) /\
   (Binderishp a = false ->
    forall (q' : nat) (tr : list TOKEN),
    S p <= q' -> S'__endp q' tr -> parse_S_ q' (tl ++ tr) = Some (a, tr)) /\
   (S p = 0 ->
    forall (tr : list TOKEN) (q0 : nat) (b d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b a) tr = Some (d, tu) ->
    parse_S'_ q0 b (tl ++ tr) = Some (d, tu)) ->
   Binderishp a = true ->
   (forall (q' : nat) (tr : list TOKEN),
    q <= q' ->
    hardendp tr -> parse_S_ q' ((NAM x :: tl) ++ tr) = Some (Preop x a, tr)) /\
   (Binderishp (Preop x a) = false ->
    forall (q' : nat) (tr : list TOKEN),
    q <= q' ->
    S'__endp q' tr ->
    parse_S_ q' ((NAM x :: tl) ++ tr) = Some (Preop x a, tr)) /\
   (q = 0 ->
    forall (tr : list TOKEN) (q0 : nat) (b d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b (Preop x a)) tr = Some (d, tu) ->
    parse_S'_ q0 b ((NAM x :: tl) ++ tr) = Some (d, tu)).
Proof.
 - intros q x p tl a Hxp Hpq H1 [IH1a [IH1b _]] Ba. repeat split. (*** S_Preop_B ***)
   + intros q' tr Hq Hr. revert Hxp. unfold preop_priority. simpl.
      case_eq (penv x). intros [[p'|] oqk] omtok; try discriminate.
      intros K1 K2. inversion K2. destruct (le_gt_dec q' p) as [Hqp|Hqp]; try omega.
      rewrite IH1a.
      * rewrite Ba. reflexivity.
      * omega.
      * assumption.
   + intros NBa. exfalso. simpl in NBa. rewrite Ba in NBa. discriminate.
   + intros Hq. exfalso. omega.
Qed.

Lemma parse_S_lem_15 :
   forall (q : nat) (x : string) (p : nat) (tl : list TOKEN) 
     (a : LTree) (tr : list TOKEN) (c : LTree),
   preop_priority x = Some p ->
   p < q ->
   pReln_S_ (S p) tl a ->
   (forall (q' : nat) (tr0 : list TOKEN),
    S p <= q' -> hardendp tr0 -> parse_S_ q' (tl ++ tr0) = Some (a, tr0)) /\
   (Binderishp a = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    S p <= q' -> S'__endp q' tr0 -> parse_S_ q' (tl ++ tr0) = Some (a, tr0)) /\
   (S p = 0 ->
    forall (tr0 : list TOKEN) (q0 : nat) (b d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b a) tr0 = Some (d, tu) ->
    parse_S'_ q0 b (tl ++ tr0) = Some (d, tu)) ->
   Binderishp a = false ->
   S'__endp (S p) tr ->
   pReln_S'_ q tr (Preop x a) c ->
   (forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    hardendp tr0 -> parse_S'_ q' (Preop x a) (tr ++ tr0) = Some (c, tr0)) /\
   (Binderishp (Preop x a) = false ->
    Binderishp c = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    S'__endp q' tr0 -> parse_S'_ q' (Preop x a) (tr ++ tr0) = Some (c, tr0)) ->
   (forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    hardendp tr0 -> parse_S_ q' ((NAM x :: tl ++ tr) ++ tr0) = Some (c, tr0)) /\
   (Binderishp c = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    S'__endp q' tr0 ->
    parse_S_ q' ((NAM x :: tl ++ tr) ++ tr0) = Some (c, tr0)) /\
   (q = 0 ->
    forall (tr0 : list TOKEN) (q0 : nat) (b d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b c) tr0 = Some (d, tu) ->
    parse_S'_ q0 b ((NAM x :: tl ++ tr) ++ tr0) = Some (d, tu)).
Proof.
  intros q x p tl a tr c Hxp Hpq H1 [IH1a [IH1b _]] NBa Hr H2 [IH2a IH2b]. repeat split. (*** S_Preop_S' ***)
   + intros q' ts Hq Hs. revert Hxp. unfold preop_priority. simpl.
      case_eq (penv x). intros [[p'|] oqk] omtok; try discriminate.
      intros K1 K2. inversion K2. destruct (le_gt_dec q' p) as [Hqp|Hqp]; try omega.
      rewrite <- app_assoc.
      rewrite IH1b.
      * rewrite NBa. rewrite tsubl_app_eq. apply IH2a; try assumption.
      * assumption.
      * omega.
      * apply S'__endp_app; try assumption. now apply hardendp__S'__endp.
   + intros NBc q' ts Hq' Hs.
      revert Hxp. unfold preop_priority. simpl.
      case_eq (penv x). intros [[p'|] oqk] omtok; try discriminate.
      intros K1 K2. inversion K2. destruct (le_gt_dec q' p) as [Hqp|Hqp]; try omega.
      rewrite <- app_assoc.
      rewrite IH1b.
      * rewrite NBa. rewrite tsubl_app_eq. apply IH2b; try assumption.
      * assumption.
      * omega.
      * apply S'__endp_app; try assumption. revert Hs. apply S'__endp_leq. omega.
   + intros Hq. exfalso. omega.
Qed.

Lemma parse_S_lem_16 :
   forall (q : nat) (tl : list TOKEN) (a : LTree) (tlr : list TOKEN)
     (bl : LTreeL) (tr : list TOKEN) (c : LTree),
   pReln_S_ 1023 tl a ->
   (forall (q' : nat) (tr0 : list TOKEN),
    1023 <= q' -> hardendp tr0 -> parse_S_ q' (tl ++ tr0) = Some (a, tr0)) /\
   (Binderishp a = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    1023 <= q' -> S'__endp q' tr0 -> parse_S_ q' (tl ++ tr0) = Some (a, tr0)) /\
   (1023 = 0 ->
    forall (tr0 : list TOKEN) (q0 : nat) (b d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b a) tr0 = Some (d, tu) ->
    parse_S'_ q0 b (tl ++ tr0) = Some (d, tu)) ->
   pReln_N tlr bl ->
   (forall tr0 : list TOKEN,
    ~ COMMAp tr0 -> hardendp tr0 -> parse_N (tlr ++ tr0) = Some (bl, tr0)) ->
   pReln_S'_ q tr (Paren a bl) c ->
   (forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    hardendp tr0 -> parse_S'_ q' (Paren a bl) (tr ++ tr0) = Some (c, tr0)) /\
   (Binderishp (Paren a bl) = false ->
    Binderishp c = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    S'__endp q' tr0 -> parse_S'_ q' (Paren a bl) (tr ++ tr0) = Some (c, tr0)) ->
   (forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    hardendp tr0 ->
    parse_S_ q' ((LPAREN :: tl ++ tlr ++ RPAREN :: tr) ++ tr0) =
    Some (c, tr0)) /\
   (Binderishp c = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    S'__endp q' tr0 ->
    parse_S_ q' ((LPAREN :: tl ++ tlr ++ RPAREN :: tr) ++ tr0) =
    Some (c, tr0)) /\
   (q = 0 ->
    forall (tr0 : list TOKEN) (q0 : nat) (b d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b c) tr0 = Some (d, tu) ->
    parse_S'_ q0 b ((LPAREN :: tl ++ tlr ++ RPAREN :: tr) ++ tr0) =
    Some (d, tu)).
Proof.
 intros q tl a tlr bl tr c H1 [IH1a [IH1b IH1c]] H2 IH2 H3 [IH3a IH3b]. repeat split. (*** S_Paren/Tuple ***)
   + intros q' ts Hq' Hs. simpl.
      assert (IH1':parse_S_ 1023 (tl ++ (tlr ++ (RPAREN::tr ++ ts))) = Some(a,tlr ++ (RPAREN::tr ++ ts))).
      {
        apply IH1a.
        - omega.
        - inversion H2.
           + simpl. tauto.
           + simpl. tauto.
      }
      rewrite <- app_assoc. rewrite <- app_assoc. simpl. rewrite IH1'.
      rewrite tsubl_app_eq. rewrite IH2.
      * { rewrite subl_tsubl_eq.
           - now apply IH3a.
           - apply subl_app. apply subl_app. apply sublcons. apply sublref.
         }
      * simpl. tauto.
      * simpl. tauto.
   + intros NBc q' ts Hq' Hs.
      assert (IH1':parse_S_ 1023 (tl ++ (tlr ++ (RPAREN::tr ++ ts))) = Some(a,tlr ++ (RPAREN::tr ++ ts))).
      {
        apply IH1a.
        - omega.
        - inversion H2.
           + simpl. tauto.
           + simpl. tauto.
      }
      simpl. rewrite <- app_assoc. rewrite <- app_assoc. simpl. rewrite IH1'.
      rewrite tsubl_app_eq. rewrite IH2.
      * { rewrite subl_tsubl_eq.
           - apply IH3b; try assumption. simpl. reflexivity.
           - apply subl_app. apply subl_app. apply sublcons. apply sublref.
         }
      * simpl. tauto.
      * simpl. tauto.
   + intros Hq0 ts q' b d tu Hq' K1.
      subst q. apply pReln_S'_0 in H3. destruct H3. subst tr. subst c.
      assert (IH3':parse_S'_ q' (Paren a bl) (RPAREN::ts) = Some(Paren a bl, RPAREN::ts)).
      {
        apply IH3b; try assumption; try omega; try reflexivity.
        destruct q'; try omega. exact I.
      }
      simpl. destruct q'; try omega.
      assert (IH1':parse_S_ 1023 (tl ++ (tlr ++ (RPAREN::ts))) = Some(a,tlr ++ (RPAREN::ts))).
      {
        apply IH1a.
        - omega.
        - inversion H2.
           + simpl. tauto.
           + simpl. tauto.
      }
      rewrite <- app_assoc. rewrite <- app_assoc. simpl. rewrite IH1'.
      rewrite tsubl_app_eq. rewrite IH2.
      * { rewrite subl_tsubl_eq.
           - exact K1.
           - apply subl_app. apply subl_app. apply sublcons. apply sublref.
           }
      * simpl. tauto.
      * simpl. tauto.
Qed.

Opaque parse_TVs.

Lemma parse_S_lem_17 :
   forall (q : nat) (x : string) (mtok : BinderMid) (vtl : list TOKEN)
     (y : string) (yl : list string) (tl : list TOKEN) 
     (a : LTree),
   q > 0 ->
   binder_midtok x = Some mtok ->
   pReln_Names vtl (y :: yl) ->
   pReln_S_ 1010 tl a ->
   (forall (q' : nat) (tr : list TOKEN),
    1010 <= q' -> hardendp tr -> parse_S_ q' (tl ++ tr) = Some (a, tr)) /\
   (Binderishp a = false ->
    forall (q' : nat) (tr : list TOKEN),
    1010 <= q' -> S'__endp q' tr -> parse_S_ q' (tl ++ tr) = Some (a, tr)) /\
   (1010 = 0 ->
    forall (tr : list TOKEN) (q0 : nat) (b d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b a) tr = Some (d, tu) ->
    parse_S'_ q0 b (tl ++ tr) = Some (d, tu)) ->
   (forall (q' : nat) (tr : list TOKEN),
    q <= q' ->
    hardendp tr ->
    parse_S_ q' ((NAM x :: vtl ++ BinderMidTok mtok :: tl) ++ tr) =
    Some (Binder x mtok [(y :: yl, None)] a, tr)) /\
   (Binderishp (Binder x mtok [(y :: yl, None)] a) = false ->
    forall (q' : nat) (tr : list TOKEN),
    q <= q' ->
    S'__endp q' tr ->
    parse_S_ q' ((NAM x :: vtl ++ BinderMidTok mtok :: tl) ++ tr) =
    Some (Binder x mtok [(y :: yl, None)] a, tr)) /\
   (q = 0 ->
    forall (tr : list TOKEN) (q0 : nat) (b d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b (Binder x mtok [(y :: yl, None)] a)) tr =
    Some (d, tu) ->
    parse_S'_ q0 b ((NAM x :: vtl ++ BinderMidTok mtok :: tl) ++ tr) = Some (d, tu)).
Proof.
 - intros q x mtok vtl y yl tl a Hq Hxm H1 H2 [IH2a [IH2b IH2c]]. repeat split. (*** S_Binder_U ***)
    + intros q' tr Hq' Hr.
       generalize Hxm. unfold binder_midtok. simpl.
       case_eq (penv x). intros [[p'|] oqk] [mtok'|]; try discriminate.
       * intros K1. exfalso. apply (penv_Preop_Binder x x p' mtok); try assumption; try reflexivity.
          unfold preop_priority. rewrite K1. reflexivity.
       * { intros K1 K2. inversion K2. subst mtok'. rewrite <- app_assoc.
 (*** This is a ridiculously long assert. The problem is that I need to destruct oqk which results in this huge goal twice. I'm doing it once in this assert. I could define an auxiliary function to make this prettier. ***)
            assert (L1:((if NAMORASCTOKb (vtl ++ (BinderMidTok mtok :: tl) ++ tr)
       then
        let (xl, l) := parse_Names (vtl ++ (BinderMidTok mtok :: tl) ++ tr) in
        match l with
        | [] => None
        | NAM _ as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match parse_S_ 1010 (tsubl (vtl ++ (BinderMidTok mtok :: tl) ++ tr) ts) with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | NUM _ _ _ as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match parse_S_ 1010 (tsubl (vtl ++ ((BinderMidTok mtok) :: tl) ++ tr) ts) with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | LPAREN as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match parse_S_ 1010 (tsubl (vtl ++ ((BinderMidTok mtok) :: tl) ++ tr) ts) with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | RPAREN as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match parse_S_ 1010 (tsubl (vtl ++ ((BinderMidTok mtok) :: tl) ++ tr) ts) with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | COMMA as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match parse_S_ 1010 (tsubl (vtl ++ ((BinderMidTok mtok) :: tl) ++ tr) ts) with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | COLON :: ts =>
            parse_Binder_ascr x xl mtok AscTp ts
              (fun ts0 : list TOKEN =>
               parse_S_ 1010 (tsubl (vtl ++ ((BinderMidTok mtok) :: tl) ++ tr) ts0))
        | DARR as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match parse_S_ 1010 (tsubl (vtl ++ ((BinderMidTok mtok) :: tl) ++ tr) ts) with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | LET as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match parse_S_ 1010 (tsubl (vtl ++ ((BinderMidTok mtok) :: tl) ++ tr) ts) with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | DEQ as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match parse_S_ 1010 (tsubl (vtl ++ ((BinderMidTok mtok) :: tl) ++ tr) ts) with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | IN as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match parse_S_ 1010 (tsubl (vtl ++ ((BinderMidTok mtok) :: tl) ++ tr) ts) with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | MEM :: ts =>
            parse_Binder_ascr x xl mtok AscSet ts
              (fun ts0 : list TOKEN =>
               parse_S_ 1010 (tsubl (vtl ++ ((BinderMidTok mtok) :: tl) ++ tr) ts0))
        | SUBEQ :: ts =>
            parse_Binder_ascr x xl mtok AscSubeq ts
              (fun ts0 : list TOKEN =>
               parse_S_ 1010 (tsubl (vtl ++ ((BinderMidTok mtok) :: tl) ++ tr) ts0))
        | VBAR as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match parse_S_ 1010 (tsubl (vtl ++ ((BinderMidTok mtok) :: tl) ++ tr) ts) with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | LCBRACE as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match parse_S_ 1010 (tsubl (vtl ++ ((BinderMidTok mtok) :: tl) ++ tr) ts) with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | RCBRACE as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match parse_S_ 1010 (tsubl (vtl ++ ((BinderMidTok mtok) :: tl) ++ tr) ts) with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | LBRACK as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match parse_S_ 1010 (tsubl (vtl ++ ((BinderMidTok mtok) :: tl) ++ tr) ts) with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | RBRACK as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match parse_S_ 1010 (tsubl (vtl ++ ((BinderMidTok mtok) :: tl) ++ tr) ts) with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | IF_ as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match
               parse_S_ 1010
                 (tsubl (vtl ++ (BinderMidTok mtok :: tl) ++ tr) ts)
             with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | THEN as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match
               parse_S_ 1010
                 (tsubl (vtl ++ (BinderMidTok mtok :: tl) ++ tr) ts)
             with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | ELSE as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match
               parse_S_ 1010
                 (tsubl (vtl ++ (BinderMidTok mtok :: tl) ++ tr) ts)
             with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        end
       else
        match parse_TVs (vtl ++ ((BinderMidTok mtok) :: tl) ++ tr) with
        | Some (vll, []) => None
        | Some (vll, tok1 :: ts) =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match parse_S_ 1010 (tsubl (vtl ++ ((BinderMidTok mtok) :: tl) ++ tr) ts) with
             | Some (a0, tu) => Some (Binder x mtok vll a0, tu)
             | None => None
             end
            else None
        | None => None
        end) = Some (Binder x mtok [(y::yl, None)] a, tr))).
                      {
            destruct vtl.
            - inversion H1. (*** vtl empty is a contradiction in this case ***)
            - simpl. inversion H1. revert H3. unfold nam_p.
               intros J1. subst x0.
               assert (K5:penv y = (None,None,None)).
               {
                 revert H4. unfold nam_p. destruct (penv y) as [[[p''|] [[q''' k'']|]] [mtok''|]]; tauto.
               }
               rewrite K5.
               destruct mtok; simpl.
               + rewrite (parse_Names_lem _ _ H6 (COMMA::tl ++ tr) (fun H => H)).
                  rewrite subl_tsubl_eq.
                  * rewrite IH2a; try assumption; try omega. destruct oqk; reflexivity.
                  * apply sublcons. apply subl_app. apply sublcons. apply sublref.
               + rewrite (parse_Names_lem _ _ H6 (DARR::tl ++ tr) (fun H => H)).
                  rewrite subl_tsubl_eq.
                  * rewrite IH2a; try assumption; try omega. destruct oqk; reflexivity.
                  * apply sublcons. apply subl_app. apply sublcons. apply sublref.
            }
            rewrite L1. destruct oqk; reflexivity.
          }
    + intros NBa. simpl in NBa. discriminate.
    + intros Hq0. exfalso. omega.
Qed.

Lemma parse_S_lem_18 :
   forall (q : nat) (x : string) (atok : TOKEN) (akd : AscKind)
     (mtok : BinderMid) (vtl : list TOKEN) (vl : list string) 
     (tr : list TOKEN) (b : LTree) (tl : list TOKEN) 
     (a : LTree),
   q > 0 ->
   atok = AscKindTok akd ->
   binder_midtok x = Some mtok ->
   pReln_Names vtl vl ->
   pReln_S_ 1010 tr b ->
   (forall (q' : nat) (tr0 : list TOKEN),
    1010 <= q' -> hardendp tr0 -> parse_S_ q' (tr ++ tr0) = Some (b, tr0)) /\
   (Binderishp b = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    1010 <= q' -> S'__endp q' tr0 -> parse_S_ q' (tr ++ tr0) = Some (b, tr0)) /\
   (1010 = 0 ->
    forall (tr0 : list TOKEN) (q0 : nat) (b0 d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b0 b) tr0 = Some (d, tu) ->
    parse_S'_ q0 b0 (tr ++ tr0) = Some (d, tu)) ->
   pReln_S_ 1010 tl a ->
   (forall (q' : nat) (tr0 : list TOKEN),
    1010 <= q' -> hardendp tr0 -> parse_S_ q' (tl ++ tr0) = Some (a, tr0)) /\
   (Binderishp a = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    1010 <= q' -> S'__endp q' tr0 -> parse_S_ q' (tl ++ tr0) = Some (a, tr0)) /\
   (1010 = 0 ->
    forall (tr0 : list TOKEN) (q0 : nat) (b0 d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b0 a) tr0 = Some (d, tu) ->
    parse_S'_ q0 b0 (tl ++ tr0) = Some (d, tu)) ->
   (forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    hardendp tr0 ->
    parse_S_ q' ((NAM x :: vtl ++ atok :: tr ++ (BinderMidTok mtok) :: tl) ++ tr0) =
    Some (Binder x mtok [(vl, Some (akd, b))] a, tr0)) /\
   (Binderishp (Binder x mtok [(vl, Some (akd, b))] a) = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    S'__endp q' tr0 ->
    parse_S_ q' ((NAM x :: vtl ++ atok :: tr ++ (BinderMidTok mtok) :: tl) ++ tr0) =
    Some (Binder x mtok [(vl, Some (akd, b))] a, tr0)) /\
   (q = 0 ->
    forall (tr0 : list TOKEN) (q0 : nat) (b0 d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b0 (Binder x mtok [(vl, Some (akd, b))] a))
      tr0 = Some (d, tu) ->
    parse_S'_ q0 b0 ((NAM x :: vtl ++ atok :: tr ++ (BinderMidTok mtok) :: tl) ++ tr0) =
    Some (d, tu)).
Proof.
 - intros q x atok akd mtok vtl vl tl a tbr b Hq Hakd Hxm H1 H2 [IH2a [IH2b IH2c]] H3 [IH3a [IH3b IH3c]]. repeat split. (*** S_Binder_UT ***)
    + intros q' tr Hq' Hr.
       generalize Hxm. unfold binder_midtok. simpl.
       case_eq (penv x). intros [[p'|] oqk] [mtok'|]; try discriminate.
       * intros K1. exfalso. apply (penv_Preop_Binder x x p' mtok); try assumption; try reflexivity.
          unfold preop_priority. rewrite K1. reflexivity.
       * { intros K1 K2. inversion K2. subst mtok'. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl.
 (*** This is a ridiculously long assert. The problem is that I need to destruct oqk which results in this huge goal twice. I'm doing it once in this assert. I could define an auxiliary function to make this prettier. ***)
            assert (L1:((if NAMORASCTOKb (vtl ++ atok :: tl ++ BinderMidTok mtok :: tbr ++ tr)
       then
        let (xl, l) :=
            parse_Names (vtl ++ atok :: tl ++ (BinderMidTok mtok) :: tbr ++ tr) in
        match l with
        | [] => None
        | NAM _ as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match
               parse_S_ 1010
                 (tsubl (vtl ++ atok :: tl ++ (BinderMidTok mtok) :: tbr ++ tr) ts)
             with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | NUM _ _ _ as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match
               parse_S_ 1010
                 (tsubl (vtl ++ atok :: tl ++ (BinderMidTok mtok) :: tbr ++ tr) ts)
             with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | LPAREN as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match
               parse_S_ 1010
                 (tsubl (vtl ++ atok :: tl ++ (BinderMidTok mtok) :: tbr ++ tr) ts)
             with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | RPAREN as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match
               parse_S_ 1010
                 (tsubl (vtl ++ atok :: tl ++ (BinderMidTok mtok) :: tbr ++ tr) ts)
             with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | COMMA as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match
               parse_S_ 1010
                 (tsubl (vtl ++ atok :: tl ++ (BinderMidTok mtok) :: tbr ++ tr) ts)
             with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | COLON :: ts =>
            parse_Binder_ascr x xl mtok AscTp ts
              (fun ts0 : list TOKEN =>
               parse_S_ 1010
                 (tsubl (vtl ++ atok :: tl ++ (BinderMidTok mtok) :: tbr ++ tr) ts0))
        | DARR as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match
               parse_S_ 1010
                 (tsubl (vtl ++ atok :: tl ++ (BinderMidTok mtok) :: tbr ++ tr) ts)
             with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | LET as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match
               parse_S_ 1010
                 (tsubl (vtl ++ atok :: tl ++ (BinderMidTok mtok) :: tbr ++ tr) ts)
             with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | DEQ as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match
               parse_S_ 1010
                 (tsubl (vtl ++ atok :: tl ++ (BinderMidTok mtok) :: tbr ++ tr) ts)
             with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | IN as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match
               parse_S_ 1010
                 (tsubl (vtl ++ atok :: tl ++ (BinderMidTok mtok) :: tbr ++ tr) ts)
             with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | MEM :: ts =>
            parse_Binder_ascr x xl mtok AscSet ts
              (fun ts0 : list TOKEN =>
               parse_S_ 1010
                 (tsubl (vtl ++ atok :: tl ++ (BinderMidTok mtok) :: tbr ++ tr) ts0))
        | SUBEQ :: ts =>
            parse_Binder_ascr x xl mtok AscSubeq ts
              (fun ts0 : list TOKEN =>
               parse_S_ 1010
                 (tsubl (vtl ++ atok :: tl ++ (BinderMidTok mtok) :: tbr ++ tr) ts0))
        | VBAR as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match
               parse_S_ 1010
                 (tsubl (vtl ++ atok :: tl ++ (BinderMidTok mtok) :: tbr ++ tr) ts)
             with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | LCBRACE as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match
               parse_S_ 1010
                 (tsubl (vtl ++ atok :: tl ++ (BinderMidTok mtok) :: tbr ++ tr) ts)
             with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | RCBRACE as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match
               parse_S_ 1010
                 (tsubl (vtl ++ atok :: tl ++ (BinderMidTok mtok) :: tbr ++ tr) ts)
             with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | LBRACK as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match
               parse_S_ 1010
                 (tsubl (vtl ++ atok :: tl ++ (BinderMidTok mtok) :: tbr ++ tr) ts)
             with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | RBRACK as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match
               parse_S_ 1010
                 (tsubl (vtl ++ atok :: tl ++ (BinderMidTok mtok) :: tbr ++ tr) ts)
             with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | IF_ as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match
               parse_S_ 1010
                 (tsubl (vtl ++ atok :: tl ++ BinderMidTok mtok :: tbr ++ tr)
                    ts)
             with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | THEN as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match
               parse_S_ 1010
                 (tsubl (vtl ++ atok :: tl ++ BinderMidTok mtok :: tbr ++ tr)
                    ts)
             with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        | ELSE as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match
               parse_S_ 1010
                 (tsubl (vtl ++ atok :: tl ++ BinderMidTok mtok :: tbr ++ tr)
                    ts)
             with
             | Some (a0, tu) => Some (Binder x mtok [(xl, None)] a0, tu)
             | None => None
             end
            else None
        end
       else
        match parse_TVs (vtl ++ atok :: tl ++ (BinderMidTok mtok) :: tbr ++ tr) with
        | Some (vll, []) => None
        | Some (vll, tok1 :: ts) =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match
               parse_S_ 1010
                 (tsubl (vtl ++ atok :: tl ++ (BinderMidTok mtok) :: tbr ++ tr) ts)
             with
             | Some (a0, tu) => Some (Binder x mtok vll a0, tu)
             | None => None
             end
            else None
        | None => None
        end) = Some (Binder x mtok [(vl, Some (akd,a))] b, tr))).
                      {
            destruct vtl; simpl; destruct akd; subst atok; simpl.
            - unfold parse_Binder_ascr. rewrite tsubl_cons_eq. rewrite IH2a.
               + destruct (dec_eq_tok (BinderMidTok mtok) (BinderMidTok mtok)) as [K4|K4]; try tauto.
                  rewrite subl_tsubl_eq.
                  * { rewrite IH3a.
                       - inversion H1. reflexivity.
                       - omega.
                       - assumption.
                     }
                  * apply sublcons. apply subl_app. apply sublcons. apply sublref.
               + omega.
               + destruct mtok; simpl; tauto.
            - unfold parse_Binder_ascr. rewrite tsubl_cons_eq. rewrite IH2a.
               + destruct (dec_eq_tok (BinderMidTok mtok) (BinderMidTok mtok)) as [K4|K4]; try tauto.
                  rewrite subl_tsubl_eq.
                  * { rewrite IH3a.
                       - inversion H1. reflexivity.
                       - omega.
                       - assumption.
                     }
                  * apply sublcons. apply subl_app. apply sublcons. apply sublref.
               + omega.
               + destruct mtok; simpl; tauto.
            - unfold parse_Binder_ascr. rewrite tsubl_cons_eq. rewrite IH2a.
               + destruct (dec_eq_tok (BinderMidTok mtok) (BinderMidTok mtok)) as [K4|K4]; try tauto.
                  rewrite subl_tsubl_eq.
                  * { rewrite IH3a.
                       - inversion H1. reflexivity.
                       - omega.
                       - assumption.
                     }
                  * apply sublcons. apply subl_app. apply sublcons. apply sublref.
               + omega.
               + destruct mtok; simpl; tauto.
            - simpl. inversion H1. revert H4. unfold nam_p.
               case_eq (penv x0). intros [[p'|] [[q'' k']|]] [mtok'|]; try tauto.
               intros _ _. 
               destruct mtok; simpl.
               + rewrite (parse_Names_lem _ _ H6 (COLON::tl ++ COMMA :: tbr ++ tr) (fun H => H)).
                  unfold parse_Binder_ascr. rewrite subl_tsubl_eq.
                  * { rewrite IH2a.
                       - destruct (dec_eq_tok COMMA COMMA) as [K4|K4]; try tauto.
                          rewrite subl_tsubl_eq.
                          + rewrite IH3a; try reflexivity; try assumption.
                          + apply sublcons. apply subl_app. apply sublcons. apply subl_app. apply sublcons. apply sublref.
                       - omega.
                       - simpl. tauto.
                     }
                  * apply sublcons. apply subl_app. apply sublcons. apply sublref.
               + rewrite (parse_Names_lem _ _ H6 (COLON::tl ++ DARR :: tbr ++ tr) (fun H => H)).
                  unfold parse_Binder_ascr. rewrite subl_tsubl_eq.
                  * { rewrite IH2a.
                       - destruct (dec_eq_tok DARR DARR) as [K4|K4]; try tauto.
                          rewrite subl_tsubl_eq.
                          + rewrite IH3a; try reflexivity; try assumption.
                          + apply sublcons. apply subl_app. apply sublcons. apply subl_app. apply sublcons. apply sublref.
                       - omega.
                       - simpl. tauto.
                     }
                  * apply sublcons. apply subl_app. apply sublcons. apply sublref.
            - simpl. inversion H1. revert H4. unfold nam_p.
               case_eq (penv x0). intros [[p'|] [[q'' k']|]] [mtok'|]; try tauto.
               intros _ _. 
               destruct mtok; simpl.
               + rewrite (parse_Names_lem _ _ H6 (MEM::tl ++ COMMA :: tbr ++ tr) (fun H => H)).
                  unfold parse_Binder_ascr. rewrite subl_tsubl_eq.
                  * { rewrite IH2a.
                       - destruct (dec_eq_tok COMMA COMMA) as [K4|K4]; try tauto.
                          rewrite subl_tsubl_eq.
                          + rewrite IH3a; try reflexivity; try assumption.
                          + apply sublcons. apply subl_app. apply sublcons. apply subl_app. apply sublcons. apply sublref.
                       - omega.
                       - simpl. tauto.
                     }
                  * apply sublcons. apply subl_app. apply sublcons. apply sublref.
               + rewrite (parse_Names_lem _ _ H6 (MEM::tl ++ DARR :: tbr ++ tr) (fun H => H)).
                  unfold parse_Binder_ascr. rewrite subl_tsubl_eq.
                  * { rewrite IH2a.
                       - destruct (dec_eq_tok DARR DARR) as [K4|K4]; try tauto.
                          rewrite subl_tsubl_eq.
                          + rewrite IH3a; try reflexivity; try assumption.
                          + apply sublcons. apply subl_app. apply sublcons. apply subl_app. apply sublcons. apply sublref.
                       - omega.
                       - simpl. tauto.
                     }
                  * apply sublcons. apply subl_app. apply sublcons. apply sublref.
            - simpl. inversion H1. revert H4. unfold nam_p.
               case_eq (penv x0). intros [[p'|] [[q'' k']|]] [mtok'|]; try tauto.
               intros _ _. 
               destruct mtok; simpl.
               + rewrite (parse_Names_lem _ _ H6 (SUBEQ::tl ++ COMMA :: tbr ++ tr) (fun H => H)).
                  unfold parse_Binder_ascr. rewrite subl_tsubl_eq.
                  * { rewrite IH2a.
                       - destruct (dec_eq_tok COMMA COMMA) as [K4|K4]; try tauto.
                          rewrite subl_tsubl_eq.
                          + rewrite IH3a; try reflexivity; try assumption.
                          + apply sublcons. apply subl_app. apply sublcons. apply subl_app. apply sublcons. apply sublref.
                       - omega.
                       - simpl. tauto.
                     }
                  * apply sublcons. apply subl_app. apply sublcons. apply sublref.
               + rewrite (parse_Names_lem _ _ H6 (SUBEQ::tl ++ DARR :: tbr ++ tr) (fun H => H)).
                  unfold parse_Binder_ascr. rewrite subl_tsubl_eq.
                  * { rewrite IH2a.
                       - destruct (dec_eq_tok DARR DARR) as [K4|K4]; try tauto.
                          rewrite subl_tsubl_eq.
                          + rewrite IH3a; try reflexivity; try assumption.
                          + apply sublcons. apply subl_app. apply sublcons. apply subl_app. apply sublcons. apply sublref.
                       - omega.
                       - simpl. tauto.
                     }
                  * apply sublcons. apply subl_app. apply sublcons. apply sublref.
          }
          destruct oqk; exact L1.
        }
    + intros NBa. simpl in NBa. discriminate.
    + intros Hq0. exfalso. omega.
Qed.

