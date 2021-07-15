Require Export ParsePrintFull3a.

Opaque le_gt_dec.

Lemma parse_S_lem_20 :
   forall (q : nat) (x : string) (tl : list TOKEN) 
     (a : LTree) (tr : list TOKEN) (c : LTree),
   q > 0 ->
   nam_p x ->
   pReln_S_ 1010 tl a ->
   (forall (q' : nat) (tr0 : list TOKEN),
    1010 <= q' -> hardendp tr0 -> parse_S_ q' (tl ++ tr0) = Some (a, tr0)) /\
   (Binderishp a = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    1010 <= q' -> S'__endp q' tr0 -> parse_S_ q' (tl ++ tr0) = Some (a, tr0)) /\
   (1010 = 0 ->
    forall (tr0 : list TOKEN) (q0 : nat) (b d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b a) tr0 = Some (d, tu) ->
    parse_S'_ q0 b (tl ++ tr0) = Some (d, tu)) ->
   pReln_S_ 1010 tr c ->
   (forall (q' : nat) (tr0 : list TOKEN),
    1010 <= q' -> hardendp tr0 -> parse_S_ q' (tr ++ tr0) = Some (c, tr0)) /\
   (Binderishp c = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    1010 <= q' -> S'__endp q' tr0 -> parse_S_ q' (tr ++ tr0) = Some (c, tr0)) /\
   (1010 = 0 ->
    forall (tr0 : list TOKEN) (q0 : nat) (b d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b c) tr0 = Some (d, tu) ->
    parse_S'_ q0 b (tr ++ tr0) = Some (d, tu)) ->
   (forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    hardendp tr0 ->
    parse_S_ q' ((LET :: NAM x :: DEQ :: tl ++ IN :: tr) ++ tr0) =
    Some (LetL x None a c, tr0)) /\
   (Binderishp (LetL x None a c) = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    S'__endp q' tr0 ->
    parse_S_ q' ((LET :: NAM x :: DEQ :: tl ++ IN :: tr) ++ tr0) =
    Some (LetL x None a c, tr0)) /\
   (q = 0 ->
    forall (tr0 : list TOKEN) (q0 : nat) (b d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b (LetL x None a c)) tr0 = Some (d, tu) ->
    parse_S'_ q0 b ((LET :: NAM x :: DEQ :: tl ++ IN :: tr) ++ tr0) =
    Some (d, tu)).
Proof.
 - intros q x tl a tr c Hq Hx H1 [IH1a [IH1b IH1c]] H2 [IH2a [IH2b IH2c]]. repeat split. (*** S_Let_U ***)
    + intros q' ts Hq' Hs. simpl. rewrite <- app_assoc. rewrite IH1a.
       * { simpl. rewrite subl_tsubl_eq.
            - rewrite IH2a; try reflexivity. assumption.
            - apply subl_app. apply sublcons. apply sublref.
          }
       * omega.
       * simpl. tauto. (*** IN needs to be a hardendp ***)
    + intros NBl. exfalso. simpl in NBl. discriminate.
    + intros Hq0. exfalso. omega.
Qed.

Lemma parse_S_lem_21 :
   forall (q : nat) (x : string) (atok : TOKEN) (akd : AscKind)
     (tlb : list TOKEN) (b : LTree) (tl : list TOKEN) 
     (a : LTree) (tr : list TOKEN) (c : LTree),
   q > 0 ->
   atok = AscKindTok akd ->
   nam_p x ->
   pReln_S_ 1010 tlb b ->
   (forall (q' : nat) (tr0 : list TOKEN),
    1010 <= q' -> hardendp tr0 -> parse_S_ q' (tlb ++ tr0) = Some (b, tr0)) /\
   (Binderishp b = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    1010 <= q' -> S'__endp q' tr0 -> parse_S_ q' (tlb ++ tr0) = Some (b, tr0)) /\
   (1010 = 0 ->
    forall (tr0 : list TOKEN) (q0 : nat) (b0 d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b0 b) tr0 = Some (d, tu) ->
    parse_S'_ q0 b0 (tlb ++ tr0) = Some (d, tu)) ->
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
   pReln_S_ 1010 tr c ->
   (forall (q' : nat) (tr0 : list TOKEN),
    1010 <= q' -> hardendp tr0 -> parse_S_ q' (tr ++ tr0) = Some (c, tr0)) /\
   (Binderishp c = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    1010 <= q' -> S'__endp q' tr0 -> parse_S_ q' (tr ++ tr0) = Some (c, tr0)) /\
   (1010 = 0 ->
    forall (tr0 : list TOKEN) (q0 : nat) (b0 d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b0 c) tr0 = Some (d, tu) ->
    parse_S'_ q0 b0 (tr ++ tr0) = Some (d, tu)) ->
   (forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    hardendp tr0 ->
    parse_S_ q'
      ((LET :: NAM x :: atok :: tlb ++ DEQ :: tl ++ IN :: tr) ++ tr0) =
    Some (LetL x (Some (akd, b)) a c, tr0)) /\
   (Binderishp (LetL x (Some (akd, b)) a c) = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    S'__endp q' tr0 ->
    parse_S_ q'
      ((LET :: NAM x :: atok :: tlb ++ DEQ :: tl ++ IN :: tr) ++ tr0) =
    Some (LetL x (Some (akd, b)) a c, tr0)) /\
   (q = 0 ->
    forall (tr0 : list TOKEN) (q0 : nat) (b0 d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b0 (LetL x (Some (akd, b)) a c)) tr0 =
    Some (d, tu) ->
    parse_S'_ q0 b0
      ((LET :: NAM x :: atok :: tlb ++ DEQ :: tl ++ IN :: tr) ++ tr0) =
    Some (d, tu)).
Proof.
 - intros q x atok akd tlb b tl a tr c Hq Hakd Hx H1 [IH1a [IH1b IH1c]] H2 [IH2a [IH2b IH2c]] H3 [IH3a [IH3b IH3c]]. destruct akd; subst atok; simpl; repeat split. (*** S_Let_T ***)
    + intros q' ts Hq' Hs. simpl. rewrite <- app_assoc. simpl. rewrite <- app_assoc.
       unfold parse_Let_ascr. rewrite tsubl_ref. rewrite IH1a.
       * { simpl. rewrite subl_tsubl_eq.
            - rewrite IH2a.
               + rewrite subl_tsubl_eq.
                  * rewrite IH3a; try reflexivity; try assumption.
                  * apply subl_app. apply sublcons. apply subl_app. apply sublcons. apply sublref.
               + omega.
               + simpl. tauto. (*** IN needs to be a hardendp ***)
            - apply subl_app. apply sublcons. apply sublref.
          }
       * omega.
       * simpl. tauto. (*** DEQ needs to be a hardendp ***)
    + intros NBl. exfalso. simpl in NBl. discriminate.
    + intros Hq0. exfalso. omega.
    + intros q' ts Hq' Hs. simpl. rewrite <- app_assoc. simpl. rewrite <- app_assoc.
       unfold parse_Let_ascr. rewrite tsubl_ref. rewrite IH1a.
       * { simpl. rewrite subl_tsubl_eq.
            - rewrite IH2a.
               + rewrite subl_tsubl_eq.
                  * rewrite IH3a; try reflexivity; try assumption.
                  * apply subl_app. apply sublcons. apply subl_app. apply sublcons. apply sublref.
               + omega.
               + simpl. tauto. (*** IN needs to be a hardendp ***)
            - apply subl_app. apply sublcons. apply sublref.
          }
       * omega.
       * simpl. tauto. (*** DEQ needs to be a hardendp ***)
    + intros NBl. exfalso. simpl in NBl. discriminate.
    + intros Hq0. exfalso. omega.
    + intros q' ts Hq' Hs. simpl. rewrite <- app_assoc. simpl. rewrite <- app_assoc.
       unfold parse_Let_ascr. rewrite tsubl_ref. rewrite IH1a.
       * { simpl. rewrite subl_tsubl_eq.
            - rewrite IH2a.
               + rewrite subl_tsubl_eq.
                  * rewrite IH3a; try reflexivity; try assumption.
                  * apply subl_app. apply sublcons. apply subl_app. apply sublcons. apply sublref.
               + omega.
               + simpl. tauto. (*** IN needs to be a hardendp ***)
            - apply subl_app. apply sublcons. apply sublref.
          }
       * omega.
       * simpl. tauto. (*** DEQ needs to be a hardendp ***)
    + intros NBl. exfalso. simpl in NBl. discriminate.
    + intros Hq0. exfalso. omega.
Qed.

