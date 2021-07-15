Require Export ParsePrintFull3a.

Opaque le_gt_dec.

Lemma parse_S_lem_24 :
   forall (q : nat) (x : string) (i : SetInfixOp) (itok : TOKEN)
     (tl : list TOKEN) (a : LTree) (tlb : list TOKEN) 
     (b : LTree) (tlc : list TOKEN) (c : LTree) (tr : list TOKEN) 
     (d : LTree),
   nam_p x ->
   itok = SetInfixTOK i ->
   pReln_S_ 1010 tl a ->
   (forall (q' : nat) (tr0 : list TOKEN),
    1010 <= q' -> hardendp tr0 -> parse_S_ q' (tl ++ tr0) = Some (a, tr0)) ->
   ~ SetInfixOpL_p a ->
   pReln_S_ 500 tlb b ->
   (forall (q' : nat) (tr0 : list TOKEN),
    500 <= q' -> hardendp tr0 -> parse_S_ q' (tlb ++ tr0) = Some (b, tr0)) ->
   pReln_S_ 1010 tlc c ->
   (forall (q' : nat) (tr0 : list TOKEN),
    1010 <= q' -> hardendp tr0 -> parse_S_ q' (tlc ++ tr0) = Some (c, tr0)) ->
   pReln_S'_ q tr (SepRepL x i a b c) d ->
   (forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    hardendp tr0 ->
    parse_S'_ q' (SepRepL x i a b c) (tr ++ tr0) = Some (d, tr0)) /\
   (Binderishp (SepRepL x i a b c) = false ->
    Binderishp d = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    S'__endp q' tr0 ->
    parse_S'_ q' (SepRepL x i a b c) (tr ++ tr0) = Some (d, tr0)) ->
   (forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    hardendp tr0 ->
    parse_S_ q'
      ((LCBRACE
        :: tl ++
           VBAR :: NAM x :: itok :: tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++
       tr0) = Some (d, tr0)) /\
   (Binderishp d = false ->
    forall (q' : nat) (tr0 : list TOKEN),
    q <= q' ->
    S'__endp q' tr0 ->
    parse_S_ q'
      ((LCBRACE
        :: tl ++
           VBAR :: NAM x :: itok :: tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++
       tr0) = Some (d, tr0)) /\
   (q = 0 ->
    forall (tr0 : list TOKEN) (q0 : nat) (b0 d0 : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b0 d) tr0 = Some (d0, tu) ->
    parse_S'_ q0 b0
      ((LCBRACE
        :: tl ++
           VBAR :: NAM x :: itok :: tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++
       tr0) = Some (d0, tu)).
Proof.
 intros q x i itok tl a tlb b tlc c tr d Hx Hi H1 IH1a Ka H2 IH2a H3 IH3a H4 [IH4a IH4b]. (*** S_SepRep_S' ***)
    assert (L1:penv x = (None,None,None)).
    {
      revert Hx. unfold nam_p. case_eq (penv x). intros [[p'|] [qk|]] [mtok'|]; try tauto.
    }
    repeat split.
    + intros q' ts Hq' Hs. simpl. rewrite <- app_assoc.
       assert (L2:(parse_S_SetBraces q'
         (tl ++ (VBAR :: NAM x :: itok :: tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
         (fun a0 : LTree => a0)
         (fun (q0 : nat) (a0 : LTree) (ts0 : list TOKEN) =>
          parse_S'_ q0 a0
            (tsubl
               (tl ++ (VBAR :: NAM x :: itok :: tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
               ts0))
         (fun (q0 : nat) (ts0 : list TOKEN) =>
          parse_S_ q0
            (tsubl
               (tl ++ (VBAR :: NAM x :: itok :: tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
               ts0))
         (fun ts0 : list TOKEN =>
          parse_N
            (tsubl
               (tl ++ (VBAR :: NAM x :: itok :: tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
               ts0))) = Some (d, ts)).
       {
         unfold parse_S_SetBraces. simpl. rewrite tsubl_ref. rewrite IH1a.
         - subst itok. destruct i.
            + simpl.
               assert (L3:(       match
         parse_S_ 1023
           (tsubl
              (tl ++ VBAR :: NAM x :: MEM :: (tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
              ((tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts))
       with
       | Some (b0, []) => None
       | Some (b0, NAM _ :: _) => None
       | Some (b0, NUM _ _ _ :: _) => None
       | Some (b0, LPAREN :: _) => None
       | Some (b0, RPAREN :: _) => None
       | Some (b0, COMMA :: tu) =>
           match
             parse_S_ 1023
               (tsubl
                  (tl ++ VBAR :: NAM x :: MEM :: (tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
                  (tsubl
                     (tl ++
                      VBAR :: NAM x :: MEM :: (tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
                     tu))
           with
           | Some (c0, []) => None
           | Some (c0, NAM _ :: _) => None
           | Some (c0, NUM _ _ _ :: _) => None
           | Some (c0, LPAREN :: _) => None
           | Some (c0, RPAREN :: _) => None
           | Some (c0, COMMA :: _) => None
           | Some (c0, COLON :: _) => None
           | Some (c0, DARR :: _) => None
           | Some (c0, LET :: _) => None
           | Some (c0, DEQ :: _) => None
           | Some (c0, IN :: _) => None
           | Some (c0, MEM :: _) => None
           | Some (c0, SUBEQ :: _) => None
           | Some (c0, VBAR :: _) => None
           | Some (c0, LCBRACE :: _) => None
           | Some (c0, RCBRACE :: tv) =>
               parse_S'_ q' (SepRepL x InfMem a b0 c0)
                 (tsubl
                    (tl ++
                     VBAR :: NAM x :: MEM :: (tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts) tv)
           | Some (c0, LBRACK :: _) => None
           | Some (c0, RBRACK :: _) => None
           | Some (c0, IF_ :: _) => None
           | Some (c0, THEN :: _) => None
           | Some (c0, ELSE :: _) => None
           | None => None
           end
       | Some (b0, COLON :: _) => None
       | Some (b0, DARR :: _) => None
       | Some (b0, LET :: _) => None
       | Some (b0, DEQ :: _) => None
       | Some (b0, IN :: _) => None
       | Some (b0, MEM :: _) => None
       | Some (b0, SUBEQ :: _) => None
       | Some (b0, VBAR :: _) => None
       | Some (b0, LCBRACE :: _) => None
       | Some (b0, RCBRACE :: tu) =>
           parse_S'_ q' (RepL x InfMem a b0)
             (tsubl
                (tl ++ VBAR :: NAM x :: MEM :: (tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
                tu)
       | Some (b0, LBRACK :: _) => None
       | Some (b0, RBRACK :: _) => None
       | Some (c0, IF_ :: _) => None
       | Some (c0, THEN :: _) => None
       | Some (c0, ELSE :: _) => None
       | None => None
       end) = Some(d,ts)).
               {
                 rewrite subl_tsubl_eq.
                 - rewrite <- app_assoc. rewrite IH2a.
                    + simpl. rewrite subl_tsubl_eq.
                       * { rewrite subl_tsubl_eq.
                            - rewrite <- app_assoc. rewrite IH3a.
                               + simpl. rewrite subl_tsubl_eq.
                                  * now apply IH4a.
                                  * apply subl_app. apply sublcons. apply sublcons. apply sublcons.
                                     apply subl_app. apply sublcons.
                                     apply subl_app. apply sublcons. apply sublref.
                               + omega.
                               + exact I.
                            - apply subl_app. apply sublcons. apply sublcons. apply sublcons.
                               apply subl_app. apply sublcons. apply sublref.
                          }
                       * { rewrite subl_tsubl_eq.
                            - apply subl_app. apply sublcons. apply sublcons. apply sublcons.
                               apply subl_app. apply sublcons. apply sublref.
                            - apply subl_app. apply sublcons. apply sublcons. apply sublcons.
                               apply subl_app. apply sublcons. apply sublref.
                          }
                    + omega.
                    + exact I.
                 - apply subl_app. apply sublcons. apply sublcons. apply sublcons. apply sublref.
               }
               rewrite L3.
               destruct a; try reflexivity.
               destruct i; try reflexivity.
               destruct a1; try reflexivity.
               exfalso. apply Ka. simpl. tauto. (*** This is where I've made sure SepRep can't be confused with Sep. ***)
            + simpl.
               assert (L3:(       match
         parse_S_ 1023
           (tsubl
              (tl ++ VBAR :: NAM x :: SUBEQ :: (tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
              ((tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts))
       with
       | Some (b0, []) => None
       | Some (b0, NAM _ :: _) => None
       | Some (b0, NUM _ _ _ :: _) => None
       | Some (b0, LPAREN :: _) => None
       | Some (b0, RPAREN :: _) => None
       | Some (b0, COMMA :: tu) =>
           match
             parse_S_ 1023
                  (tsubl
                     (tl ++
                      VBAR :: NAM x :: SUBEQ :: (tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
                     tu)
           with
           | Some (c0, []) => None
           | Some (c0, NAM _ :: _) => None
           | Some (c0, NUM _ _ _ :: _) => None
           | Some (c0, LPAREN :: _) => None
           | Some (c0, RPAREN :: _) => None
           | Some (c0, COMMA :: _) => None
           | Some (c0, COLON :: _) => None
           | Some (c0, DARR :: _) => None
           | Some (c0, LET :: _) => None
           | Some (c0, DEQ :: _) => None
           | Some (c0, IN :: _) => None
           | Some (c0, MEM :: _) => None
           | Some (c0, SUBEQ :: _) => None
           | Some (c0, VBAR :: _) => None
           | Some (c0, LCBRACE :: _) => None
           | Some (c0, RCBRACE :: tv) =>
               parse_S'_ q' (SepRepL x InfSubq a b0 c0)
                 (tsubl
                    (tl ++
                     VBAR :: NAM x :: SUBEQ :: (tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts) tv)
           | Some (c0, LBRACK :: _) => None
           | Some (c0, RBRACK :: _) => None
           | Some (c0, IF_ :: _) => None
           | Some (c0, THEN :: _) => None
           | Some (c0, ELSE :: _) => None
           | None => None
           end
       | Some (b0, COLON :: _) => None
       | Some (b0, DARR :: _) => None
       | Some (b0, LET :: _) => None
       | Some (b0, DEQ :: _) => None
       | Some (b0, IN :: _) => None
       | Some (b0, MEM :: _) => None
       | Some (b0, SUBEQ :: _) => None
       | Some (b0, VBAR :: _) => None
       | Some (b0, LCBRACE :: _) => None
       | Some (b0, RCBRACE :: tu) =>
           parse_S'_ q' (RepL x InfSubq a b0)
             (tsubl
                (tl ++ VBAR :: NAM x :: SUBEQ :: (tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
                tu)
       | Some (b0, LBRACK :: _) => None
       | Some (b0, RBRACK :: _) => None
       | Some (c0, IF_ :: _) => None
       | Some (c0, THEN :: _) => None
       | Some (c0, ELSE :: _) => None
       | None => None
       end) = Some(d,ts)).
               {
                 rewrite subl_tsubl_eq.
                 - rewrite <- app_assoc. rewrite IH2a.
                    + simpl. rewrite subl_tsubl_eq.
                       * { 
                            - rewrite <- app_assoc. rewrite IH3a.
                               + simpl. rewrite subl_tsubl_eq.
                                  * now apply IH4a.
                                  * apply subl_app. apply sublcons. apply sublcons. apply sublcons.
                                     apply subl_app. apply sublcons.
                                     apply subl_app. apply sublcons. apply sublref.
                               + omega.
                               + exact I.
                          }
                       * apply subl_app. apply sublcons. apply sublcons. apply sublcons.
                          apply subl_app. apply sublcons. apply sublref.
                    + omega.
                    + exact I.
                 - apply subl_app. apply sublcons. apply sublcons. apply sublcons. apply sublref.
               }
               rewrite L3.
               destruct a; try reflexivity.
               destruct i; try reflexivity.
               destruct a1; try reflexivity.
               exfalso. apply Ka. simpl. tauto. (*** This is where I've made sure SepRep can't be confused with Sep. ***)
          - omega.
          - exact I.
       }
       rewrite L2.
       destruct tl.
       * exfalso. inversion H1.
       * destruct t; try reflexivity. inversion H1.
    + intros NBc q' ts Hq' Hs.
       simpl. rewrite <- app_assoc.
       assert (L2:(parse_S_SetBraces q'
         (tl ++ (VBAR :: NAM x :: itok :: tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
         (fun a0 : LTree => a0)
         (fun (q0 : nat) (a0 : LTree) (ts0 : list TOKEN) =>
          parse_S'_ q0 a0
            (tsubl
               (tl ++ (VBAR :: NAM x :: itok :: tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
               ts0))
         (fun (q0 : nat) (ts0 : list TOKEN) =>
          parse_S_ q0
            (tsubl
               (tl ++ (VBAR :: NAM x :: itok :: tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
               ts0))
         (fun ts0 : list TOKEN =>
          parse_N
            (tsubl
               (tl ++ (VBAR :: NAM x :: itok :: tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
               ts0))) = Some (d, ts)).
       {
         unfold parse_S_SetBraces. simpl. rewrite tsubl_ref. rewrite IH1a.
         - subst itok. destruct i.
            + simpl.
               assert (L3:(       match
         parse_S_ 1023
           (tsubl
              (tl ++ VBAR :: NAM x :: MEM :: (tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
              ((tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts))
       with
       | Some (b0, []) => None
       | Some (b0, NAM _ :: _) => None
       | Some (b0, NUM _ _ _ :: _) => None
       | Some (b0, LPAREN :: _) => None
       | Some (b0, RPAREN :: _) => None
       | Some (b0, COMMA :: tu) =>
           match
             parse_S_ 1023
               (tsubl
                  (tl ++ VBAR :: NAM x :: MEM :: (tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
                  (tsubl
                     (tl ++
                      VBAR :: NAM x :: MEM :: (tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
                     tu))
           with
           | Some (c0, []) => None
           | Some (c0, NAM _ :: _) => None
           | Some (c0, NUM _ _ _ :: _) => None
           | Some (c0, LPAREN :: _) => None
           | Some (c0, RPAREN :: _) => None
           | Some (c0, COMMA :: _) => None
           | Some (c0, COLON :: _) => None
           | Some (c0, DARR :: _) => None
           | Some (c0, LET :: _) => None
           | Some (c0, DEQ :: _) => None
           | Some (c0, IN :: _) => None
           | Some (c0, MEM :: _) => None
           | Some (c0, SUBEQ :: _) => None
           | Some (c0, VBAR :: _) => None
           | Some (c0, LCBRACE :: _) => None
           | Some (c0, RCBRACE :: tv) =>
               parse_S'_ q' (SepRepL x InfMem a b0 c0)
                 (tsubl
                    (tl ++
                     VBAR :: NAM x :: MEM :: (tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts) tv)
           | Some (c0, LBRACK :: _) => None
           | Some (c0, RBRACK :: _) => None
           | Some (c0, IF_ :: _) => None
           | Some (c0, THEN :: _) => None
           | Some (c0, ELSE :: _) => None
           | None => None
           end
       | Some (b0, COLON :: _) => None
       | Some (b0, DARR :: _) => None
       | Some (b0, LET :: _) => None
       | Some (b0, DEQ :: _) => None
       | Some (b0, IN :: _) => None
       | Some (b0, MEM :: _) => None
       | Some (b0, SUBEQ :: _) => None
       | Some (b0, VBAR :: _) => None
       | Some (b0, LCBRACE :: _) => None
       | Some (b0, RCBRACE :: tu) =>
           parse_S'_ q' (RepL x InfMem a b0)
             (tsubl
                (tl ++ VBAR :: NAM x :: MEM :: (tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
                tu)
       | Some (b0, LBRACK :: _) => None
       | Some (b0, RBRACK :: _) => None
       | Some (c0, IF_ :: _) => None
       | Some (c0, THEN :: _) => None
       | Some (c0, ELSE :: _) => None
       | None => None
       end) = Some(d,ts)).
               {
                 rewrite subl_tsubl_eq.
                 - rewrite <- app_assoc. rewrite IH2a.
                    + simpl. rewrite subl_tsubl_eq.
                       * { rewrite subl_tsubl_eq.
                            - rewrite <- app_assoc. rewrite IH3a.
                               + simpl. rewrite subl_tsubl_eq.
                                  * now apply IH4b.
                                  * apply subl_app. apply sublcons. apply sublcons. apply sublcons.
                                     apply subl_app. apply sublcons.
                                     apply subl_app. apply sublcons. apply sublref.
                               + omega.
                               + exact I.
                            - apply subl_app. apply sublcons. apply sublcons. apply sublcons.
                               apply subl_app. apply sublcons. apply sublref.
                          }
                       * { rewrite subl_tsubl_eq.
                            - apply subl_app. apply sublcons. apply sublcons. apply sublcons.
                               apply subl_app. apply sublcons. apply sublref.
                            - apply subl_app. apply sublcons. apply sublcons. apply sublcons.
                               apply subl_app. apply sublcons. apply sublref.
                          }
                    + omega.
                    + exact I.
                 - apply subl_app. apply sublcons. apply sublcons. apply sublcons. apply sublref.
               }
               rewrite L3.
               destruct a; try reflexivity.
               destruct i; try reflexivity.
               destruct a1; try reflexivity.
               exfalso. apply Ka. simpl. tauto. (*** This is where I've made sure SepRep can't be confused with Sep. ***)
            + simpl.
               assert (L3:(       match
         parse_S_ 1023
           (tsubl
              (tl ++ VBAR :: NAM x :: SUBEQ :: (tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
              ((tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts))
       with
       | Some (b0, []) => None
       | Some (b0, NAM _ :: _) => None
       | Some (b0, NUM _ _ _ :: _) => None
       | Some (b0, LPAREN :: _) => None
       | Some (b0, RPAREN :: _) => None
       | Some (b0, COMMA :: tu) =>
           match
             parse_S_ 1023
                  (tsubl
                     (tl ++
                      VBAR :: NAM x :: SUBEQ :: (tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
                     tu)
           with
           | Some (c0, []) => None
           | Some (c0, NAM _ :: _) => None
           | Some (c0, NUM _ _ _ :: _) => None
           | Some (c0, LPAREN :: _) => None
           | Some (c0, RPAREN :: _) => None
           | Some (c0, COMMA :: _) => None
           | Some (c0, COLON :: _) => None
           | Some (c0, DARR :: _) => None
           | Some (c0, LET :: _) => None
           | Some (c0, DEQ :: _) => None
           | Some (c0, IN :: _) => None
           | Some (c0, MEM :: _) => None
           | Some (c0, SUBEQ :: _) => None
           | Some (c0, VBAR :: _) => None
           | Some (c0, LCBRACE :: _) => None
           | Some (c0, RCBRACE :: tv) =>
               parse_S'_ q' (SepRepL x InfSubq a b0 c0)
                 (tsubl
                    (tl ++
                     VBAR :: NAM x :: SUBEQ :: (tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts) tv)
           | Some (c0, LBRACK :: _) => None
           | Some (c0, RBRACK :: _) => None
           | Some (c0, IF_ :: _) => None
           | Some (c0, THEN :: _) => None
           | Some (c0, ELSE :: _) => None
           | None => None
           end
       | Some (b0, COLON :: _) => None
       | Some (b0, DARR :: _) => None
       | Some (b0, LET :: _) => None
       | Some (b0, DEQ :: _) => None
       | Some (b0, IN :: _) => None
       | Some (b0, MEM :: _) => None
       | Some (b0, SUBEQ :: _) => None
       | Some (b0, VBAR :: _) => None
       | Some (b0, LCBRACE :: _) => None
       | Some (b0, RCBRACE :: tu) =>
           parse_S'_ q' (RepL x InfSubq a b0)
             (tsubl
                (tl ++ VBAR :: NAM x :: SUBEQ :: (tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
                tu)
       | Some (b0, LBRACK :: _) => None
       | Some (b0, RBRACK :: _) => None
       | Some (c0, IF_ :: _) => None
       | Some (c0, THEN :: _) => None
       | Some (c0, ELSE :: _) => None
       | None => None
       end) = Some(d,ts)).
               {
                 rewrite subl_tsubl_eq.
                 - rewrite <- app_assoc. rewrite IH2a.
                    + simpl. rewrite subl_tsubl_eq.
                       * { 
                            - rewrite <- app_assoc. rewrite IH3a.
                               + simpl. rewrite subl_tsubl_eq.
                                  * now apply IH4b.
                                  * apply subl_app. apply sublcons. apply sublcons. apply sublcons.
                                     apply subl_app. apply sublcons.
                                     apply subl_app. apply sublcons. apply sublref.
                               + omega.
                               + exact I.
                          }
                       * apply subl_app. apply sublcons. apply sublcons. apply sublcons.
                          apply subl_app. apply sublcons. apply sublref.
                    + omega.
                    + exact I.
                 - apply subl_app. apply sublcons. apply sublcons. apply sublcons. apply sublref.
               }
               rewrite L3.
               destruct a; try reflexivity.
               destruct i; try reflexivity.
               destruct a1; try reflexivity.
               exfalso. apply Ka. simpl. tauto. (*** This is where I've made sure SepRep can't be confused with Sep. ***)
          - omega.
          - exact I.
       }
       rewrite L2.
       destruct tl.
       * exfalso. inversion H1.
       * destruct t; try reflexivity. inversion H1.
    + intros Hq0 ts q' e d' tu Hq' K1. simpl. destruct q'; try (exfalso; omega).
       rewrite <- app_assoc.
       assert (L2:(parse_S_SetBraces (S q')
         (tl ++
          (VBAR :: NAM x :: itok :: tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++
          ts) (fun b0 : LTree => ImplicitInfop e b0)
         (fun (q0 : nat) (a0 : LTree) (ts0 : list TOKEN) =>
          parse_S'_ q0 a0
            (tsubl
               (tl ++
                (VBAR
                 :: NAM x :: itok :: tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++
                ts) ts0))
         (fun (q0 : nat) (ts0 : list TOKEN) =>
          parse_S_ q0
            (tsubl
               (tl ++
                (VBAR
                 :: NAM x :: itok :: tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++
                ts) ts0))
         (fun ts0 : list TOKEN =>
          parse_N
            (tsubl
               (tl ++
                (VBAR
                 :: NAM x :: itok :: tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++
                ts) ts0))) = Some(d',tu)).
       {
         unfold parse_S_SetBraces.
         rewrite tsubl_ref.
         rewrite IH1a.
         - simpl. subst itok. destruct i; simpl.
            + assert (L3:(match
         parse_S_ 1023
           (tsubl
              (tl ++
               VBAR
               :: NAM x
                  :: MEM :: (tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
              ((tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts))
       with
       | Some (b0, []) => None
       | Some (b0, NAM _ :: _) => None
       | Some (b0, NUM _ _ _ :: _) => None
       | Some (b0, LPAREN :: _) => None
       | Some (b0, RPAREN :: _) => None
       | Some (b0, COMMA :: tu0) =>
           match
             parse_S_ 1023
               (tsubl
                  (tl ++
                   VBAR
                   :: NAM x
                      :: MEM :: (tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
                  (tsubl
                     (tl ++
                      VBAR
                      :: NAM x
                         :: MEM
                            :: (tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
                     tu0))
           with
           | Some (c0, []) => None
           | Some (c0, NAM _ :: _) => None
           | Some (c0, NUM _ _ _ :: _) => None
           | Some (c0, LPAREN :: _) => None
           | Some (c0, RPAREN :: _) => None
           | Some (c0, COMMA :: _) => None
           | Some (c0, COLON :: _) => None
           | Some (c0, DARR :: _) => None
           | Some (c0, LET :: _) => None
           | Some (c0, DEQ :: _) => None
           | Some (c0, IN :: _) => None
           | Some (c0, MEM :: _) => None
           | Some (c0, SUBEQ :: _) => None
           | Some (c0, VBAR :: _) => None
           | Some (c0, LCBRACE :: _) => None
           | Some (c0, RCBRACE :: tv) =>
               parse_S'_ (S q') (ImplicitInfop e (SepRepL x InfMem a b0 c0))
                 (tsubl
                    (tl ++
                     VBAR
                     :: NAM x
                        :: MEM
                           :: (tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
                    tv)
           | Some (c0, LBRACK :: _) => None
           | Some (c0, RBRACK :: _) => None
           | Some (c0, IF_ :: _) => None
           | Some (c0, THEN :: _) => None
           | Some (c0, ELSE :: _) => None
           | None => None
           end
       | Some (b0, COLON :: _) => None
       | Some (b0, DARR :: _) => None
       | Some (b0, LET :: _) => None
       | Some (b0, DEQ :: _) => None
       | Some (b0, IN :: _) => None
       | Some (b0, MEM :: _) => None
       | Some (b0, SUBEQ :: _) => None
       | Some (b0, VBAR :: _) => None
       | Some (b0, LCBRACE :: _) => None
       | Some (b0, RCBRACE :: tu0) =>
           parse_S'_ (S q') (ImplicitInfop e (RepL x InfMem a b0))
             (tsubl
                (tl ++
                 VBAR
                 :: NAM x
                    :: MEM :: (tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
                tu0)
       | Some (b0, LBRACK :: _) => None
       | Some (b0, RBRACK :: _) => None
       | Some (c0, IF_ :: _) => None
       | Some (c0, THEN :: _) => None
       | Some (c0, ELSE :: _) => None
       | None => None
       end) = Some(d',tu)).
            {
              rewrite subl_tsubl_eq.
              - rewrite <- app_assoc. rewrite IH2a.
                 + simpl. rewrite subl_tsubl_eq.
                    * { rewrite subl_tsubl_eq.
                         - rewrite <- app_assoc. rewrite IH3a.
                            + simpl. rewrite subl_tsubl_eq.
                               * subst q. apply pReln_S'_0 in H4. destruct H4. subst tr. subst d. exact K1.
                               * apply subl_app. apply sublcons. apply sublcons. apply sublcons.
                                  apply subl_app. apply sublcons.
                                  apply subl_app. apply sublcons. apply sublref.
                            + omega.
                            + exact I.
                         - apply subl_app. apply sublcons. apply sublcons. apply sublcons.
                            apply subl_app. apply sublcons. apply sublref.
                       }
                    * { rewrite subl_tsubl_eq.
                         - apply subl_app. apply sublcons. apply sublcons. apply sublcons.
                            apply subl_app. apply sublcons. apply sublref.
                         - apply subl_app. apply sublcons. apply sublcons. apply sublcons.
                            apply subl_app. apply sublcons. apply sublref.
                       }
                 + omega.
                 + exact I.
              - apply subl_app. apply sublcons. apply sublcons. apply sublcons. apply sublref.
            }
            rewrite L3.
            destruct a; try reflexivity.
            destruct i; try reflexivity.
            exfalso. apply Ka. simpl. tauto.
            + assert (L3:(match
         parse_S_ 1023
           (tsubl
              (tl ++
               VBAR
               :: NAM x
                  :: SUBEQ :: (tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
              ((tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts))
       with
       | Some (b0, []) => None
       | Some (b0, NAM _ :: _) => None
       | Some (b0, NUM _ _ _ :: _) => None
       | Some (b0, LPAREN :: _) => None
       | Some (b0, RPAREN :: _) => None
       | Some (b0, COMMA :: tu0) =>
           match
             parse_S_ 1023
               (tsubl
                  (tl ++
                   VBAR
                   :: NAM x
                      :: SUBEQ
                         :: (tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts) tu0)
           with
           | Some (c0, []) => None
           | Some (c0, NAM _ :: _) => None
           | Some (c0, NUM _ _ _ :: _) => None
           | Some (c0, LPAREN :: _) => None
           | Some (c0, RPAREN :: _) => None
           | Some (c0, COMMA :: _) => None
           | Some (c0, COLON :: _) => None
           | Some (c0, DARR :: _) => None
           | Some (c0, LET :: _) => None
           | Some (c0, DEQ :: _) => None
           | Some (c0, IN :: _) => None
           | Some (c0, MEM :: _) => None
           | Some (c0, SUBEQ :: _) => None
           | Some (c0, VBAR :: _) => None
           | Some (c0, LCBRACE :: _) => None
           | Some (c0, RCBRACE :: tv) =>
               parse_S'_ (S q') (ImplicitInfop e (SepRepL x InfSubq a b0 c0))
                 (tsubl
                    (tl ++
                     VBAR
                     :: NAM x
                        :: SUBEQ
                           :: (tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
                    tv)
           | Some (c0, LBRACK :: _) => None
           | Some (c0, RBRACK :: _) => None
           | Some (c0, IF_ :: _) => None
           | Some (c0, THEN :: _) => None
           | Some (c0, ELSE :: _) => None
           | None => None
           end
       | Some (b0, COLON :: _) => None
       | Some (b0, DARR :: _) => None
       | Some (b0, LET :: _) => None
       | Some (b0, DEQ :: _) => None
       | Some (b0, IN :: _) => None
       | Some (b0, MEM :: _) => None
       | Some (b0, SUBEQ :: _) => None
       | Some (b0, VBAR :: _) => None
       | Some (b0, LCBRACE :: _) => None
       | Some (b0, RCBRACE :: tu0) =>
           parse_S'_ (S q') (ImplicitInfop e (RepL x InfSubq a b0))
             (tsubl
                (tl ++
                 VBAR
                 :: NAM x
                    :: SUBEQ :: (tlb ++ COMMA :: tlc ++ RCBRACE :: tr) ++ ts)
                tu0)
       | Some (b0, LBRACK :: _) => None
       | Some (b0, RBRACK :: _) => None
       | Some (c0, IF_ :: _) => None
       | Some (c0, THEN :: _) => None
       | Some (c0, ELSE :: _) => None
       | None => None
       end) = Some(d',tu)).
            {
              rewrite subl_tsubl_eq.
              - rewrite <- app_assoc. rewrite IH2a.
                 + simpl. rewrite subl_tsubl_eq.
                    * { 
                         - rewrite <- app_assoc. rewrite IH3a.
                            + simpl. rewrite subl_tsubl_eq.
                               * subst q. apply pReln_S'_0 in H4. destruct H4. subst tr. subst d. exact K1.
                               * apply subl_app. apply sublcons. apply sublcons. apply sublcons.
                                  apply subl_app. apply sublcons.
                                  apply subl_app. apply sublcons. apply sublref.
                            + omega.
                            + exact I.
                       }
                    * apply subl_app. apply sublcons. apply sublcons. apply sublcons.
                            apply subl_app. apply sublcons. apply sublref.
                 + omega.
                 + exact I.
              - apply subl_app. apply sublcons. apply sublcons. apply sublcons. apply sublref.
            }
            rewrite L3.
            destruct a; try reflexivity.
            destruct i; try reflexivity.
            exfalso. apply Ka. simpl. tauto.
         - omega.
         - exact I.
       }
       rewrite L2.
       destruct tl.
       * exfalso. inversion H1.
       * destruct t; try reflexivity. inversion H1.
Qed.
