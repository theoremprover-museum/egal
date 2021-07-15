Require Export ParsePrintFull3b.
Require Export ParsePrintFull3bb.
Require Export ParsePrintFull3bc.
Require Export ParsePrintFull3bd.
Require Export ParsePrintFull3be.
Require Export ParsePrintFull3c.
Require Export ParsePrintFull3cb.
Require Export ParsePrintFull3d.
Require Export ParsePrintFull3db.

Opaque le_gt_dec.

Lemma parse_S_lem :
 (forall q tl a c, pReln_S'_ q tl a c ->
    (forall q' tr, q <= q' -> hardendp tr -> parse_S'_ q' a (tl ++ tr) = Some(c,tr))
    /\
    (Binderishp a = false -> Binderishp c = false -> forall q' tr, q <= q' -> S'__endp q' tr -> parse_S'_ q' a (tl ++ tr) = Some(c,tr)))
 /\
 (forall q tl a, pReln_S_ q tl a -> 
    (forall q' tr, q <= q' -> hardendp tr -> parse_S_ q' (tl ++ tr) = Some(a,tr))
    /\
    (Binderishp a = false -> forall q' tr, q <= q' -> S'__endp q' tr -> parse_S_ q' (tl ++ tr) = Some(a,tr))
    /\
    (q = 0 -> forall tr q b d tu, q > 0
           -> parse_S'_ q (ImplicitInfop b a) tr = Some(d, tu)
           -> parse_S'_ q b (tl ++ tr) = Some(d, tu)))
 /\
 (forall tl vll, pReln_TVs tl vll -> forall tr, ~LPARENp tr -> parse_TVs (tl ++ tr) = Some(vll,tr))
 /\
 (forall tl a, pReln_N tl a -> forall tr, ~COMMAp tr -> hardendp tr -> parse_N (tl ++ tr) = Some(a,tr)).
Proof.
  apply pRelnl_mutind.
  - exact parse_S_lem_1.
  - exact parse_S_lem_2.
  - exact parse_S_lem_3.
  - exact parse_S_lem_4.
  - exact parse_S_lem_5.
  - exact parse_S_lem_6.
  - exact parse_S_lem_7.
  - exact parse_S_lem_8.
  - exact parse_S_lem_9.
  - exact parse_S_lem_10.
  - exact parse_S_lem_11.
  - exact parse_S_lem_12.
  - exact parse_S_lem_13.
  - exact parse_S_lem_14.
  - exact parse_S_lem_15.
  - exact parse_S_lem_16.
  - exact parse_S_lem_17.
  - exact parse_S_lem_18.
  - exact parse_S_lem_19.
  - exact parse_S_lem_20.
  - exact parse_S_lem_21.
  - intros q x i itok tl a tlb b tr c Hx Hi H1 [IH1a [IH1b IH1c]] H2 [IH2a [IH2b IH2c]] H3 [IH3a IH3b]. (*** S_Sep_S' ***)
     assert (L1:penv x = (None,None,None)).
     {
       revert Hx. unfold nam_p. case_eq (penv x). intros [[p'|] [qk|]] [mtok'|]; try tauto.
     }
     repeat split.
     + exact (parse_S_lem_22a q x i itok tl a tlb b tr c Hx Hi H1 IH1a IH1b IH1c H2 IH2a IH2b IH2c H3 IH3a IH3b L1).
     + exact (parse_S_lem_22b q x i itok tl a tlb b tr c Hx Hi H1 IH1a IH1b IH1c H2 IH2a IH2b IH2c H3 IH3a IH3b L1).
     + exact (parse_S_lem_22c q x i itok tl a tlb b tr c Hx Hi H1 IH1a IH1b IH1c H2 IH2a IH2b IH2c H3 IH3a IH3b L1).
 - exact parse_S_lem_23.
 - intros q x i itok tl a tlb b tlc c tr d Hx Hi H1 [IH1a _] Ha H2 [IH2a _] H3 [IH3a _].
   exact (parse_S_lem_24 q x i itok tl a tlb b tlc c tr d Hx Hi H1 IH1a Ha H2 IH2a H3 IH3a).
 - intros q tr c H1 [IH1a IH1b]. repeat split. (*** S_SetEmpty_S' ***)
    + intros q' ts Hq' Hs. simpl. now apply IH1a.
    + intros NBc q' ts Hq' Hs. simpl. apply IH1b; try assumption. reflexivity.
    + intros Hq0 ts q' b d tu Hq' K1. simpl. destruct q'; try (exfalso; omega).
       subst q. apply pReln_S'_0 in H1. destruct H1. subst tr. subst c.
       exact K1.
 - intros q tl a tlr bl tr c H1 [IH1a [IH1b IH1c]] H2 IH2 H3 [IH3a IH3b]. (*** S_SetEnum_S' ***)
    repeat split.
    + intros q' ts Hq' Hs. simpl. rewrite <- app_assoc.
       assert (L2:(parse_S_SetBraces q' (tl ++ (tlr ++ RCBRACE :: tr) ++ ts)
         (fun a0 : LTree => a0)
         (fun (q0 : nat) (a0 : LTree) (ts0 : list TOKEN) =>
          parse_S'_ q0 a0 (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) ts0))
         (fun (q0 : nat) (ts0 : list TOKEN) =>
          parse_S_ q0 (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) ts0))
         (fun ts0 : list TOKEN =>
          parse_N (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) ts0))) = Some(c,ts)).
       { unfold parse_S_SetBraces. rewrite tsubl_ref. rewrite IH1a.
         - rewrite tsubl_app_eq.
            assert (L3:(match (tlr ++ RCBRACE :: tr) ++ ts with
       | [] =>
           match parse_N ((tlr ++ RCBRACE :: tr) ++ ts) with
           | Some (bl0, []) => None
           | Some (bl0, NAM _ :: _) => None
           | Some (bl0, NUM _ _ _ :: _) => None
           | Some (bl0, LPAREN :: _) => None
           | Some (bl0, RPAREN :: _) => None
           | Some (bl0, COMMA :: _) => None
           | Some (bl0, COLON :: _) => None
           | Some (bl0, DARR :: _) => None
           | Some (bl0, LET :: _) => None
           | Some (bl0, DEQ :: _) => None
           | Some (bl0, IN :: _) => None
           | Some (bl0, MEM :: _) => None
           | Some (bl0, SUBEQ :: _) => None
           | Some (bl0, VBAR :: _) => None
           | Some (bl0, LCBRACE :: _) => None
           | Some (bl0, RCBRACE :: tu) =>
               parse_S'_ q' (SetEnumL (LCons a bl0))
                 (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) tu)
           | Some (bl0, LBRACK :: _) => None
           | Some (bl0, RBRACK :: _) => None
           | Some (bl0, IF_ :: _) => None
           | Some (bl0, THEN :: _) => None
           | Some (bl0, ELSE :: _) => None
           | None => None
           end
       | NAM _ :: _ =>
           match parse_N ((tlr ++ RCBRACE :: tr) ++ ts) with
           | Some (bl0, []) => None
           | Some (bl0, NAM _ :: _) => None
           | Some (bl0, NUM _ _ _ :: _) => None
           | Some (bl0, LPAREN :: _) => None
           | Some (bl0, RPAREN :: _) => None
           | Some (bl0, COMMA :: _) => None
           | Some (bl0, COLON :: _) => None
           | Some (bl0, DARR :: _) => None
           | Some (bl0, LET :: _) => None
           | Some (bl0, DEQ :: _) => None
           | Some (bl0, IN :: _) => None
           | Some (bl0, MEM :: _) => None
           | Some (bl0, SUBEQ :: _) => None
           | Some (bl0, VBAR :: _) => None
           | Some (bl0, LCBRACE :: _) => None
           | Some (bl0, RCBRACE :: tu) =>
               parse_S'_ q' (SetEnumL (LCons a bl0))
                 (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) tu)
           | Some (bl0, LBRACK :: _) => None
           | Some (bl0, RBRACK :: _) => None
           | Some (bl0, IF_ :: _) => None
           | Some (bl0, THEN :: _) => None
           | Some (bl0, ELSE :: _) => None
           | None => None
           end
       | NUM _ _ _ :: _ =>
           match parse_N ((tlr ++ RCBRACE :: tr) ++ ts) with
           | Some (bl0, []) => None
           | Some (bl0, NAM _ :: _) => None
           | Some (bl0, NUM _ _ _ :: _) => None
           | Some (bl0, LPAREN :: _) => None
           | Some (bl0, RPAREN :: _) => None
           | Some (bl0, COMMA :: _) => None
           | Some (bl0, COLON :: _) => None
           | Some (bl0, DARR :: _) => None
           | Some (bl0, LET :: _) => None
           | Some (bl0, DEQ :: _) => None
           | Some (bl0, IN :: _) => None
           | Some (bl0, MEM :: _) => None
           | Some (bl0, SUBEQ :: _) => None
           | Some (bl0, VBAR :: _) => None
           | Some (bl0, LCBRACE :: _) => None
           | Some (bl0, RCBRACE :: tu) =>
               parse_S'_ q' (SetEnumL (LCons a bl0))
                 (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) tu)
           | Some (bl0, LBRACK :: _) => None
           | Some (bl0, RBRACK :: _) => None
           | Some (bl0, IF_ :: _) => None
           | Some (bl0, THEN :: _) => None
           | Some (bl0, ELSE :: _) => None
           | None => None
           end
       | LPAREN :: _ =>
           match parse_N ((tlr ++ RCBRACE :: tr) ++ ts) with
           | Some (bl0, []) => None
           | Some (bl0, NAM _ :: _) => None
           | Some (bl0, NUM _ _ _ :: _) => None
           | Some (bl0, LPAREN :: _) => None
           | Some (bl0, RPAREN :: _) => None
           | Some (bl0, COMMA :: _) => None
           | Some (bl0, COLON :: _) => None
           | Some (bl0, DARR :: _) => None
           | Some (bl0, LET :: _) => None
           | Some (bl0, DEQ :: _) => None
           | Some (bl0, IN :: _) => None
           | Some (bl0, MEM :: _) => None
           | Some (bl0, SUBEQ :: _) => None
           | Some (bl0, VBAR :: _) => None
           | Some (bl0, LCBRACE :: _) => None
           | Some (bl0, RCBRACE :: tu) =>
               parse_S'_ q' (SetEnumL (LCons a bl0))
                 (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) tu)
           | Some (bl0, LBRACK :: _) => None
           | Some (bl0, RBRACK :: _) => None
           | Some (bl0, IF_ :: _) => None
           | Some (bl0, THEN :: _) => None
           | Some (bl0, ELSE :: _) => None
           | None => None
           end
       | RPAREN :: _ =>
           match parse_N ((tlr ++ RCBRACE :: tr) ++ ts) with
           | Some (bl0, []) => None
           | Some (bl0, NAM _ :: _) => None
           | Some (bl0, NUM _ _ _ :: _) => None
           | Some (bl0, LPAREN :: _) => None
           | Some (bl0, RPAREN :: _) => None
           | Some (bl0, COMMA :: _) => None
           | Some (bl0, COLON :: _) => None
           | Some (bl0, DARR :: _) => None
           | Some (bl0, LET :: _) => None
           | Some (bl0, DEQ :: _) => None
           | Some (bl0, IN :: _) => None
           | Some (bl0, MEM :: _) => None
           | Some (bl0, SUBEQ :: _) => None
           | Some (bl0, VBAR :: _) => None
           | Some (bl0, LCBRACE :: _) => None
           | Some (bl0, RCBRACE :: tu) =>
               parse_S'_ q' (SetEnumL (LCons a bl0))
                 (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) tu)
           | Some (bl0, LBRACK :: _) => None
           | Some (bl0, RBRACK :: _) => None
           | Some (bl0, IF_ :: _) => None
           | Some (bl0, THEN :: _) => None
           | Some (bl0, ELSE :: _) => None
           | None => None
           end
       | COMMA :: _ =>
           match parse_N ((tlr ++ RCBRACE :: tr) ++ ts) with
           | Some (bl0, []) => None
           | Some (bl0, NAM _ :: _) => None
           | Some (bl0, NUM _ _ _ :: _) => None
           | Some (bl0, LPAREN :: _) => None
           | Some (bl0, RPAREN :: _) => None
           | Some (bl0, COMMA :: _) => None
           | Some (bl0, COLON :: _) => None
           | Some (bl0, DARR :: _) => None
           | Some (bl0, LET :: _) => None
           | Some (bl0, DEQ :: _) => None
           | Some (bl0, IN :: _) => None
           | Some (bl0, MEM :: _) => None
           | Some (bl0, SUBEQ :: _) => None
           | Some (bl0, VBAR :: _) => None
           | Some (bl0, LCBRACE :: _) => None
           | Some (bl0, RCBRACE :: tu) =>
               parse_S'_ q' (SetEnumL (LCons a bl0))
                 (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) tu)
           | Some (bl0, LBRACK :: _) => None
           | Some (bl0, RBRACK :: _) => None
           | Some (bl0, IF_ :: _) => None
           | Some (bl0, THEN :: _) => None
           | Some (bl0, ELSE :: _) => None
           | None => None
           end
       | COLON :: _ =>
           match parse_N ((tlr ++ RCBRACE :: tr) ++ ts) with
           | Some (bl0, []) => None
           | Some (bl0, NAM _ :: _) => None
           | Some (bl0, NUM _ _ _ :: _) => None
           | Some (bl0, LPAREN :: _) => None
           | Some (bl0, RPAREN :: _) => None
           | Some (bl0, COMMA :: _) => None
           | Some (bl0, COLON :: _) => None
           | Some (bl0, DARR :: _) => None
           | Some (bl0, LET :: _) => None
           | Some (bl0, DEQ :: _) => None
           | Some (bl0, IN :: _) => None
           | Some (bl0, MEM :: _) => None
           | Some (bl0, SUBEQ :: _) => None
           | Some (bl0, VBAR :: _) => None
           | Some (bl0, LCBRACE :: _) => None
           | Some (bl0, RCBRACE :: tu) =>
               parse_S'_ q' (SetEnumL (LCons a bl0))
                 (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) tu)
           | Some (bl0, LBRACK :: _) => None
           | Some (bl0, RBRACK :: _) => None
           | Some (bl0, IF_ :: _) => None
           | Some (bl0, THEN :: _) => None
           | Some (bl0, ELSE :: _) => None
           | None => None
           end
       | DARR :: _ =>
           match parse_N ((tlr ++ RCBRACE :: tr) ++ ts) with
           | Some (bl0, []) => None
           | Some (bl0, NAM _ :: _) => None
           | Some (bl0, NUM _ _ _ :: _) => None
           | Some (bl0, LPAREN :: _) => None
           | Some (bl0, RPAREN :: _) => None
           | Some (bl0, COMMA :: _) => None
           | Some (bl0, COLON :: _) => None
           | Some (bl0, DARR :: _) => None
           | Some (bl0, LET :: _) => None
           | Some (bl0, DEQ :: _) => None
           | Some (bl0, IN :: _) => None
           | Some (bl0, MEM :: _) => None
           | Some (bl0, SUBEQ :: _) => None
           | Some (bl0, VBAR :: _) => None
           | Some (bl0, LCBRACE :: _) => None
           | Some (bl0, RCBRACE :: tu) =>
               parse_S'_ q' (SetEnumL (LCons a bl0))
                 (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) tu)
           | Some (bl0, LBRACK :: _) => None
           | Some (bl0, RBRACK :: _) => None
           | Some (bl0, IF_ :: _) => None
           | Some (bl0, THEN :: _) => None
           | Some (bl0, ELSE :: _) => None
           | None => None
           end
       | LET :: _ =>
           match parse_N ((tlr ++ RCBRACE :: tr) ++ ts) with
           | Some (bl0, []) => None
           | Some (bl0, NAM _ :: _) => None
           | Some (bl0, NUM _ _ _ :: _) => None
           | Some (bl0, LPAREN :: _) => None
           | Some (bl0, RPAREN :: _) => None
           | Some (bl0, COMMA :: _) => None
           | Some (bl0, COLON :: _) => None
           | Some (bl0, DARR :: _) => None
           | Some (bl0, LET :: _) => None
           | Some (bl0, DEQ :: _) => None
           | Some (bl0, IN :: _) => None
           | Some (bl0, MEM :: _) => None
           | Some (bl0, SUBEQ :: _) => None
           | Some (bl0, VBAR :: _) => None
           | Some (bl0, LCBRACE :: _) => None
           | Some (bl0, RCBRACE :: tu) =>
               parse_S'_ q' (SetEnumL (LCons a bl0))
                 (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) tu)
           | Some (bl0, LBRACK :: _) => None
           | Some (bl0, RBRACK :: _) => None
           | Some (bl0, IF_ :: _) => None
           | Some (bl0, THEN :: _) => None
           | Some (bl0, ELSE :: _) => None
           | None => None
           end
       | DEQ :: _ =>
           match parse_N ((tlr ++ RCBRACE :: tr) ++ ts) with
           | Some (bl0, []) => None
           | Some (bl0, NAM _ :: _) => None
           | Some (bl0, NUM _ _ _ :: _) => None
           | Some (bl0, LPAREN :: _) => None
           | Some (bl0, RPAREN :: _) => None
           | Some (bl0, COMMA :: _) => None
           | Some (bl0, COLON :: _) => None
           | Some (bl0, DARR :: _) => None
           | Some (bl0, LET :: _) => None
           | Some (bl0, DEQ :: _) => None
           | Some (bl0, IN :: _) => None
           | Some (bl0, MEM :: _) => None
           | Some (bl0, SUBEQ :: _) => None
           | Some (bl0, VBAR :: _) => None
           | Some (bl0, LCBRACE :: _) => None
           | Some (bl0, RCBRACE :: tu) =>
               parse_S'_ q' (SetEnumL (LCons a bl0))
                 (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) tu)
           | Some (bl0, LBRACK :: _) => None
           | Some (bl0, RBRACK :: _) => None
           | Some (bl0, IF_ :: _) => None
           | Some (bl0, THEN :: _) => None
           | Some (bl0, ELSE :: _) => None
           | None => None
           end
       | IN :: _ =>
           match parse_N ((tlr ++ RCBRACE :: tr) ++ ts) with
           | Some (bl0, []) => None
           | Some (bl0, NAM _ :: _) => None
           | Some (bl0, NUM _ _ _ :: _) => None
           | Some (bl0, LPAREN :: _) => None
           | Some (bl0, RPAREN :: _) => None
           | Some (bl0, COMMA :: _) => None
           | Some (bl0, COLON :: _) => None
           | Some (bl0, DARR :: _) => None
           | Some (bl0, LET :: _) => None
           | Some (bl0, DEQ :: _) => None
           | Some (bl0, IN :: _) => None
           | Some (bl0, MEM :: _) => None
           | Some (bl0, SUBEQ :: _) => None
           | Some (bl0, VBAR :: _) => None
           | Some (bl0, LCBRACE :: _) => None
           | Some (bl0, RCBRACE :: tu) =>
               parse_S'_ q' (SetEnumL (LCons a bl0))
                 (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) tu)
           | Some (bl0, LBRACK :: _) => None
           | Some (bl0, RBRACK :: _) => None
           | Some (bl0, IF_ :: _) => None
           | Some (bl0, THEN :: _) => None
           | Some (bl0, ELSE :: _) => None
           | None => None
           end
       | MEM :: _ =>
           match parse_N ((tlr ++ RCBRACE :: tr) ++ ts) with
           | Some (bl0, []) => None
           | Some (bl0, NAM _ :: _) => None
           | Some (bl0, NUM _ _ _ :: _) => None
           | Some (bl0, LPAREN :: _) => None
           | Some (bl0, RPAREN :: _) => None
           | Some (bl0, COMMA :: _) => None
           | Some (bl0, COLON :: _) => None
           | Some (bl0, DARR :: _) => None
           | Some (bl0, LET :: _) => None
           | Some (bl0, DEQ :: _) => None
           | Some (bl0, IN :: _) => None
           | Some (bl0, MEM :: _) => None
           | Some (bl0, SUBEQ :: _) => None
           | Some (bl0, VBAR :: _) => None
           | Some (bl0, LCBRACE :: _) => None
           | Some (bl0, RCBRACE :: tu) =>
               parse_S'_ q' (SetEnumL (LCons a bl0))
                 (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) tu)
           | Some (bl0, LBRACK :: _) => None
           | Some (bl0, RBRACK :: _) => None
           | Some (bl0, IF_ :: _) => None
           | Some (bl0, THEN :: _) => None
           | Some (bl0, ELSE :: _) => None
           | None => None
           end
       | SUBEQ :: _ =>
           match parse_N ((tlr ++ RCBRACE :: tr) ++ ts) with
           | Some (bl0, []) => None
           | Some (bl0, NAM _ :: _) => None
           | Some (bl0, NUM _ _ _ :: _) => None
           | Some (bl0, LPAREN :: _) => None
           | Some (bl0, RPAREN :: _) => None
           | Some (bl0, COMMA :: _) => None
           | Some (bl0, COLON :: _) => None
           | Some (bl0, DARR :: _) => None
           | Some (bl0, LET :: _) => None
           | Some (bl0, DEQ :: _) => None
           | Some (bl0, IN :: _) => None
           | Some (bl0, MEM :: _) => None
           | Some (bl0, SUBEQ :: _) => None
           | Some (bl0, VBAR :: _) => None
           | Some (bl0, LCBRACE :: _) => None
           | Some (bl0, RCBRACE :: tu) =>
               parse_S'_ q' (SetEnumL (LCons a bl0))
                 (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) tu)
           | Some (bl0, LBRACK :: _) => None
           | Some (bl0, RBRACK :: _) => None
           | Some (bl0, IF_ :: _) => None
           | Some (bl0, THEN :: _) => None
           | Some (bl0, ELSE :: _) => None
           | None => None
           end
       | VBAR :: NAM x :: MEM :: ts0 =>
           match
             parse_S_ 1023 (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) ts0)
           with
           | Some (b, []) => None
           | Some (b, NAM _ :: _) => None
           | Some (b, NUM _ _ _ :: _) => None
           | Some (b, LPAREN :: _) => None
           | Some (b, RPAREN :: _) => None
           | Some (b, COMMA :: tu) =>
               match
                 parse_S_ 1023
                   (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts)
                      (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) tu))
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
                   parse_S'_ q' (SepRepL x InfMem a b c0)
                     (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) tv)
               | Some (c0, LBRACK :: _) => None
               | Some (c0, RBRACK :: _) => None
               | Some (c0, IF_ :: _) => None
               | Some (c0, THEN :: _) => None
               | Some (c0, ELSE :: _) => None
               | None => None
               end
           | Some (b, COLON :: _) => None
           | Some (b, DARR :: _) => None
           | Some (b, LET :: _) => None
           | Some (b, DEQ :: _) => None
           | Some (b, IN :: _) => None
           | Some (b, MEM :: _) => None
           | Some (b, SUBEQ :: _) => None
           | Some (b, VBAR :: _) => None
           | Some (b, LCBRACE :: _) => None
           | Some (b, RCBRACE :: tu) =>
               parse_S'_ q' (RepL x InfMem a b)
                 (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) tu)
           | Some (b, LBRACK :: _) => None
           | Some (b, RBRACK :: _) => None
           | Some (b, IF_ :: _) => None
           | Some (b, THEN :: _) => None
           | Some (b, ELSE :: _) => None
           | None => None
           end
       | VBAR :: NAM x :: SUBEQ :: ts0 =>
           match
             parse_S_ 1023 (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) ts0)
           with
           | Some (b, []) => None
           | Some (b, NAM _ :: _) => None
           | Some (b, NUM _ _ _ :: _) => None
           | Some (b, LPAREN :: _) => None
           | Some (b, RPAREN :: _) => None
           | Some (b, COMMA :: tu) =>
               match
                 parse_S_ 1023
                   (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) tu)
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
                   parse_S'_ q' (SepRepL x InfSubq a b c0)
                     (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) tv)
               | Some (c0, LBRACK :: _) => None
               | Some (c0, RBRACK :: _) => None
               | Some (c0, IF_ :: _) => None
               | Some (c0, THEN :: _) => None
               | Some (c0, ELSE :: _) => None
               | None => None
               end
           | Some (b, COLON :: _) => None
           | Some (b, DARR :: _) => None
           | Some (b, LET :: _) => None
           | Some (b, DEQ :: _) => None
           | Some (b, IN :: _) => None
           | Some (b, MEM :: _) => None
           | Some (b, SUBEQ :: _) => None
           | Some (b, VBAR :: _) => None
           | Some (b, LCBRACE :: _) => None
           | Some (b, RCBRACE :: tu) =>
               parse_S'_ q' (RepL x InfSubq a b)
                 (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) tu)
           | Some (b, LBRACK :: _) => None
           | Some (b, RBRACK :: _) => None
           | Some (b, IF_ :: _) => None
           | Some (b, THEN :: _) => None
           | Some (b, ELSE :: _) => None
           | None => None
           end
       | _ =>
           match parse_N ((tlr ++ RCBRACE :: tr) ++ ts) with
           | Some (bl0, []) => None
           | Some (bl0, NAM _ :: _) => None
           | Some (bl0, NUM _ _ _ :: _) => None
           | Some (bl0, LPAREN :: _) => None
           | Some (bl0, RPAREN :: _) => None
           | Some (bl0, COMMA :: _) => None
           | Some (bl0, COLON :: _) => None
           | Some (bl0, DARR :: _) => None
           | Some (bl0, LET :: _) => None
           | Some (bl0, DEQ :: _) => None
           | Some (bl0, IN :: _) => None
           | Some (bl0, MEM :: _) => None
           | Some (bl0, SUBEQ :: _) => None
           | Some (bl0, VBAR :: _) => None
           | Some (bl0, LCBRACE :: _) => None
           | Some (bl0, RCBRACE :: tu) =>
               parse_S'_ q' (SetEnumL (LCons a bl0))
                 (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) tu)
           | Some (bl0, LBRACK :: _) => None
           | Some (bl0, RBRACK :: _) => None
           | Some (bl0, IF_ :: _) => None
           | Some (bl0, THEN :: _) => None
           | Some (bl0, ELSE :: _) => None
           | None => None
           end
       end) = Some(c,ts)).
            {
              assert (L4:(match parse_N ((tlr ++ RCBRACE :: tr) ++ ts) with
       | Some (bl0, []) => None
       | Some (bl0, NAM _ :: _) => None
       | Some (bl0, NUM _ _ _ :: _) => None
       | Some (bl0, LPAREN :: _) => None
       | Some (bl0, RPAREN :: _) => None
       | Some (bl0, COMMA :: _) => None
       | Some (bl0, COLON :: _) => None
       | Some (bl0, DARR :: _) => None
       | Some (bl0, LET :: _) => None
       | Some (bl0, DEQ :: _) => None
       | Some (bl0, IN :: _) => None
       | Some (bl0, MEM :: _) => None
       | Some (bl0, SUBEQ :: _) => None
       | Some (bl0, VBAR :: _) => None
       | Some (bl0, LCBRACE :: _) => None
       | Some (bl0, RCBRACE :: tu) =>
           parse_S'_ q' (SetEnumL (LCons a bl0))
             (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) tu)
       | Some (bl0, LBRACK :: _) => None
       | Some (bl0, RBRACK :: _) => None
       | Some (bl0, IF_ :: _) => None
       | Some (bl0, THEN :: _) => None
       | Some (bl0, ELSE :: _) => None
       | None => None
       end) = Some(c,ts)).
              {
                rewrite <- app_assoc.
                rewrite IH2.
                - simpl. rewrite subl_tsubl_eq.
                   + now apply IH3a.
                   + apply subl_app. apply subl_app. apply sublcons. apply sublref.
                - simpl. tauto.
                - simpl. tauto.
              }
              rewrite L4.
              inversion H2.
              - simpl. reflexivity.
              - simpl. reflexivity.
            }
            rewrite L3.
            destruct a; try reflexivity.
            destruct i; try reflexivity.
            destruct a1; try reflexivity.
            assert (L4:(match parse_N ((tlr ++ RCBRACE :: tr) ++ ts) with
       | Some (bl0, []) => None
       | Some (bl0, NAM _ :: _) => None
       | Some (bl0, NUM _ _ _ :: _) => None
       | Some (bl0, LPAREN :: _) => None
       | Some (bl0, RPAREN :: _) => None
       | Some (bl0, COMMA :: _) => None
       | Some (bl0, COLON :: _) => None
       | Some (bl0, DARR :: _) => None
       | Some (bl0, LET :: _) => None
       | Some (bl0, DEQ :: _) => None
       | Some (bl0, IN :: _) => None
       | Some (bl0, MEM :: _) => None
       | Some (bl0, SUBEQ :: _) => None
       | Some (bl0, VBAR :: _) => None
       | Some (bl0, LCBRACE :: _) => None
       | Some (bl0, RCBRACE :: tu) =>
           parse_S'_ q' (SetEnumL (LCons (Infop (InfSet s) (Nam s0) a2) bl0))
             (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) tu)
       | Some (bl0, LBRACK :: _) => None
       | Some (bl0, RBRACK :: _) => None
       | Some (bl0, IF_ :: _) => None
       | Some (bl0, THEN :: _) => None
       | Some (bl0, ELSE :: _) => None
       | None => None
       end) = Some(c,ts)).
            {
              rewrite <- app_assoc. rewrite IH2.
              - simpl. rewrite subl_tsubl_eq.
                 + now apply IH3a.
                 + apply subl_app. apply subl_app. apply sublcons. apply sublref.
              - simpl. tauto.
              - simpl. tauto.
            }
            rewrite L4.
            inversion H2; try reflexivity.
         - omega.
         - inversion H2; exact I.
       }
       rewrite L2.
       destruct tl.
       * inversion H1.
       * destruct t; try reflexivity. inversion H1.
    + intros NBc q' ts Hq' Hs. simpl. rewrite <- app_assoc.
       assert (L2:(parse_S_SetBraces q' (tl ++ (tlr ++ RCBRACE :: tr) ++ ts)
         (fun a0 : LTree => a0)
         (fun (q0 : nat) (a0 : LTree) (ts0 : list TOKEN) =>
          parse_S'_ q0 a0 (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) ts0))
         (fun (q0 : nat) (ts0 : list TOKEN) =>
          parse_S_ q0 (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) ts0))
         (fun ts0 : list TOKEN =>
          parse_N (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) ts0))) = Some(c,ts)).
       {
         unfold parse_S_SetBraces.
         rewrite tsubl_ref.
         rewrite IH1a.
         - assert (L3:(match
             parse_N
               (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts)
                  ((tlr ++ RCBRACE :: tr) ++ ts))
           with
           | Some (bl0, []) => None
           | Some (bl0, NAM _ :: _) => None
           | Some (bl0, NUM _ _ _ :: _) => None
           | Some (bl0, LPAREN :: _) => None
           | Some (bl0, RPAREN :: _) => None
           | Some (bl0, COMMA :: _) => None
           | Some (bl0, COLON :: _) => None
           | Some (bl0, DARR :: _) => None
           | Some (bl0, LET :: _) => None
           | Some (bl0, DEQ :: _) => None
           | Some (bl0, IN :: _) => None
           | Some (bl0, MEM :: _) => None
           | Some (bl0, SUBEQ :: _) => None
           | Some (bl0, VBAR :: _) => None
           | Some (bl0, LCBRACE :: _) => None
           | Some (bl0, RCBRACE :: tu) =>
               parse_S'_ q' (SetEnumL (LCons a bl0))
                 (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) tu)
           | Some (bl0, LBRACK :: _) => None
           | Some (bl0, RBRACK :: _) => None
           | Some (bl0, IF_ :: _) => None
           | Some (bl0, THEN :: _) => None
           | Some (bl0, ELSE :: _) => None
           | None => None
           end) = Some(c,ts)).
         {
           rewrite tsubl_app_eq. rewrite <- app_assoc. rewrite IH2.
           - simpl. rewrite subl_tsubl_eq.
              + now apply IH3b.
              + apply subl_app. apply subl_app. apply sublcons. apply sublref. 
           - simpl. tauto.
           - simpl. tauto.
         }
            rewrite L3.
            inversion H2; simpl.
            + destruct a; try reflexivity.
               destruct i; try reflexivity.
               destruct a1; reflexivity.
            + destruct a; try reflexivity.
               destruct i; try reflexivity.
               destruct a1; reflexivity.
         - omega.
         - inversion H2; exact I.
       }
       rewrite L2.
       destruct tl.
       * inversion H1.
       * destruct t; try reflexivity. inversion H1.
    + intros Hq0 ts q' b d tu Hq' K1. simpl. destruct q'; try (exfalso; omega).
       rewrite <- app_assoc.
       assert (L2:(parse_S_SetBraces (S q') (tl ++ (tlr ++ RCBRACE :: tr) ++ ts)
         (fun b0 : LTree => ImplicitInfop b b0)
         (fun (q0 : nat) (a0 : LTree) (ts0 : list TOKEN) =>
          parse_S'_ q0 a0 (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) ts0))
         (fun (q0 : nat) (ts0 : list TOKEN) =>
          parse_S_ q0 (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) ts0))
         (fun ts0 : list TOKEN =>
          parse_N (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) ts0))) = Some(d,tu)).
       {
         unfold parse_S_SetBraces. rewrite tsubl_ref. rewrite IH1a.
         - assert (L3:(match
             parse_N
               (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts)
                  ((tlr ++ RCBRACE :: tr) ++ ts))
           with
           | Some (bl0, []) => None
           | Some (bl0, NAM _ :: _) => None
           | Some (bl0, NUM _ _ _ :: _) => None
           | Some (bl0, LPAREN :: _) => None
           | Some (bl0, RPAREN :: _) => None
           | Some (bl0, COMMA :: _) => None
           | Some (bl0, COLON :: _) => None
           | Some (bl0, DARR :: _) => None
           | Some (bl0, LET :: _) => None
           | Some (bl0, DEQ :: _) => None
           | Some (bl0, IN :: _) => None
           | Some (bl0, MEM :: _) => None
           | Some (bl0, SUBEQ :: _) => None
           | Some (bl0, VBAR :: _) => None
           | Some (bl0, LCBRACE :: _) => None
           | Some (bl0, RCBRACE :: tu0) =>
               parse_S'_ (S q') (ImplicitInfop b (SetEnumL (LCons a bl0)))
                 (tsubl (tl ++ (tlr ++ RCBRACE :: tr) ++ ts) tu0)
           | Some (bl0, LBRACK :: _) => None
           | Some (bl0, RBRACK :: _) => None
           | Some (bl0, IF_ :: _) => None
           | Some (bl0, THEN :: _) => None
           | Some (bl0, ELSE :: _) => None
           | None => None
           end) = Some(d,tu)).
            {
              rewrite tsubl_app_eq. rewrite <- app_assoc. rewrite IH2.
              - simpl. rewrite subl_tsubl_eq.
                 + subst q. apply pReln_S'_0 in H3. destruct H3. subst tr. subst c. exact K1.
                 + apply subl_app. apply subl_app. apply sublcons. apply sublref.
              - simpl. tauto.
              - simpl. tauto.
            }
            rewrite L3.
            inversion H2.
            + destruct a; try reflexivity. destruct i; try reflexivity. destruct a1; reflexivity.
            + destruct a; try reflexivity. destruct i; try reflexivity. destruct a1; reflexivity.
         - omega.
         - inversion H2; exact I.
       }
       rewrite L2.
       destruct tl.
       * inversion H1.
       * destruct t; try reflexivity. inversion H1.
 - intros q tl a tlr bl tr c H1 [IH1a [IH1b IH1c]] H2 IH2 H3 [IH3a IH3b]. (*** S_MTuple_S' ***)
    repeat split.
    + intros q' ts Hq' Hs. simpl. rewrite <- app_assoc. rewrite IH1a.
       * { rewrite tsubl_app_eq. rewrite <- app_assoc. rewrite IH2.
            - simpl. rewrite subl_tsubl_eq.
               + now apply IH3a.
               + apply subl_app. apply subl_app. apply sublcons. apply sublref.
            - simpl. tauto.
            - simpl. tauto.
          }
       * omega.
       * inversion H2; exact I.
    + intros NBc q' ts Hq' Hs. simpl. rewrite <- app_assoc. rewrite IH1a.
       * { rewrite tsubl_app_eq. rewrite <- app_assoc. rewrite IH2.
            - simpl. rewrite subl_tsubl_eq.
               + now apply IH3b.
               + apply subl_app. apply subl_app. apply sublcons. apply sublref.
            - simpl. tauto.
            - simpl. tauto.
          }
       * omega.
       * inversion H2; exact I.
    + intros Hq0 ts q' b d tu Hq' K1. simpl. destruct q'; try (exfalso; omega).
       rewrite <- app_assoc. rewrite IH1a.
       * { rewrite tsubl_app_eq. rewrite <- app_assoc. rewrite IH2.
            - simpl. rewrite subl_tsubl_eq.
               + rewrite Hq0 in H3. apply pReln_S'_0 in H3. destruct H3. subst tr. subst c. exact K1.
               + apply subl_app. apply subl_app. apply sublcons. apply sublref.
            - simpl. tauto.
            - simpl. tauto.
          }
       * omega.
       * inversion H2; exact I.
 - exact parse_S_lem_25. (*** S_IfThenElse ***)
 - intros tr H1. simpl. (*** TVs_Nil ***)
    destruct tr; simpl; try reflexivity.
    destruct t; simpl; try reflexivity.
    simpl in H1. tauto.
 - intros vtl xl tl vll H1 H2 IH2 tr K1. (*** TVs_UCons ***)
    Transparent parse_TVs.
    simpl. rewrite <- app_assoc. simpl.
    rewrite parse_Names_lem with (xl := xl).
    + rewrite subl_tsubl_eq.
       * rewrite IH2; try reflexivity. assumption.
       * apply subl_app. apply sublcons. apply sublref.
    + assumption.
    + simpl. tauto.
 - intros itok i vtl xl tl a tlr vll Hi H1 H2 [IH2a [IH2b IH2c]] H3 IH3 ts K1. (*** TVs_TCons ***)
    simpl. rewrite <- app_assoc. simpl.
    rewrite Hi.
    rewrite parse_Names_lem with (xl := xl).
    + rewrite subl_tsubl_eq.
       * { destruct i; simpl.
            - unfold parse_TVs_ascr. rewrite subl_tsubl_eq.
               + rewrite <- app_assoc.
                  simpl. rewrite IH2a.
                  * { rewrite subl_tsubl_eq.
                       * rewrite IH3; try reflexivity. assumption.
                       * apply subl_app. apply sublcons. apply subl_app. apply sublcons. apply sublref.
                     }
                  * omega.
                  * simpl. tauto.
               + apply subl_app. apply sublcons. apply sublref.
            - unfold parse_TVs_ascr. rewrite subl_tsubl_eq.
               + rewrite <- app_assoc.
                  simpl. rewrite IH2a.
                  * { rewrite subl_tsubl_eq.
                       * rewrite IH3; try reflexivity. assumption.
                       * apply subl_app. apply sublcons. apply subl_app. apply sublcons. apply sublref.
                     }
                  * omega.
                  * simpl. tauto.
               + apply subl_app. apply sublcons. apply sublref.
            - unfold parse_TVs_ascr. rewrite subl_tsubl_eq.
               + rewrite <- app_assoc.
                  simpl. rewrite IH2a.
                  * { rewrite subl_tsubl_eq.
                       * rewrite IH3; try reflexivity. assumption.
                       * apply subl_app. apply sublcons. apply subl_app. apply sublcons. apply sublref.
                     }
                  * omega.
                  * simpl. tauto.
               + apply subl_app. apply sublcons. apply sublref.
          }
       * apply subl_app. apply sublcons. apply sublref.
    + assumption.
    + destruct i; simpl; tauto.
 - intros tl K1 K2. (*** N_Nil ***)
    destruct tl; simpl; try reflexivity.
    destruct t; simpl; try reflexivity.
    simpl in K1. tauto.
 - intros tl a tlr bl H1 [IH1a [IH1b IH1c]] H2 IH2 tr K1 K2. (*** N_Cons ***)
    simpl. rewrite <- app_assoc.
    rewrite IH1a.
    + rewrite tsubl_app_eq. rewrite IH2.
       * reflexivity.
       * assumption.
       * assumption.
    + omega.
    + inversion H2.
       * simpl. assumption.
       * simpl. tauto.
Qed.

Lemma print_parse_S__id (q : nat) (a : LTree) :
 suppL q a -> parse_S_ q (print_S a) = Some(a,nil).
Proof.
  assert (L1:q <= q) by omega.
  intros H. generalize (print_S__thm q a H q L1). intros H2.
  destruct parse_S_lem as [_ [H3 _]].
  destruct (H3 q _ _ H2) as [H4 _].
  generalize (H4 q nil L1).
  rewrite <- app_nil_end. intros G. apply G.
  simpl. tauto.
Qed.

Lemma print_parse_S_id (a : LTree) :
 suppL 1023 a -> parse_S_ 1023 (print_S a) = Some(a,nil).
Proof.
  apply print_parse_S__id.
Qed.
