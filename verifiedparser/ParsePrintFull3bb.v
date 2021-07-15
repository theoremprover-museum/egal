Require Export ParsePrintFull3a.

Opaque le_gt_dec.

Lemma parse_S_lem_19 :
   forall (q : nat) (x : string) (mtok : BinderMid) (vtl : list TOKEN)
     (vll : list (list string * option (AscKind * LTree))) 
     (tl : list TOKEN) (a : LTree),
   q > 0 ->
   binder_midtok x = Some mtok ->
   pReln_TVs vtl vll ->
   (forall tr : list TOKEN,
    ~ LPARENp tr -> parse_TVs (vtl ++ tr) = Some (vll, tr)) ->
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
    parse_S_ q' ((NAM x :: vtl ++ (BinderMidTok mtok) :: tl) ++ tr) =
    Some (Binder x mtok vll a, tr)) /\
   (Binderishp (Binder x mtok vll a) = false ->
    forall (q' : nat) (tr : list TOKEN),
    q <= q' ->
    S'__endp q' tr ->
    parse_S_ q' ((NAM x :: vtl ++ (BinderMidTok mtok) :: tl) ++ tr) =
    Some (Binder x mtok vll a, tr)) /\
   (q = 0 ->
    forall (tr : list TOKEN) (q0 : nat) (b d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b (Binder x mtok vll a)) tr = Some (d, tu) ->
    parse_S'_ q0 b ((NAM x :: vtl ++ (BinderMidTok mtok) :: tl) ++ tr) = Some (d, tu)).
Proof.
 - intros q x mtok vtl vll tl a Hq Hxm H1 IH1 H2 [IH2a [IH2b IH2c]]. repeat split. (*** S_Binder_T ***)
    + intros q' tr Hq' Hr. 
       generalize Hxm. unfold binder_midtok. simpl.
       case_eq (penv x). intros [[p'|] oqk] [mtok'|]; try discriminate.
       * intros K1. exfalso. apply (penv_Preop_Binder x x p' mtok); try assumption; try reflexivity.
          unfold preop_priority. rewrite K1. reflexivity.
       * { intros K1 K2. inversion K2. subst mtok'. rewrite <- app_assoc. 
 (*** This is a ridiculously long assert. The problem is that I need to destruct oqk which results in this huge goal twice. I'm doing it once in this assert. I could define an auxiliary function to make this prettier. ***)
            assert (L1:(if NAMORASCTOKb (vtl ++ ((BinderMidTok mtok) :: tl) ++ tr)
       then
        let (xl, l) := parse_Names (vtl ++ ((BinderMidTok mtok) :: tl) ++ tr) in
        match l with
        | [] => None
        | NAM _ as tok1 :: ts =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match parse_S_ 1010 (tsubl (vtl ++ ((BinderMidTok mtok) :: tl) ++ tr) ts) with
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
        | Some (vll0, []) => None
        | Some (vll0, tok1 :: ts) =>
            if dec_eq_tok (BinderMidTok mtok) tok1
            then
             match parse_S_ 1010 (tsubl (vtl ++ ((BinderMidTok mtok) :: tl) ++ tr) ts) with
             | Some (a0, tu) => Some (Binder x mtok vll0 a0, tu)
             | None => None
             end
            else None
        | None => None
        end) = Some (Binder x mtok vll a, tr)).
                      { inversion H1.
(***
                        - simpl. destruct mtok; simpl.
                           + subst vtl. simpl in IH1.
                              rewrite IH1.
                              * { destruct (dec_eq_tok COMMA COMMA) as [K4|K4]; try tauto.
                                   rewrite tsubl_cons_eq.
                                   rewrite IH2a.
                                   - subst vll. reflexivity.
                                   - omega.
                                   - assumption.
                                 }
                              * simpl. tauto.
                           + subst vtl. simpl in IH1.
                              rewrite IH1.
                              * { destruct (dec_eq_tok DARR DARR) as [K4|K4]; try tauto.
                                   rewrite tsubl_cons_eq.
                                   rewrite IH2a.
                                   - subst vll. reflexivity.
                                   - omega.
                                   - assumption.
                                 }
                              * simpl. tauto.
***)
                        - simpl. destruct mtok; simpl.
                           + subst vtl. rewrite tsubl_cons_eq.
                              rewrite IH2a.
                              * reflexivity.
                              * omega.
                              * assumption.
                           + subst vtl. rewrite tsubl_cons_eq.
                              rewrite IH2a.
                              * reflexivity.
                              * omega.
                              * assumption.
                        - simpl. subst vtl. subst vll.
                           change (match
     parse_TVs ((LPAREN :: vtl0 ++ RPAREN :: tl0) ++ (BinderMidTok mtok) :: tl ++ tr)
   with
   | Some (vll1, nil) => None
   | Some (vll1, tok1 :: ts) =>
       if dec_eq_tok (BinderMidTok mtok) tok1
       then
        match
          parse_S_ 1010
            (tsubl (LPAREN :: (vtl0 ++ RPAREN :: tl0) ++ (BinderMidTok mtok) :: tl ++ tr) ts)
        with
        | Some (a0, tu) => Some (Binder x mtok vll1 a0, tu)
        | None => None
        end
       else None
   | None => None
   end = Some (Binder x mtok ((vl, None) :: vll0) a, tr)).
                           rewrite IH1.
                           + destruct (dec_eq_tok (BinderMidTok mtok) (BinderMidTok mtok)); try tauto.
                              rewrite subl_tsubl_eq.
                              * { rewrite IH2a.
                                   - reflexivity.
                                   - omega.
                                   - assumption.
                                 }
                              * apply sublcons. rewrite <- app_assoc. apply subl_app. simpl. apply sublcons.
                                 apply subl_app. apply sublcons. apply sublref.
                           + destruct mtok; simpl; tauto.
                        - simpl. destruct mtok; simpl.
                           + subst vtl. simpl in IH1.
                              rewrite IH1.
                              * { destruct (dec_eq_tok COMMA COMMA) as [K4|K4]; try tauto.
                                   rewrite subl_tsubl_eq.
                                   - rewrite IH2a.
                                      + subst vll. reflexivity.
                                      + omega.
                                      + assumption.
                                   - apply sublcons. apply subl_app. apply sublcons. apply sublref.
                                 }
                              * simpl. tauto.
                           + subst vtl. simpl in IH1.
                              rewrite IH1.
                              * { destruct (dec_eq_tok DARR DARR) as [K4|K4]; try tauto.
                                   rewrite subl_tsubl_eq.
                                   - rewrite IH2a.
                                      + subst vll. reflexivity.
                                      + omega.
                                      + assumption.
                                   - apply sublcons. apply subl_app. apply sublcons. apply sublref.
                                 }
                              * simpl. tauto.
                      }
          destruct oqk; exact L1.
          }
    + intros NBa. simpl in NBa. discriminate.
    + intros Hq0. exfalso. omega.
Qed.

