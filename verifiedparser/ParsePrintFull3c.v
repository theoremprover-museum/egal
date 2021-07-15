Require Export ParsePrintFull3a.

Opaque le_gt_dec.

Lemma parse_S_lem_22c
  (q : nat)
  (x : string)
  (i : SetInfixOp)
  (itok : TOKEN)
  (tl : list TOKEN)
  (a : LTree)
  (tlb : list TOKEN)
  (b : LTree)
  (tr : list TOKEN)
  (c : LTree)
  (Hx : nam_p x)
  (Hi : itok = SetInfixTOK i)
  (H1 : pReln_S_ 500 tl a)
  (IH1a : forall (q' : nat) (tr : list TOKEN),
         500 <= q' -> hardendp tr -> parse_S_ q' (tl ++ tr) = Some (a, tr))
  (IH1b : Binderishp a = false ->
         forall (q' : nat) (tr : list TOKEN),
         500 <= q' -> S'__endp q' tr -> parse_S_ q' (tl ++ tr) = Some (a, tr))
  (IH1c : 500 = 0 ->
         forall (tr : list TOKEN) (q : nat) (b d : LTree) (tu : list TOKEN),
         q > 0 ->
         parse_S'_ q (ImplicitInfop b a) tr = Some (d, tu) ->
         parse_S'_ q b (tl ++ tr) = Some (d, tu))
  (H2 : pReln_S_ 1010 tlb b)
  (IH2a : forall (q' : nat) (tr : list TOKEN),
         1010 <= q' -> hardendp tr -> parse_S_ q' (tlb ++ tr) = Some (b, tr))
  (IH2b : Binderishp b = false ->
         forall (q' : nat) (tr : list TOKEN),
         1010 <= q' ->
         S'__endp q' tr -> parse_S_ q' (tlb ++ tr) = Some (b, tr))
  (IH2c : 1010 = 0 ->
         forall (tr : list TOKEN) (q : nat) (b0 d : LTree) (tu : list TOKEN),
         q > 0 ->
         parse_S'_ q (ImplicitInfop b0 b) tr = Some (d, tu) ->
         parse_S'_ q b0 (tlb ++ tr) = Some (d, tu))
  (H3 : pReln_S'_ q tr (SepL x i a b) c)
  (IH3a : forall (q' : nat) (tr0 : list TOKEN),
         q <= q' ->
         hardendp tr0 ->
         parse_S'_ q' (SepL x i a b) (tr ++ tr0) = Some (c, tr0))
  (IH3b : Binderishp (SepL x i a b) = false ->
         Binderishp c = false ->
         forall (q' : nat) (tr0 : list TOKEN),
         q <= q' ->
         S'__endp q' tr0 ->
         parse_S'_ q' (SepL x i a b) (tr ++ tr0) = Some (c, tr0))
  (L1 : penv x = (None, None, None)) :
   q = 0 ->
   forall (tr0 : list TOKEN) (q0 : nat) (b0 d : LTree) (tu : list TOKEN),
   q0 > 0 ->
   parse_S'_ q0 (ImplicitInfop b0 c) tr0 = Some (d, tu) ->
   parse_S'_ q0 b0
     ((LCBRACE :: NAM x :: itok :: tl ++ VBAR :: tlb ++ RCBRACE :: tr) ++ tr0) =
   Some (d, tu).
Proof.
  intros Hq0 ts q' e d tu Hq' K1. subst q. apply pReln_S'_0 in H3. destruct H3. subst tr. subst c.
        simpl. destruct q'; try (exfalso; omega).
        unfold parse_S_SetBraces. rewrite tsubl_ref. simpl. rewrite L1. rewrite Hi. destruct i; simpl; unfold parse_S'_Infix. simpl.
        * { destruct (le_gt_dec 1023 500); try (exfalso; omega). rewrite tsubl_ref. rewrite <- app_assoc. rewrite IH1a.
             - case_eq (Binderishp a); intros Ba; simpl.
                + rewrite subl_tsubl_eq.
                   * { simpl. rewrite <- app_assoc. rewrite IH2a.
                        - simpl. rewrite subl_tsubl_eq.
                           + exact K1.
                           + apply sublcons. apply sublcons. apply subl_app. apply sublcons.
                              apply subl_app. apply sublcons. apply sublref.
                        - omega.
                        - simpl. exact I.
                      }
                   * apply sublcons. apply sublcons. apply subl_app. apply sublcons. apply sublref.
                + rewrite subl_tsubl_eq.
                   * { simpl. rewrite subl_tsubl_eq.
                        - rewrite <- app_assoc. rewrite IH2a.
                           + simpl. rewrite subl_tsubl_eq.
                              * exact K1.
                              * apply sublcons. apply sublcons. apply subl_app. apply sublcons.
                                 apply subl_app. apply sublcons. apply sublref.
                           + omega.
                           + exact I.
                        - apply sublcons. apply sublcons. apply subl_app. apply sublcons. apply sublref.
                      }
                   * apply subl_app. apply sublref.
             - omega.
             - exact I.
            }
        * { destruct (le_gt_dec 1023 500); try (exfalso; omega). rewrite tsubl_ref. rewrite <- app_assoc. rewrite IH1a.
             - case_eq (Binderishp a); intros Ba; simpl.
                + rewrite subl_tsubl_eq.
                   * { simpl. rewrite <- app_assoc. rewrite IH2a.
                        - simpl. rewrite subl_tsubl_eq.
                           + exact K1.
                           + apply sublcons. apply sublcons. apply subl_app. apply sublcons.
                              apply subl_app. apply sublcons. apply sublref.
                        - omega.
                        - simpl. exact I.
                      }
                   * apply sublcons. apply sublcons. apply subl_app. apply sublcons. apply sublref.
                + rewrite subl_tsubl_eq.
                   * { simpl. rewrite subl_tsubl_eq.
                        - rewrite <- app_assoc. rewrite IH2a.
                           + simpl. rewrite subl_tsubl_eq.
                              * exact K1.
                              * apply sublcons. apply sublcons. apply subl_app. apply sublcons.
                                 apply subl_app. apply sublcons. apply sublref.
                           + omega.
                           + exact I.
                        - apply sublcons. apply sublcons. apply subl_app. apply sublcons. apply sublref.
                      }
                   * apply subl_app. apply sublref.
             - omega.
             - exact I.
            }
Qed.

