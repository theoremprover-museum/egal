Require Export ParsePrintFull3a.

Opaque le_gt_dec.

Lemma parse_S_lem_25 :
   forall (q : nat) (tl1 : list TOKEN) (a : LTree) 
     (tl2 : list TOKEN) (b : LTree) (tl3 : list TOKEN) 
     (c : LTree),
   q > 0 ->
   pReln_S_ 1010 tl1 a ->
   (forall (q' : nat) (tr : list TOKEN),
    1010 <= q' -> hardendp tr -> parse_S_ q' (tl1 ++ tr) = Some (a, tr)) /\
   (Binderishp a = false ->
    forall (q' : nat) (tr : list TOKEN),
    1010 <= q' -> S'__endp q' tr -> parse_S_ q' (tl1 ++ tr) = Some (a, tr)) /\
   (1010 = 0 ->
    forall (tr : list TOKEN) (q0 : nat) (b0 d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b0 a) tr = Some (d, tu) ->
    parse_S'_ q0 b0 (tl1 ++ tr) = Some (d, tu)) ->
   pReln_S_ 1010 tl2 b ->
   (forall (q' : nat) (tr : list TOKEN),
    1010 <= q' -> hardendp tr -> parse_S_ q' (tl2 ++ tr) = Some (b, tr)) /\
   (Binderishp b = false ->
    forall (q' : nat) (tr : list TOKEN),
    1010 <= q' -> S'__endp q' tr -> parse_S_ q' (tl2 ++ tr) = Some (b, tr)) /\
   (1010 = 0 ->
    forall (tr : list TOKEN) (q0 : nat) (b0 d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b0 b) tr = Some (d, tu) ->
    parse_S'_ q0 b0 (tl2 ++ tr) = Some (d, tu)) ->
   pReln_S_ 1010 tl3 c ->
   (forall (q' : nat) (tr : list TOKEN),
    1010 <= q' -> hardendp tr -> parse_S_ q' (tl3 ++ tr) = Some (c, tr)) /\
   (Binderishp c = false ->
    forall (q' : nat) (tr : list TOKEN),
    1010 <= q' -> S'__endp q' tr -> parse_S_ q' (tl3 ++ tr) = Some (c, tr)) /\
   (1010 = 0 ->
    forall (tr : list TOKEN) (q0 : nat) (b0 d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b0 c) tr = Some (d, tu) ->
    parse_S'_ q0 b0 (tl3 ++ tr) = Some (d, tu)) ->
   (forall (q' : nat) (tr : list TOKEN),
    q <= q' ->
    hardendp tr ->
    parse_S_ q' ((IF_ :: tl1 ++ THEN :: tl2 ++ ELSE :: tl3) ++ tr) =
    Some (IfThenElseL a b c, tr)) /\
   (Binderishp (IfThenElseL a b c) = false ->
    forall (q' : nat) (tr : list TOKEN),
    q <= q' ->
    S'__endp q' tr ->
    parse_S_ q' ((IF_ :: tl1 ++ THEN :: tl2 ++ ELSE :: tl3) ++ tr) =
    Some (IfThenElseL a b c, tr)) /\
   (q = 0 ->
    forall (tr : list TOKEN) (q0 : nat) (b0 d : LTree) (tu : list TOKEN),
    q0 > 0 ->
    parse_S'_ q0 (ImplicitInfop b0 (IfThenElseL a b c)) tr = Some (d, tu) ->
    parse_S'_ q0 b0 ((IF_ :: tl1 ++ THEN :: tl2 ++ ELSE :: tl3) ++ tr) =
    Some (d, tu)).
Proof.
  intros q tl1 a tl2 b tl3 c Hq H1 [IH1a [IH1b IH1c]] H2 [IH2a [IH2b IH2c]] H3 [IH3a [IH3b IH3c]].
  repeat split.
  - intros q' tr Hq' K1. simpl. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl.
     rewrite IH1a.
     + rewrite subl_tsubl_eq.
        * { rewrite IH2a.
             - rewrite subl_tsubl_eq.
                + rewrite IH3a.
                   * reflexivity.
                   * omega.
                   * exact K1.
                + apply subl_app. apply sublcons. apply subl_app. apply sublcons. apply sublref.
             - omega.
             - exact I. (*** ELSE is a hardend ***)
           }
        * apply subl_app. apply sublcons. apply sublref.
     + omega.
     + exact I. (*** THEN is a hardend ***)
  - intros K1. simpl in K1. exfalso. discriminate K1.
  - intros Hq0. exfalso. omega.
Qed.