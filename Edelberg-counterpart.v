(** W.Edelberg, A Perspectivalist Semantics for the Attitudes (1995) *)
(** Используем counterpart relation    *)

(** Общие определения *)

Parameter man: Set.
Parameter C: man -> Prop(* в Чикаго *).

Parameter Murdered: man -> man -> Prop. (* x murdered y *)
Parameter Smith Johes:man.
Definition S (m:man): Prop := Murdered m Smith. (* убил Смита *)
Definition J (m:man): Prop := Murdered m Johes. (* убил Джонса *)
(* Definition K (M:man): Type := { m:man| Murdered m M }. (* убийцы M *) *)
Definition Sk:Type := { m:man | S m }. (* убийцы Смита *)
Definition Jk:Type := { m:man | J m }. (* убийцы Джонса *)




(** * MODULE CASE1  *)

Module Case1.
(* Smith died of drowning. 
   Detectives Arsky and Barsky jointly conclude that Smith was murdered by  
      drowning, and that this explains his current condition.
   Neither detective has anyone in mind as a suspect, 
   but Barsky thinks that Smith’s murderer is still in Chicago, where the 
      body was found. 
   But Smith was not murdered, he drowned by accident. *)
  (** Дело 1. Смит утонул.  Детективы Арский и Барский%\textellipsis%  *)

  (** Определим контексты: *)

  Record ГA := mkГA
   {Am:man;
    AS:S(Am)}.
  Record ГB := mkГB
   {Bm:man;
    BS:S(Bm);
    BC:C(Bm)}.
  Record ГH := mkГH
   {Hm:man;
    HS:~S(Hm)}.

  (** В контексте Арского есть один человек, которого он считает убийцей Смита,
      В контексте Барского есть также один человек, которого он считает убийцей 
      о котором он дополнительно думает, что он находится в Чикаго. 
      Контекст $\Gamma H$ обозначает актуальный, действительный или <<наш>> (Home)
      контекст, в котором мы просто предполагаем одного человека. *)

  (** Отношения двойников -- между объектами в контексте *)

  Definition CpartAB:= (ГA->man) -> (ГB->man) -> Prop.
  Inductive CAB : CpartAB :=
    | cab : CAB Am Bm.
  (* следующие отношения пусты *)
  Definition CpartAH:= (ГA->man) -> (ГH->man) -> Prop.
  Inductive CAH : CpartAH := .
  Definition CpartBH:= (ГB->man) -> (ГH->man) -> Prop.
  Inductive CBH : CpartBH := .

  (* типы двойников *)
  Definition cBinA (mb:ГB->man) := { ma:ГA->man | CAB ma mb }.
  Definition cAinB (ma:ГA->man) := { mb:ГB->man | CAB ma mb }.
  Definition cHinA (mh:ГH->man) := { ma:ГA->man | CAH ma mh }.
  Definition cAinH (ma:ГA->man) := { mh:ГH->man | CAH ma mh }.

  (** Объекты, общие для разных контекстов  *)
  Record mABH := mkmABH
    { mABHa:ГA->man;
      mABHb:ГB->man;
      mABHh:ГH->man;
      cABHb: CAB mABHa mABHb;
      cABHh: CAH mABHa mABHh}.

  (* докажем, что двойников ГA и ГH нет *)
  Lemma noHinA:forall mh:ГH->man, cHinA mh -> False.
  Proof.
    unfold cHinA.
    intros mh H.
    destruct H as [ma c].
    induction c.
  Qed.

  Lemma noAinH:forall ma:ГA->man, cAinH ma -> False.
  Proof.
    unfold cAinH.
    intros m H.
    destruct H as [mh c].
    induction c.
  Qed.

  (* нет общих объектов *)
  Lemma noABH: mABH -> False.
  Proof.
    intro.
    destruct H as [ma _ mh _ H].
    induction H.
  Qed.


  (** (1) Arsky thinks someone murdered Smith, 
          and Barsky thinks he is still in Chicago 
          (but there is no such murderer). *)
  (* True *)

  Fact C1_ASBC: exists w:{ m:ГA->man | forall ga:ГA, S (m ga) }, 
    exists c:cAinB(proj1_sig w), forall gb:ГB, C (proj1_sig c gb).
  Proof.
    exists (exist _ Am AS).
    unfold cAinB, proj1_sig.
    exists (exist _ Bm cab).
    apply BC.
  Qed.

  Fact C1_ASBC': forall ga:ГA, exists ma:ГA->man, S (ma ga) /\ 
    exists c:cAinB(ma), forall gb:ГB, C (proj1_sig c gb).
  Proof.
    intros.
    exists Am.
    split.
    apply AS.
    unfold cAinB, proj1_sig.
    exists (exist _ Bm cab).
    apply BC.
  Qed.


  (** (2) Someone is believed by Arsky to have murdered Smith, 
          and Barsky thinks he is still in Chicago. *)
  (* False *)

  (* сначала докажем ложность "Someone is believed by Arsky to have murdered Smith" *)
  Fact C1_AHSn: ~(exists mh:ГH->man, exists c:cHinA(mh), 
    forall ga:ГA, S (proj1_sig c ga)).
  Proof.
    unfold not. 
    intro H.
    destruct H as [mh H].
    destruct H.
    contradiction (noHinA mh).
  Qed.

  (* теперь полностью (2) *)
  Fact C1_AHSBCn: ~(exists mh:ГH->man, exists c:cHinA(mh), 
    (forall ga:ГA, S (proj1_sig c ga)) /\
    (exists cb:cAinB(proj1_sig c), forall gb:ГB, C (proj1_sig cb gb))).
  Proof.
    unfold not. 
    intro H.
    destruct H as [mh H].
    destruct H as [c _].
    apply (noHinA mh).
    exact c.
  Qed.

  (* докажем, используя общие объекты *)
  Fact C1_ASBCns: ~(exists mabh:mABH, 
    (forall ga:ГA, S(mABHa mabh ga)) /\ (forall gb:ГB, C (mABHb mabh gb))).
  Proof.
    unfold not.
    intros H.
    destruct H as [mabh _].
    contradiction noABH.
  Qed.


  (* теперь определим отношение двойников *)
  (* тогда (2) будет истинно *)

  Inductive CAH' : CpartAH := 
    | cah: CAH' Am Hm.
  Inductive CBH' : CpartBH := 
    | cbh: CBH' Bm Hm.

  (* типы двойников *)
  Definition cHinB' (mh:ГH->man): Type := { mb:ГB->man | CBH' mb mh }.
  Definition cHinA' (mh:ГH->man): Type := { ma:ГA->man | CAH' ma mh }.

  (** Объекты, общие для разных контекстов  *)
  Record mABH' := mkmABH'
    { mABHa':ГA->man;
      mABHb':ГB->man;
      mABHh':ГH->man;
      cABHb': CAB mABHa' mABHb';
      cABHh': CAH' mABHa' mABHh'}.

  Fact C1_AHSBC: exists mh:ГH->man, exists c:cHinA'(mh), 
    (forall ga:ГA, S (proj1_sig c ga)) /\
    (exists cb:cAinB(proj1_sig c), forall gb:ГB, C (proj1_sig cb gb)).
  Proof.
    exists Hm.
    unfold cHinA'.
    exists (exist _ Am cah).
    unfold proj1_sig.
    split.
    apply AS.
    unfold cAinB.
    exists (exist _ Bm cab).
    apply BC.
  Qed.

  (* докажем, используя общие объекты *)
  Fact C1_AHSBCs: exists mabh:mABH', 
    (forall ga:ГA, S(mABHa' mabh ga)) /\ (forall gb:ГB, C (mABHb' mabh gb)).
  Proof.
    exists (mkmABH' Am Bm Hm cab cah).
    unfold mABHa', mABHb'.
    split.
    apply AS.
    apply BC.
  Qed.

End Case1.






(** * MODULE CASE2   *)

Module Case2.
(* Smith died of drowning. 
   This is explained by the fact that someone intentionally drowned him. 
   Detective Barsky, who is investigating the case, sees Smith’s
     condition and on that basis comes to believe that Smith was murdered 
     by drowning. 
   Barsky believes that the murderer is still in Chicago. *)

  Record ГB := mkГB
   {Bm:man;
    BS:S(Bm);
    BC:C(Bm)}.
  Record ГH := mkГH
   {Hm:man;
    HS:S(Hm)}.

  (** Отношения двойников -- между объектами в контексте *)

  Definition CpartBH:= (ГB->man) -> (ГH->man) -> Prop.
  Inductive CBH : CpartBH :=
    | cbh : CBH Bm Hm.

  (* типы двойников *)
  Definition cBinH (mb:ГB->man) := { mh:ГH->man | CBH mb mh }.
  Definition cHinB (mh:ГH->man) := { mb:ГB->man | CBH mb mh }.

  (** Объекты, общие для разных контекстов  *)
  Record mBH := mkmBH
    { mBHb:ГB->man;
      mBHh:ГH->man;
      cBHb: CBH mBHb mBHh}.

  (** (3) Someone murdered Smith, 
          and Barsky thinks he is still in Chicago. *)
  (* True *)

  Fact C2_HSBC: exists w:{ mh:ГH->man | forall gh:ГH, S(mh gh) },
    exists c:cHinB(proj1_sig w), forall gb:ГB, C(proj1_sig c gb).
  Proof.
    exists (exist _ Hm HS).
    unfold proj1_sig.
    unfold cHinB.
    exists (exist _ Bm cbh).
    apply BC.
  Qed.

  Fact C2_HSBC': forall gh:ГH, exists mh:ГH->man, S(mh gh) /\
    exists c:cHinB(mh), forall gb:ГB, C(proj1_sig c gb).
  Proof.
    intro.
    exists Hm.
    split.
    apply HS.
    unfold proj1_sig.
    unfold cHinB.
    exists (exist _ Bm cbh).
    apply BC.
  Qed.

  (* докажем, используя общие объекты *)
  Fact C2_HSBCs: exists mbh:mBH, 
    forall gh:ГH, S(mBHh mbh gh) /\ 
    forall gb:ГB, C(mBHb mbh gb).
  Proof.
    exists (mkmBH Bm Hm cbh).
    split.
    apply HS.
    apply BC.
  Qed.

End Case2.





(** * MODULE CASE3   *)

Module Case3.
(* Arsky and Barsky investigate the apparent murder of Smith, and 
   they conclude that Smith was murdered by a single person, 
     though they have no one in mind as a suspect. 
   A few days later, they investigate the apparent murder of a second person, Jones,
     and again they conclude that Jones was murdered by a single person.
   At this point, however, a disagreement between the two detectives arises. 
   Arsky thinks that the two murderers are completely unrelated, and that 
   the person who murdered Smith, but not the one who murdered Jones, is still in
     Chicago. 
   Barsky, however, thinks that one and the same person murdered both Smith and Jones. 
   However, neither Smith nor Jones was really murdered. *)

  Record ГA := mkГA
   {Am1:man;
    Am2:man;
    A1S:S(Am1);
    A1J:~J(Am1);
    A1C:C(Am1);
    A2J:J(Am2);
    A2S:~S(Am2)}.
  (* убийцы в ГA *)
  Definition ASk := { m:ГA->man | forall ga:ГA, S (m ga) }.
  Definition AJk := { m:ГA->man | forall ga:ГA, J (m ga) }.
  Definition AmSk:ASk := exist _ Am1 A1S.
  Definition AmJk:AJk := exist _ Am2 A2J.

  Record ГB := mkГB
   {Bm:man;
    BS:S(Bm);
    BJ:J(Bm)}.
  (* убийцы в ГB *)
  Definition BSk := { m:ГB->man | forall gb:ГB, S (m gb) }.
  Definition BJk := { m:ГB->man | forall gb:ГB, J (m gb) }.
  Definition BmSk:BSk := exist _ Bm BS.
  Definition BmJk:BJk := exist _ Bm BJ.

  Record ГH := mkГH
   {Hm:man;
    HnS:~S(Hm);
    HnJ:~J(Hm)}.

  (** Двойники -- между не объектами, а интенсионалами "убийца Смита" и
                  "убийца Джонса" *)

  Definition cSAinB (c:ASk):BSk := match c with AmSk => BmSk end.
  Definition cJAinB (c:AJk):BJk := match c with AmJk => BmJk end.
  Definition cSBinA (c:BSk):ASk := match c with BmSk => AmSk end.
  Definition cJBinA (c:BJk):AJk := match c with BmJk => AmJk end.



  (** (4) Arsky thinks someone murdered Smith, 
          and Barsky thinks he murdered Jones. *)
  (* True  *)

  (* существует убийца Смита в ГA, ... *)
  Fact C3_ASBJ: exists sk:{ m:ГA->man | forall ga:ГA, S (m ga) },
    forall gb:ГB, J (proj1_sig (cSAinB sk) gb).
  Proof.
    unfold cSAinB, BmSk, proj1_sig.
    exists AmSk.
    apply BJ.
  Qed.

  (* то же с сокращением для ASk *)
  Fact C3_ASBJ': exists sk:ASk,
    forall gb:ГB, J (proj1_sig (cSAinB sk) gb).
  Proof.
    apply C3_ASBJ.
  Qed.

  (** (5) Barsky thinks someone murdered Jones, 
          and Arsky thinks he murdered Smith. *)
  (* False *)

  Fact C3_BJAS: forall ga:ГA, ~(exists jk:{ m:ГB->man | forall gb:ГB, J (m gb) },
    forall ga:ГA, S (proj1_sig (cJBinA jk) ga)).
  Proof.
    unfold cJBinA, BmJk, AmJk, proj1_sig, not.
    intros ga H.
    destruct H as [_ H].
    apply (A2S ga).
    apply H.
  Qed.

  (* с сокращением *)
  Fact C3_BJAS': forall ga:ГA, ~(exists jk:BJk,
    forall ga:ГA, S (proj1_sig (cJBinA jk) ga)).
  Proof.
    apply C3_BJAS.
  Qed.

  (** (6) Barsky thinks that someone murdered Smith, 
          and Arsky thinks that he did not murder Jones. *)
  (* True *)

  Fact C3_BSAnJ: exists sk:{ m:ГB->man | forall gb:ГB, S (m gb) },
    forall ga:ГA, ~J (proj1_sig (cSBinA sk) ga).
  Proof.
    exists BmSk.
    apply A1J.
  Qed.

  (** (7) Barsky thinks that someone murdered Smith, 
          and Arsky thinks that he is still in Chicago. *)
  (* True *)

  Fact C3_BSAC: exists sk:{ m:ГB->man | forall gb:ГB, S (m gb) },
    forall ga:ГA, C (proj1_sig (cSBinA sk) ga).
  Proof.
    exists BmSk.
    apply A1C.
  Qed.

End Case3.




(** * MODULE CASE4   *)

Module Case4.
(* Smith and Jones are dead. 
   A single person murdered both of them. 
   Detective Arsky investigates both cases, and comes to believe that 
   someone murdered Smith and that someone murdered Jones, 
     but he doesn’t have anyone in particular in mind as a suspect. 
   Arsky does not believe that Smith’s murderer and Jones’s murderer 
     are the same person. 
   He believes, for instance, that Smith’s murderer, but not Jones’s, 
     is still in Chicago. *)

  Record ГA := mkГA
   {Am1:man;
    Am2:man;
    A1S:S(Am1);
    A2J:J(Am2);
    A1J:~J(Am1);
    A2S:~S(Am2);
    A1C:C(Am1);
    A2C:~C(Am2)}.
  (* убийцы в ГA *)
  Definition ASk := { m:ГA->man | forall ga:ГA, S (m ga) }.
  Definition AJk := { m:ГA->man | forall ga:ГA, J (m ga) }.
  Definition AmSk:ASk := exist _ Am1 A1S.
  Definition AmJk:AJk := exist _ Am2 A2J.

  Record ГH := mkГH
   {Hm:man;
    HS:S(Hm);
    HJ:J(Hm)}.
  (* убийцы в HOME *)
  Definition HSk := { m:ГH->man | forall gh:ГH, S (m gh) }.
  Definition HJk := { m:ГH->man | forall gh:ГH, J (m gh) }.
  Definition HmSk:HSk := exist _ Hm HS.
  Definition HmJk:HJk := exist _ Hm HJ.

  (** Двойники -- между интенсионалами *)

  Definition cSAinH (c:ASk):HSk := match c with AmSk => HmSk end.
  Definition cJAinH (c:AJk):HJk := match c with AmJk => HmJk end.
  Definition cSHinA (c:HSk):ASk := match c with HmSk => AmSk end.
  Definition cJHinA (c:HJk):AJk := match c with HmJk => AmJk end.


  (** (8) Someone murdered Smith, 
          and Arsky thinks he murdered Jones. *)
  (* False *)

  Fact C4_HSAJ: forall ga:ГA, ~(exists sk:{ m:ГH->man | forall gh:ГH, S (m gh) },
    forall ga:ГA, J(proj1_sig (cSHinA sk) ga)).
  Proof.
    unfold not, cSHinA, AmSk, proj1_sig.
    intros ga H.
    destruct H as [_ H].
    apply (A1J ga).
    apply H.
  Qed.

  (** (9) Someone murdered Jones, 
          and Arsky thinks he is still in Chicago. *)
  (* False *)

  Fact C4_HJAC: forall ga:ГA, ~(exists jk:{ m:ГH->man | forall gh:ГH, J (m gh) },
      forall ga:ГA, C (proj1_sig (cJHinA jk) ga)).
  Proof.
    unfold not, cJHinA, HmJk, AmJk, proj1_sig.
    intros ga H.
    destruct H as [_ H].
    apply (A2C ga).
    apply H.
  Qed.

  (** (10) Someone murdered Smith, 
           and Arsky thinks he is still in Chicago. *)
  (* True *)

  Fact C4_SAC: exists sk:{ m:ГH->man | forall gh:ГH, S (m gh) },
    forall ga:ГA, C (proj1_sig (cSHinA sk) ga).
  Proof.
    exists HmSk.
    unfold cSHinA.
    unfold AmSk.
    unfold proj1_sig.
    apply A1C.
  Qed.

  (** (11) Someone murdered Jones, 
           and Arsky thinks he is no longer in Chicago. *)
  (* True *)

  Fact C4_JAnC: exists jk:{ m:ГH->man | forall gh:ГH, J (m gh) },
    forall ga:ГA, ~C (proj1_sig (cJHinA jk) ga).
  Proof.
    unfold cJHinA.
    unfold AmJk.
    unfold proj1_sig.
    exists HmJk.
    apply A2C.
  Qed.

  (** (12) Someone murdered Smith, 
           and Arsky thinks he didn’t murder Jones. *)
  (* True *)

  Fact C4_SAnJ: exists sk:{ m:ГH->man | forall gh:ГH, S (m gh) },
      forall ga:ГA, ~J (proj1_sig (cSHinA sk) ga).
  Proof.
    unfold cSHinA.
    unfold AmSk.
    unfold proj1_sig.
    exists HmSk.
    apply A1J.
  Qed.

End Case4.