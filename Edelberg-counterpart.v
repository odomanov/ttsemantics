(** W.Edelberg, A Perspectivalist Semantics for the Attitudes (1995) *)
(** Используем counterpart relation    *)

(** Общие определения *)

Parameter man: Set.
Parameter C: man -> Prop(* в Чикаго *).

Parameter Murdered: man -> man -> Prop. (* x murdered y *)
Parameter Smith Johes:man.
Definition S (m:man): Prop := Murdered m Smith. (* убил Смита *)
Definition J (m:man): Prop := Murdered m Johes. (* убил Джонса *)
Definition nS(m:man): Prop := ~S(m).
Definition nJ(m:man): Prop := ~J(m).
Definition nC(m:man): Prop := ~C(m).
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

  Inductive Counterpart (Гin:Type) (Гout:Type)
            (ki:Гin->man) (ko:Гout->man) : Prop := 
    | cp: Counterpart Гin Гout ki ko.   (* конструктор отношений *)
  Axiom Crefl: forall Гin, forall Гout, forall ki, forall ko, 
    Counterpart Гin Гout ki ko = Counterpart Гout Гin ko ki.
  (* конструируем отношения *)
  Definition cab:= cp ГA ГB Am Bm.
  (* Definition cba:= cp ГB ГA Bm Am. *)

  (* типы двойников *)
  Definition Ck (Гin:Type) (Гout:Type) (ki:Гin->man) := 
    { ko:Гout->man | Counterpart Гin Гout ki ko }.

  (* близнецов с ГH нет *)
  Axiom noAH: forall ma, forall mh, Counterpart ГA ГH ma mh -> False.
  Axiom noBH: forall mb, forall mh, Counterpart ГB ГH mb mh -> False.

  (** Объекты, общие для разных контекстов  *)
  Record mABH := mkmABH
    { mABHa:ГA->man;
      mABHb:ГB->man;
      mABHh:ГH->man;
      cABHb: Counterpart ГA ГB mABHa mABHb;
      cABHh: Counterpart ГA ГH mABHa mABHh}.

  (* докажем, что двойников ГA и ГH нет *)
  Lemma noAinH:forall ma:ГA->man, Ck ГA ГH ma -> False.
  Proof.
    intros.
    destruct X.
    contradiction (noAH ma x).
  Qed.

  Lemma noHinA:forall mh:ГH->man, Ck ГH ГA mh -> False.
  Proof.
    intros.
    destruct X.
    rewrite Crefl in c.
    contradiction (noAH x mh).
  Qed.

  (* нет общих объектов *)
  Lemma noABH: mABH -> False.
  Proof.
    intro.
    destruct H as [ma _ mh _ H].
    contradiction (noAH ma mh).
  Qed.


  (** (1) Arsky thinks someone murdered Smith, 
          and Barsky thinks he is still in Chicago 
          (but there is no such murderer). *)
  (* True *)

  Fact C1_ASBC: exists w:{ m:ГA->man | forall ga:ГA, S (m ga) }, 
    exists c:Ck ГA ГB (proj1_sig w), forall gb:ГB, C (proj1_sig c gb).
  Proof.
    exists (exist _ Am AS).
    unfold Ck, proj1_sig.
    exists (exist _ Bm cab).
    apply BC.
  Qed.

  Fact C1_ASBC': forall ga:ГA, exists ma:ГA->man, S (ma ga) /\ 
    exists c:Ck ГA ГB ma, forall gb:ГB, C (proj1_sig c gb).
  Proof.
    intros.
    exists Am.
    split.
    * apply AS.
    * unfold Ck, proj1_sig.
      exists (exist _ Bm cab).
      apply BC.
  Qed.


  (** (2) Someone is believed by Arsky to have murdered Smith, 
          and Barsky thinks he is still in Chicago. *)
  (* False *)

  (* сначала докажем ложность 
    "Someone is believed by Arsky to have murdered Smith" *)
  Fact C1_AHSn: ~(exists mh:ГH->man, exists c:Ck ГH ГA mh, 
    forall ga:ГA, S (proj1_sig c ga)).
  Proof.
    unfold not.
    intro H.
    destruct H as [mh H].
    destruct H.
    contradiction (noHinA mh).
  Qed.

  (* теперь полностью (2) *)
  Fact C1_AHSBCn: ~(exists mh:ГH->man, exists c:Ck ГH ГA mh, 
    (forall ga:ГA, S (proj1_sig c ga)) /\
    (exists cb:Ck ГA ГB (proj1_sig c), forall gb:ГB, C (proj1_sig cb gb))).
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

  Reset noAH.

  (* конструируем отношения *)
  Definition cha:= cp ГH ГA Hm Am.
  Definition cbh:= cp ГB ГH Bm Hm.

  (** Объекты, общие для разных контекстов  *)
  Record mABH := mkmABH'
    { mABHa':ГA->man;
      mABHb':ГB->man;
      mABHh':ГH->man;
      cABHb': Counterpart ГA ГB mABHa' mABHb';
      cABHh': Counterpart ГH ГA mABHh' mABHa'}.

  Fact C1_AHSBC: exists mh:ГH->man, exists c:Ck ГH ГA mh, 
    (forall ga:ГA, S (proj1_sig c ga)) /\
    (exists cb:Ck ГA ГB (proj1_sig c), forall gb:ГB, C (proj1_sig cb gb)).
  Proof.
    exists Hm.
    unfold Ck.
    exists (exist _ Am cha).
    unfold proj1_sig.
    split.
    apply AS.
    exists (exist _ Bm cab).
    apply BC.
  Qed.

  (* докажем, используя общие объекты *)
  Fact C1_AHSBCs: exists mabh:mABH, 
    (forall ga:ГA, S(mABHa' mabh ga)) /\ (forall gb:ГB, C (mABHb' mabh gb)).
  Proof.
    exists (mkmABH' Am Bm Hm cab cha).
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

  (* тип man в Г, таких, что P (в Г) --- "killers" *)
  Definition k (Г:Type) (P:man->Prop) := { m:Г->man | forall g:Г, P (m g) }.

  Record ГB := mkГB
   {Bm:man;
    BS:S(Bm);
    BC:C(Bm)}.
  Record ГH := mkГH
   {Hm:man;
    HS:S(Hm)}.

  (** Отношения двойников -- между объектами в контексте *)

  Inductive Counterpart (Гin:Type) (Гout:Type)
            (ki:Гin->man) (ko:Гout->man) : Prop := 
    | cp: Counterpart Гin Гout ki ko.   (* конструктор отношений *)
  (* конструируем отношения *)
  Definition cbh:= cp ГB ГH Bm Hm.
  Definition chb:= cp ГH ГB Hm Bm.

  (* типы двойников *)
  Definition Ck (Гin:Type) (Гout:Type) (ki:Гin->man) := 
    { ko:Гout->man | Counterpart Гin Гout ki ko }.

  (** универсальная формулировка теоремы: "Гin верит, что Pin, и Гout верит, что Pout"
      Или: "существует некто в Гin, такой, что Pin и существует его двойник в Гout,
      такой, что Pout" *)
  Definition G (Гin:Type) (Гout:Type) (Pin:man->Prop) (Pout:man->Prop) := 
      exists mk: k Гin Pin,
      exists c:(Ck Гin Гout (proj1_sig mk)), 
      forall gout:Гout, Pout (proj1_sig c gout).

  (** Объекты, общие для разных контекстов  *)
  Record mBH := mkmBH
    { mBHb: ГB->man;
      mBHh: ГH->man;
      cBHb: Counterpart ГB ГH mBHb mBHh}.

  (** (3) Someone murdered Smith, 
          and Barsky thinks he is still in Chicago. *)
  (* True *)

  Fact C2_HSBC: G ГH ГB S C.
  Proof.
    exists (exist _ Hm HS).
    unfold proj1_sig.
    unfold Ck.
    exists (exist _ Bm chb).
    apply BC.
  Qed.

  Fact C2_HSBC': forall gh:ГH, exists mh:ГH->man, S(mh gh) /\
    exists c:Ck ГH ГB mh, forall gb:ГB, C(proj1_sig c gb).
  Proof.
    intro.
    exists Hm.
    split.
    apply HS.
    unfold proj1_sig.
    unfold Ck.
    exists (exist _ Bm chb).
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

  (* тип man в Г, таких, что P (в Г) --- "killers" *)
  Definition k (Г:Type) (P:man->Prop) := { m:Г->man | forall g:Г, P (m g) }.

  Record ГA := mkГA
   {Am1:man;
    Am2:man;
    A1S:S(Am1);
    A1J:~J(Am1);
    A1C:C(Am1);
    A2J:J(Am2);
    A2S:~S(Am2)}.
  (* убийцы в ГA *)
  Definition AmSk:k ГA S := exist _ Am1 A1S.
  Definition AmJk:k ГA J := exist _ Am2 A2J.
  (* есть только один убийца... *)
  Axiom uASk: forall mk:k ГA S, mk = AmSk.
  Axiom uAJk: forall mk:k ГA J, mk = AmJk.

  Record ГB := mkГB
   {Bm:man;
    BS:S(Bm);
    BJ:J(Bm)}.
  (* убийцы в ГB *)
  Definition BmSk:k ГB S := exist _ Bm BS.
  Definition BmJk:k ГB J := exist _ Bm BJ.
  (* есть только один убийца... *)
  Axiom uBSk: forall mk:k ГB S, mk = BmSk.
  Axiom uBJk: forall mk:k ГB J, mk = BmJk.

  Record ГH := mkГH
   {Hm:man;
    HnS:~S(Hm);
    HnJ:~J(Hm)}.


  (** Двойники -- между не объектами, а понятиями "убийца Смита" и
                  "убийца Джонса" *)

  Inductive Counterpart (Гin:Type) (Гout:Type) (P:man->Prop) 
            (ki:k Гin P) (ko:k Гout P) : Prop := 
    | cp: Counterpart Гin Гout P ki ko.   (* конструктор отношений *)
  (* конструируем отношения *)
  Definition cabs:= cp ГA ГB S AmSk BmSk.
  Definition cabj:= cp ГA ГB J AmJk BmJk.
  Definition cbas:= cp ГB ГA S BmSk AmSk.
  Definition cbaj:= cp ГB ГA J BmJk AmJk.

  (* типы двойников *)
  Definition Ck (Гin:Type) (Гout:Type) (P:man->Prop) (ki:k Гin P) := 
    { ko:k Гout P | Counterpart Гin Гout P ki ko }.


  (** универсальная формулировка теоремы: "Гin верит, что Pin, и Гout верит, что Pout"
      Или: "существует некто в Гin, такой, что Pin и существует его двойник в Гout,
      такой, что Pout" *)
  Definition G (Гin:Type) (Гout:Type) (Pin:man->Prop) (Pout:man->Prop) := 
      exists mk: k Гin Pin,
      exists c:(Ck Гin Гout Pin mk), 
      forall gout:Гout, Pout (proj1_sig (proj1_sig c) gout).


  (** (4) Arsky thinks someone murdered Smith, 
          and Barsky thinks he murdered Jones. *)
  (* True  *)

  Fact C3_ASBJ: G ГA ГB S J.
  Proof.
    exists AmSk.
    exists (exist _ BmSk cabs).
    apply BJ.
  Qed.

  (** (5) Barsky thinks someone murdered Jones, 
          and Arsky thinks he murdered Smith. *)
  (* False *)

  Fact C3_BJAS: forall ga:ГA, ~(G ГB ГA J S).
  Proof.
    unfold G.
    unfold Ck, BmJk, AmJk, proj1_sig, not.
    intros ga H.
    apply (A2S ga).
    destruct H as [jk H].
    destruct H as [ja H].
    destruct ja as [ja _].
    rewrite (uAJk ja) in H.
    apply H.
  Qed.

  (** (6) Barsky thinks that someone murdered Smith, 
          and Arsky thinks that he did not murder Jones. *)
  (* True *)

  Fact C3_BSAnJ: G ГB ГA S nJ.
  Proof.
    exists BmSk.
    exists (exist _ AmSk cbas).
    apply A1J.
  Qed.

  (** (7) Barsky thinks that someone murdered Smith, 
          and Arsky thinks that he is still in Chicago. *)
  (* True *)

  Fact C3_BSAC: G ГB ГA S C. 
  Proof.
    exists BmSk.
    exists (exist _ AmSk cbas).
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

  (* тип man в Г, таких, что P (в Г) --- "killers" *)
  Definition k (Г:Type) (P:man->Prop) := { m:Г->man | forall g:Г, P (m g) }.

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
  Definition AmSk:k ГA S := exist _ Am1 A1S.
  Definition AmJk:k ГA J := exist _ Am2 A2J.
  (* есть только один убийца... *)
  Axiom uASk: forall mk:k ГA S, mk = AmSk.
  Axiom uAJk: forall mk:k ГA J, mk = AmJk.

  Record ГH := mkГH
   {Hm:man;
    HS:S(Hm);
    HJ:J(Hm)}.
  (* убийцы в HOME *)
  Definition HmSk:k ГH S := exist _ Hm HS.
  Definition HmJk:k ГH J := exist _ Hm HJ.
  (* есть только один убийца... *)
  Axiom uHSk: forall mk:k ГH S, mk = HmSk.
  Axiom uHJk: forall mk:k ГH J, mk = HmJk.

  (** Двойники -- между не объектами, а понятиями "убийца Смита" и
                  "убийца Джонса" *)

  Inductive Counterpart (Гin:Type) (Гout:Type) (P:man->Prop) 
            (ki:k Гin P) (ko:k Гout P) : Prop := 
    | cp: Counterpart Гin Гout P ki ko.   (* конструктор отношений *)
  (* конструируем отношения *)
  Definition cahs:= cp ГA ГH S AmSk HmSk.
  Definition cahj:= cp ГA ГH J AmJk HmJk.
  Definition chas:= cp ГH ГA S HmSk AmSk.
  Definition chaj:= cp ГH ГA J HmJk AmJk.

  (* типы двойников *)
  Definition Ck (Гin:Type) (Гout:Type) (P:man->Prop) (ki:k Гin P) := 
    { ko:k Гout P | Counterpart Гin Гout P ki ko }.


  (** универсальная формулировка теоремы: "Гin верит, что Pin, и Гout верит, что Pout"
      Или: "существует некто в Гin, такой, что Pin и существует его двойник в Гout,
      такой, что Pout" *)
  Definition G (Гin:Type) (Гout:Type) (Pin:man->Prop) (Pout:man->Prop) := 
      exists mk: k Гin Pin,
      exists c:(Ck Гin Гout Pin mk), 
      forall gout:Гout, Pout (proj1_sig (proj1_sig c) gout).

  (* уникальность двойников (леммы не используются) *)
  Lemma ucHSk: forall kk:{ko : k ГA S | Counterpart ГH ГA S HmSk ko}, 
    kk = exist _ AmSk chas.
  Proof.
    intros.
    induction kk.
    assert (uu:x=AmSk).
    { apply uASk. }
    destruct p.
    rewrite uu.
    reflexivity.
  Qed.

  Lemma ucHJk: forall kk:{ko : k ГA J | Counterpart ГH ГA J HmJk ko}, 
    kk = exist _ AmJk chaj.
  Proof.
    intros.
    induction kk.
    assert (uu:x=AmJk).
    { apply uAJk. }
    destruct p.
    rewrite uu.
    reflexivity.
  Qed.

  (** (8) Someone murdered Smith, 
          and Arsky thinks he murdered Jones. *)
  (* False *)

  Fact C4_HSAJ: forall ga:ГA, ~(G ГH ГA S J).
  Proof.
    unfold G.
    unfold not, Ck, AmSk, proj1_sig.
    intros ga H.
    apply (A1J ga).
    destruct H as [ksh H].
    destruct H as [ksa H].
    destruct ksa as [ksa _].
    rewrite (uASk ksa) in H.
    unfold AmSk in H.
    apply H.
  Qed.

  (** (9) Someone murdered Jones, 
          and Arsky thinks he is still in Chicago. *)
  (* False *)

  Fact C4_HJAC: forall ga:ГA, ~(G ГH ГA J C).
  Proof.
    unfold G.
    unfold not, Ck, AmJk, proj1_sig.
    intros ga H.
    apply (A2C ga).
    destruct H as [khj H].
    destruct H as [kaj H].
    destruct kaj as [kaj _].
    rewrite (uAJk kaj) in H.
    unfold AmJk in H.
    apply H.
  Qed.

  (** (10) Someone murdered Smith, 
           and Arsky thinks he is still in Chicago. *)
  (* True *)

  Fact C4_SAC: G ГH ГA S C.
  Proof.
    exists HmSk.
    exists (exist _ AmSk chas).
    apply A1C.
  Qed.

  (** (11) Someone murdered Jones, 
           and Arsky thinks he is no longer in Chicago. *)
  (* True *)

  Fact C4_JAnC: G ГH ГA J nC.
  Proof.
    exists HmJk.
    exists (exist _ AmJk chaj).
    apply A2C.
  Qed.

  (** (12) Someone murdered Smith, 
           and Arsky thinks he didn’t murder Jones. *)
  (* True *)

  Fact C4_SAnJ: G ГH ГA S nJ.
  Proof.
    exists HmSk.
    exists (exist _ AmSk chas).
    apply A1J.
  Qed.

End Case4.