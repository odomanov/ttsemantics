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

(** Отношение двойников в общем виде *)

(* тип man в Г, таких, что P (в Г) --- "killers" *)
Definition k (Г:Type) (P:man->Prop) := { m:Г->man | forall g:Г, P (m g) }.

(* Двойники -- между не объектами, а понятиями "убийца Смита" и "убийца Джонса" *)
(* Поскольку в Case1, Case2 есть только убийца Смита, отношение двойников 
   можно устанавливать и между объектами. Но я делаю между понятиями для 
   единообразия с Case3, Case4.  *)
Inductive Counterpart (Гin:Type) (Гout:Type) (P:man->Prop) 
          (ki:k Гin P) (ko:k Гout P) : Prop := 
  | cp: Counterpart Гin Гout P ki ko.   (* конструктор отношений *)

(* рефлексивность отношения *)
Axiom Crefl: forall Гin, forall Гout, forall P, forall ki, forall ko,
  Counterpart Гin Гout P ki ko = Counterpart Гout Гin P ko ki.

(* типы двойников: двойники k Гin P в Гout *)
Definition Ck (Гin:Type) (Гout:Type) (P:man->Prop) (ki:k Гin P) := 
  { ko:k Гout P | Counterpart Гin Гout P ki ko }.

(** универсальная формулировка теоремы для всех Cases: 
    "Гin верит, что Pin, и Гout верит, что Pout"
    Или: "существует некто в Гin, такой, что Pin и существует его двойник в Гout,
    такой, что Pout" *)
Definition G (Гin:Type) (Гout:Type) (Pin:man->Prop) (Pout:man->Prop) := 
    exists mk: k Гin Pin,
    exists c:(Ck Гin Гout Pin mk), 
    forall gout:Гout, Pout (proj1_sig (proj1_sig c) gout).



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
  (* убийцы в ГA *)
  Definition AmSk:k ГA S := exist _ Am AS.
  (* есть только один убийца... *)
  Axiom uASk: forall mk:k ГA S, mk = AmSk.
  Record ГB := mkГB
   {Bm:man;
    BS:S(Bm);
    BC:C(Bm)}.
  (* убийцы в ГB *)
  Definition BmSk:k ГB S := exist _ Bm BS.
  (* есть только один убийца... *)
  Axiom uBSk: forall mk:k ГB S, mk = BmSk.
  Record ГH := mkГH
   {Hm:man;
    HS:~S(Hm)}.

  (** В контексте Арского есть один человек, которого он считает убийцей Смита,
      В контексте Барского есть также один человек, которого он считает убийцей 
      о котором он дополнительно думает, что он находится в Чикаго. 
      Контекст $\Gamma H$ обозначает актуальный, действительный или <<наш>> (Home)
      контекст, в котором мы просто предполагаем одного человека. *)

  (* конструируем отношения *)
  Definition cab:= cp _ _ _ AmSk BmSk.

  (** Объекты, общие для разных контекстов  *)
  Record mABH := mkmABH
    { mABHa:k ГA S;
      mABHb:k ГB S;
      mABHh:k ГH S;
      cABHb: Counterpart _ _ _ mABHa mABHb;
      cABHh: Counterpart _ _ _ mABHa mABHh}.

  (* близнецов с ГH нет (можно ли это доказать?) *)
  Axiom noAH: forall ma, forall mh, Counterpart ГA ГH S ma mh -> False.
  Axiom noBH: forall mb, forall mh, Counterpart ГB ГH S mb mh -> False.

  (* докажем для примера, что двойников ГA и ГH нет *)
  Lemma noAinH:forall ma:k ГA S, Ck ГA ГH S ma -> False.
  Proof.
    intros ma c.
    destruct c as [mh c].
    contradiction (noAH ma mh).
  Qed.

  Lemma noHinA:forall mh:k ГH S, Ck ГH ГA S mh -> False.
  Proof.
    intros mh c.
    destruct c as [ma c].
    rewrite Crefl in c.
    contradiction (noAH ma mh).
  Qed.

  (* а также нет общих объектов *)
  Lemma noABH: mABH -> False.
  Proof.
    intro H.
    destruct H as [ma _ mh _ H].
    contradiction (noAH ma mh).
  Qed.


  (** (1) Arsky thinks someone murdered Smith, 
          and Barsky thinks he is still in Chicago 
          (but there is no such murderer). *)
  (* True *)

  Fact C1_ASBC: G ГA ГB S C.
  Proof.
    exists (exist _ Am AS).
    exists (exist _ BmSk cab).
    apply BC.
  Qed.


  (** (2) Someone is believed by Arsky to have murdered Smith, 
          and Barsky thinks he is still in Chicago. *)
  (* False *)

  (* сначала докажем ложность 
    "Someone is believed by Arsky to have murdered Smith" *)
  Fact C1_AHSn: ~(G ГH ГA S S).
  Proof.
    unfold not, G, proj1_sig, Ck.
    intro H.
    destruct H as [mh H].
    destruct H as [c _].
    apply (noHinA mh).
    exact c.
  Qed.

  (* теперь полностью (2) *)
  Fact C1_AHSBCn: ~(exists mh:k ГH S, exists c:Ck _ ГA _ mh, 
    (forall ga:ГA, S (proj1_sig (proj1_sig c) ga)) /\
    (exists cb:Ck _ ГB _ (proj1_sig c), forall gb:ГB, C (proj1_sig (proj1_sig cb) gb))).
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
    (forall ga:ГA, S (proj1_sig(mABHa mabh) ga)) /\ 
    (forall gb:ГB, C (proj1_sig(mABHb mabh) gb))).
  Proof.
    unfold not.
    intros H.
    destruct H as [mabh _].
    contradiction noABH.
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
  (* убийцы в ГB *)
  Definition BmSk:k ГB S := exist _ Bm BS.
  (* есть только один убийца... *)
  Axiom uBSk: forall mk:k ГB S, mk = BmSk.

  Record ГH := mkГH
   {Hm:man;
    HS:S(Hm)}.
  (* убийцы в ГH *)
  Definition HmSk:k ГH S := exist _ Hm HS.
  (* есть только один убийца... *)
  Axiom uHSk: forall mk:k ГH S, mk = HmSk.

  (* конструируем отношения *)
  Definition cbh:= cp ГB ГH S BmSk HmSk.


  (** Объекты, общие для разных контекстов  *)
  Record mBH := mkmBH
    { mBHb: k ГB S;
      mBHh: k ГH S;
      cBHb: Counterpart _ _ _ mBHb mBHh}.

  (** (3) Someone murdered Smith, 
          and Barsky thinks he is still in Chicago. *)
  (* True *)

  Fact C2_HSBC: G ГH ГB S C.
  Proof.
    exists (exist _ Hm HS).
    pose (chb:=cbh).
    rewrite Crefl in chb.
    exists (exist _ BmSk chb).
    apply BC.
  Qed.

  (* докажем, используя общие объекты *)
  Fact C2_HSBCs: exists mbh:mBH, 
    forall gh:ГH, S (proj1_sig (mBHh mbh) gh) /\ 
    forall gb:ГB, C (proj1_sig (mBHb mbh) gb).
  Proof.
    exists (mkmBH BmSk HmSk cbh).
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


  (* конструируем отношения *)
  Definition cabs:= cp _ _ _ AmSk BmSk.
  Definition cabj:= cp _ _ _ AmJk BmJk.



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
    pose (cbas:=cabs).
    rewrite Crefl in cbas.
    exists (exist _ AmSk cbas).
    apply A1J.
  Qed.

  (** (7) Barsky thinks that someone murdered Smith, 
          and Arsky thinks that he is still in Chicago. *)
  (* True *)

  Fact C3_BSAC: G ГB ГA S C. 
  Proof.
    exists BmSk.
    pose (cbas:=cabs).
    rewrite Crefl in cbas.
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

  (* конструируем отношения *)
  Definition cahs:= cp _ _ _ AmSk HmSk.
  Definition cahj:= cp _ _ _ AmJk HmJk.
  Definition chas:= cp _ _ _ HmSk AmSk.
  Definition chaj:= cp _ _ _ HmJk AmJk.

  (* уникальность двойников (леммы не используются) *)
  Lemma ucHSk: forall kk:{ko : k ГA S | Counterpart _ _ _ HmSk ko}, 
    kk = exist _ AmSk chas.
  Proof.
    intro kk.
    induction kk as [kas c].
    assert (e:kas=AmSk).
    { apply uASk. }
    subst kas.
    destruct c.
    reflexivity.
  Qed.

  Lemma ucHJk: forall kk:{ko : k ГA J | Counterpart _ _ _ HmJk ko}, 
    kk = exist _ AmJk chaj.
  Proof.
    intro kk.
    induction kk as [kas c].
    assert (e:kas=AmJk).
    { apply uAJk. }
    subst kas.
    destruct c.
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