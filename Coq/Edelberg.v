(** W.Edelberg, A Perspectivalist Semantics for the Attitudes (1995) *)

(** Сигнатура: *)

Parameter man: Type.
Parameter S: man -> Prop(* убил Смита *).
Parameter J: man -> Prop(* убил Джонса *).
Parameter C: man -> Prop(* в Чикаго *).

(** * MODULE CASE1  *)

Module Case1.
(* Smith died of drowning. 
   Detectives Arsky and Barsky jointly conclude that Smith was murdered by  
      drowning, and that this explains his current condition.
   Neither detective has anyone in mind as a suspect, 
   but Barsky thinks that Smith’s murderer is still in Chicago, where the 
      body was found. 
   But Smith was not murdered, he drowned by accident. *)
  (** Смит утонул.  Детективы Арский и Барский%\textellipsis%  *)

  (** Определим контексты: *)

  Record ГA := mkГA
   {Am:man;
    AmS:S(Am)}.
  Record ГB := mkГB
   {Bm:man;
    BmS:S(Bm);
    BmC:C(Bm)}.
  Record ГH := mkГH
   {Hm:man}.

  (** Функция связи контекстов (расширения):  *)

  Definition fBA (gb:ГB):ГA := mkГA (Bm gb) (BmS gb).

  (** Функции в ГH не существуют, т.е. Арский и Барский никого конкретно 
      не подозревают. *)

  Axiom C1_AxA: (ГA -> ГH) -> False.
  Axiom C1_AxB: (ГB -> ГH) -> False.

  (** Простое утверждение: 
      Барский и Арский имеют в виду одного и того же человека. *)

  Lemma C1_AeqB: forall gb:ГB, Am (fBA gb) = Bm gb.
  Proof. auto. Qed.

  (** (1) Arsky thinks someone murdered Smith, 
          and Barsky thinks he is still in Chicago 
          (but there is no such murderer). *)
  (* True *)

  Fact C1_ASBC: exists m:ГA->man, 
    forall ga:ГA, S(m ga) /\ forall gb:ГB, C(m (fBA gb)).
  Proof.
    exists (fun ga:ГA => Am ga).
    split.
    apply AmS.
    apply BmC.
  Qed.

  Fact C1_ASBC': exists m:ГA->man, 
    { w:(forall ga:ГA, S(m ga)) | forall gb:ГB, C(m (fBA gb))}.
  Proof.
    exists (fun ga:ГA => Am ga).
    exists (fun ga:ГA => AmS ga).
    apply BmC.
  Qed.

  Fact C1_ASBC'': forall ga:ГA, 
    (exists w:(forall ga:ГA, { m:ГA->man | S(m ga)}),
      forall gb:ГB, C(proj1_sig(w ga) (fBA gb))).
  Proof.
    exists (fun ga:ГA => exist _ Am (AmS ga)).
    unfold proj1_sig.
    apply BmC.
  Qed.

  (** (2) Someone is believed by Arsky to have murdered Smith, 
          and Barsky thinks he is still in Chicago. *)
  (* False *)

  Fact C1_AHSBCn: ~(exists m:ГH->man, exists f:ГA->ГH, 
    exists Sm:(forall ga:ГA, S(m (f ga))), 
    forall gb:ГB, C(m (f (fBA gb)))).
  Proof.
    unfold not. intros H. 
    destruct H as [m H]. destruct H as [f H].
    apply C1_AxA. apply f.
  Qed.

  (* не существует f, такой, что ... *)
  Fact C1_AHSBCn': ~exists f:ГA->ГH, 
    exists m:ГH->man, exists Sm:(forall ga:ГA, S(m (f ga))), 
    forall gb:ГB, C(m (f (fBA gb))).
  Proof.
    unfold not. intros H. 
    destruct H as [f H]. 
    apply C1_AxA. apply f.
  Qed.


  (* теперь определим функции в ГH *)
  (* тогда (2) будет истинно *)
  
  Definition fAH (ga:ГA):ГH := mkГH (Am ga).
  Definition fBH (gb:ГB):ГH := mkГH (Bm gb).

  Fact C1_AHSBC: exists m:ГH->man, exists Sm:(forall ga:ГA, S(m (fAH ga))), 
    forall gb:ГB, C(m (fAH (fBA gb))).
  Proof.
    exists (fun gh:ГH => Hm gh).
    exists (fun ga:ГA => AmS ga).
    apply BmC.
  Qed.

  (* существует f, такая, что ... *)
  Fact C1_AHSBC': exists f:ГA->ГH, 
    exists m:ГH->man, exists Sm:(forall ga:ГA, S(m (f ga))), 
    forall gb:ГB, C(m (f (fBA gb))).
  Proof.
    exists fAH.
    exists (fun gh:ГH => Hm gh).
    exists (fun ga:ГA => AmS ga).
    apply BmC.
  Qed.

  Fact C1_AHSBC'': forall ga:ГA,
    (exists w:(forall ga:ГA, { m:ГH->man | S(m (fAH ga))} ),
      forall gb:ГB, C(proj1_sig(w ga) (fBH gb))).
  Proof.
    exists (fun ga:ГA => exist _ Hm (AmS ga)).
    unfold proj1_sig.
    apply BmC.
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
    BmS:S(Bm);
    BmC:C(Bm)}.
  Record ГH := mkГH
   {Hm:man;
    HmS:S(Hm)}.

  Definition fBH (gb:ГB):ГH := mkГH (Bm gb) (BmS gb).

  (** (3) Someone murdered Smith, 
          and Barsky thinks he is still in Chicago. *)
  (* True *)

  Fact C2_HSBC: exists m:ГH->man, forall gh:ГH, S(m gh) /\ 
    forall gb:ГB, C(m (fBH gb)).
  Proof.
    exists (fun gh:ГH => Hm gh).
    split.
    apply HmS.
    apply BmC.
  Qed.

  Fact C2_HSBC': forall gh:ГH,
    (exists w:(forall gh:ГH, { m:ГH->man | S(m gh)}),
      forall gb:ГB, C(proj1_sig(w gh) (fBH gb))).
  Proof.
    exists (fun gh:ГH => exist _ Hm (HmS gh)).
    unfold proj1_sig.
    apply BmC.
  Qed.

  (* то же для forall w *)
  (*   не доказано !! *)
  Fact C2_HSBC'': forall gh:ГH,
    (forall w:(forall gh:ГH, { m:ГH->man | S(m gh)}),
      forall gb:ГB, C(proj1_sig(w gh) (fBH gb))).
  Proof.
  Abort.

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
   {Am:man;
    Am2:man;
    AmS:S(Am);
    Am2J:J(Am2);
    Am2S:~S(Am2);
    AmJ:~J(Am);
    AmC:C(Am)}.
  Record ГB := mkГB
   {Bm:man;
    Bm2:man;
    BmS:S(Bm);
    Bm2J:J(Bm2);
    Beq:Bm=Bm2}.
  Record ГH := mkГH
   {Hm:man;
    HnS:~(exists m:man, S(m));
    HnJ:~(exists m:man, J(m))}.
  Record ГAB := mkГAB
   {ABm:man;
    ABm2:man;
    ABmS:S(ABm);
    ABm2J:J(ABm2)}.

  Definition fAAB (ga:ГA):ГAB := mkГAB (Am ga) (Am2 ga) (AmS ga) (Am2J ga).
  Definition fBAB (gb:ГB):ГAB := mkГAB (Bm gb) (Bm2 gb) (BmS gb) (Bm2J gb).

  (* функции в ГH не существуют *)
  Axiom C3_AxA: (ГA -> ГH) -> False.
  Axiom C3_AxB: (ГB -> ГH) -> False.

  (* begin hide *)
  (* определим отношение *)
  (* не используется пока *)
  Inductive rAB (ga:ГA) (gb:ГB):Prop :=
    | ex_rAB: (exists gab:ГAB, gab=fAAB(ga) /\ gab=fBAB(gb)) -> rAB ga gb.
  (* end hide *)

  (** (4) Arsky thinks someone murdered Smith, 
          and Barsky thinks he murdered Jones. *)
  (* True  *)

  Fact C3_ASBJ: { m:ГAB->man | (forall ga:ГA, S(m (fAAB ga))) /\
    (forall gb:ГB, J(m (fBAB gb)))}.
  Proof.
    exists ABm.
    split.
    apply AmS.
    intros.
    assert (H:ABm (fBAB gb)=ABm2 (fBAB gb)).
    { apply Beq. }
    rewrite H.
    apply ABm2J.
  Qed.

  Fact C3_ASBJ': { m:ГAB->man | 
    { w:(forall ga:ГA, S(m (fAAB ga))) | (forall gb:ГB, J(m (fBAB gb)))}  }.
  Proof.
    exists (fun gab:ГAB => ABm gab).
    exists (fun ga:ГA => AmS ga).
    intros.
    assert (H:ABm (fBAB gb)=ABm2 (fBAB gb)).
    { apply Beq. }
    rewrite H.
    apply ABm2J.
  Qed.

  Fact C3_ASBJ'': forall ga:ГA,
    (exists w:(forall ga:ГA, { m:ГAB->man | S(m (fAAB ga))}), 
      (forall gb:ГB, J(proj1_sig(w ga) (fBAB gb)))).
  Proof.
    exists (fun ga:ГA => exist _ ABm (AmS ga)).
    intros.
    unfold proj1_sig.
    assert (H:ABm (fBAB gb)=ABm2 (fBAB gb)).
    { apply Beq. }
    rewrite H.
    apply ABm2J.
  Qed.

  (* begin hide *)
  (* не доказано !! *)
  Fact C3_ASBJ''': forall ga:ГA,
    (exists w:(forall ga:ГA, { m:ГA->man | S(m ga)}), 
      (exists gab:ГAB, gab=(fAAB ga) /\ (forall gb:ГB, J(proj1_sig(w ga) ga)))).
  Proof.
    exists (fun ga:ГA => exist _ Am (AmS ga)).
    intros.
    unfold proj1_sig.
    exists (fAAB ga).
    split.
    auto.
    intros.
  Abort.
  (* end hide *)

  (** (5) Barsky thinks someone murdered Jones, 
          and Arsky thinks he murdered Smith. *)
  (* False *)

  (* first, in a sense C3_ASBJ already proofs this *)

  (* then let's try another interpretation *)
  (* (5) is False for ABm *)
  Fact C3_BJAS: forall ga:ГA,
    (~exists w:(forall gb:ГB, S(ABm (fBAB gb))), (forall ga:ГA, J(ABm (fAAB ga)))).
  Proof.
    intros. unfold not. intros H.
    destruct H as (H1, H2).
    assert (JA1:forall ga:ГA, J(Am ga)).
    { intros. apply H2. }
    set (J1:=JA1 ga).
    set (J2:=AmJ ga).
    contradiction.
  Qed.

  (** (6) Barsky thinks that someone murdered Smith, 
          and Arsky thinks that he did not murder Jones. *)
  (* True *)

  Fact C3_BSAnJ: { m:ГAB->man | (forall gb:ГB, S(m (fBAB gb))) /\
    (forall ga:ГA, ~J(m (fAAB ga)))}.
  Proof.
    exists (fun gab:ГAB => ABm gab).
    split.
    apply BmS.
    apply AmJ.
  Qed.

  (** (7) Barsky thinks that someone murdered Smith, 
          and Arsky thinks that he is still in Chicago. *)
  (* True *)

  Fact C3_BSAC: { m:ГAB->man | (forall gb:ГB, S(m (fBAB gb))) /\
    (forall ga:ГA, C(m (fAAB ga)))}.
  Proof.
    exists (fun gab:ГAB => ABm gab).
    split.
    apply BmS.
    apply AmC.
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
   {Am:man;
    Am2:man;
    AmS:S(Am);
    Am2J:J(Am2);
    AmJ:~J(Am);
    Am2S:~S(Am2);
    AmC:C(Am);
    Am2C:~C(Am2)}.
  Record ГH := mkГH
   {Hm:man;
    HmS:S(Hm);
    HmJ:J(Hm)}.
  Record ГAH := mkГAH
   {AHm:man;
    AHm2:man;
    AHmS:S(AHm);
    AHm2J:J(AHm2)}.

  Definition fAAH (ga:ГA):ГAH := mkГAH (Am ga) (Am2 ga) (AmS ga) (Am2J ga).
  Definition fHAH (gh:ГH):ГAH := mkГAH (Hm gh) (Hm gh) (HmS gh) (HmJ gh).

  (** (8) Someone murdered Smith, 
          and Arsky thinks he murdered Jones. *)
  (* False *)

  Fact C4_HSAJ: forall ga:ГA,
    (~exists w:(forall gh:ГH, S(AHm (fHAH gh)) ),
      (forall ga:ГA, J(AHm (fAAH ga)))).
  Proof.
    intros. unfold not. intros H.
    destruct H as [H1 H2].
    assert (JA:forall ga:ГA, J (Am ga)).
    { intros. apply H2. }
    set (J1:=AmJ ga).
    set (J2:=JA ga).
    contradiction.
  Qed.

  (* when does (8) become true? *)
  (*   when m=AHm2  *)
  Fact C4_SAJ: {m:ГAH->man | (forall gh:ГH, S(m (fHAH gh))) /\
    (forall ga:ГA, J(m (fAAH ga)))}.
  Proof.
    exists (fun gah:ГAH => AHm2 gah).
    split.
    apply HmS.
    apply Am2J.
  Qed.

  Fact C4_SAJ': forall gh:ГH,
    (exists w:(forall gh:ГH, { m:ГAH->man | S(m (fHAH gh)) } ),
      (forall ga:ГA, J(proj1_sig(w gh) (fAAH ga)))).
  Proof.
    exists (fun gh:ГH => exist _ AHm2 (AHmS (fHAH gh))).
    unfold proj1_sig.
    apply Am2J.
  Qed.

  (** (9) Someone murdered Jones, 
          and Arsky thinks he is still in Chicago. *)
  (* False *)

  Fact C4_HJAC: forall ga:ГA,
    (~exists w:(forall gh:ГH, J(AHm2 (fHAH gh)) ),
      (forall ga:ГA, C(AHm2 (fAAH ga)))).
  Proof.
    intros. unfold not. intros H.
    destruct H as [H1 H2].
    assert (JA:forall ga:ГA, C (Am2 ga)).
    { intros. apply H2. }
    set (J1:=Am2C ga).
    set (J2:=JA ga).
    contradiction.
  Qed.

  (* When does (9) become true? *)
  (*   when m=AHm  *)
  Fact C4_JAC: {m:ГAH->man | (forall gh:ГH, J(m (fHAH gh))) /\
    (forall ga:ГA, C(m (fAAH ga)))}.
  Proof.
    exists (fun gah:ГAH => AHm gah).
    split.
    apply HmJ.
    apply AmC.
  Qed.

  Fact C4_JAC': forall gh:ГH,
    (exists w:(forall gh:ГH, { m:ГAH->man | J(m (fHAH gh)) } ),
      (forall ga:ГA, C(proj1_sig(w gh) (fAAH ga)))).
  Proof.
    exists (fun gh:ГH => exist _ AHm (AHm2J (fHAH gh))).
    unfold proj1_sig.
    apply AmC.
  Qed.

  (** (10) Someone murdered Smith, 
           and Arsky thinks he is still in Chicago. *)
  (* True *)

  Fact C4_SAC: {m:ГAH->man | (forall gh:ГH, S(m (fHAH gh))) /\
    (forall ga:ГA, C(m (fAAH ga))) }.
  Proof.
    exists (fun gah:ГAH => AHm gah).
    split.
    apply HmS.
    apply AmC.
  Qed.

  Fact C4_SAC': forall gh:ГH,
    (exists w:(forall gh:ГH, { m:ГAH->man | S(m (fHAH gh)) } ),
      (forall ga:ГA, C(proj1_sig(w gh) (fAAH ga)))).
  Proof.
    exists (fun gh:ГH => exist _ AHm (AHmS (fHAH gh))).
    unfold proj1_sig.
    apply AmC.
  Qed.

  (** (11) Someone murdered Jones, 
           and Arsky thinks he is no longer in Chicago. *)
  (* True *)

  Fact C4_JAnC: {m:ГAH->man | (forall gh:ГH, J(m (fHAH gh))) /\
    (forall ga:ГA, ~C(m (fAAH ga)))}.
  Proof.
    exists (fun gah:ГAH => AHm2 gah).
    split.
    apply HmJ.
    apply Am2C.
  Qed.

  (** (12) Someone murdered Smith, 
           and Arsky thinks he didn’t murder Jones. *)
  (* True *)

  Fact C4_SAnJ: {m:ГAH->man | (forall gh:ГH, S(m (fHAH gh))) /\
    (forall ga:ГA, ~J(m (fAAH ga)))}.
  Proof.
    exists (fun gah:ГAH => AHm gah).
    split.
    apply HmS.
    apply AmJ.
  Qed.

End Case4.
