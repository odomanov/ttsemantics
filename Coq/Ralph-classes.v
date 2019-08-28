(** Фраза Куайна "Ральф верит, что кто-то шпион" *)

(**   Используем typeclasses  *)

(* Сигнатура  *)
Parameter man:Set.
Parameter spy: man->Prop.




(** ***********************************************************)
(** Модуль: в актуальном контексте человек в шляпе и на пляже *)

Module Ralph_hb.

  (** Актуальный контекст *)
  Class ГA:Type := mkГA
    {Ah:man;       (* человек в шляпе *)
     Ab:man}.      (* человек на пляже *)

  (** Контекст Ральфа **)
  Class ГR:Type := mkГR
    {Ra:>ГA;           (* актуальный контекст *)
     spy_h: spy(Ah);   (* человек в шляпе --- шпион *)
     spy_b: ~spy(Ab)}. (* человек на пляже --- не шпион *)

  (* вспомогательные определения *)
  Definition Rh (gr:ГR):man := Ah.
  Definition Rb (gr:ГR):man := Ab.
  (** Определения для Rh, Rb неверны!!
      Как показано ниже, аналогичные определения в других модулях приводят к
      противоречиям.  *)
  (* пропозиция (spy h) в ГA и ГR *)
  Definition spyhR (gr:ГR):Prop := spy (Rh gr).
  Definition spyhA (ga:ГA):Prop := spy (Ah).
  (* пропозиция (spy b) в ГA и ГR *)
  Definition spybR (gr:ГR):Prop := spy (Rb gr).
  Definition spybA (ga:ГA):Prop := spy (Ab).

  (* Преобразование из Prop в контексте ГA в Prop в контексте ГR *)

  Definition PAtoR (P:ГA->Prop):ГR->Prop :=
    fun gr:ГR => P Ra.

  (** ************************************************************)
  (**   de dicto              *)
  (** ************************************************************)

  (** Докажем spy(h) для всех ГR --- de dicto *)

  Fact spyh: forall gr:ГR, spy (Rh gr).
  Proof.
    intros.
    apply spy_h.
  Qed.

  (* то же *)
  Fact spyh': forall gr:ГR, spyhR gr.
  Proof.
    apply spyh.
  Qed.

  (* Ральф верит, что существует человек...  *)
  Fact spy_ex: forall gr:ГR, exists m:ГR->man, spy (m gr).
  Proof.
    exists @Rh.
    apply spy_h.
  Qed.

  Fact spy_exn: forall gr:ГR, exists m:ГR->man, ~spy (m gr).
  Proof.
    exists @Rb.
    apply spy_b.
  Qed.

  Parameter гr:ГR.

  (** ********************************************************************)
  (**     de re                     *)
  (** ********************************************************************)

  (** Мнения для (spy Ah) *)

  (** (ГR -> (spy Ah)) истинно *)
  Fact spyh_A: forall gr:ГR, (PAtoR spyhA) gr.
  Proof.
    apply spyh.
  Qed.

  (** (ГR -> ~(spy Ah)) ложно *)
  Fact spyh_An : ~forall gr:ГR, ~((PAtoR spyhA) gr).
  Proof.
    unfold not.
    intros H.
    apply (H гr). apply spyh_A.
  Qed.

  (** Мнения для (spy Ab)  *)

  (** (ГR -> ~(spy Ab)) истинно *)
  Fact spyb_A : forall gr:ГR, ~((PAtoR spybA) gr).
  Proof.
    unfold not.
    unfold PAtoR.
    intros gr.
    apply spy_b.
  Qed.

  (** (ГR -> (spy Ab)) ложно *)
  Fact spyb_An: forall gr:ГR, ~forall gr:ГR, (PAtoR spybA) gr.
  Proof.
    unfold not.
    unfold PAtoR.
    unfold spybA.
    intros gr H.
    set (H1:=H gr).
    apply spy_b in H1.
    assumption.
  Qed.

  (** существует ГA->man ... *)

  (* существует человек, о котором Ральф верит, что он шпион *)
  Fact ex_man: exists m:ГA->man, forall gr:ГR, spy (m Ra).
  Proof.
    exists @Ah.
    intros.
    apply spy_h.
  Qed.

  (* существует человек, о котором Ральф верит, что он НЕ шпион *)
  Fact ex_mann: exists m:ГA->man, forall gr:ГR, ~spy (m Ra).
  Proof.
    exists @Ab.
    intros.
    apply spy_b.
  Qed.

  (* существует человек, о котором неверно, что Ральф верит, 
     что он шпион *)
  Fact ex_mann''': exists m:ГA->man, ~forall gr:ГR, spy (m Ra).
  Proof.
    unfold not.
    exists @Ab.
    intros H.
    set (H1:=H гr).
    apply spy_b in H1.
    assumption.
  Qed.

  (** *******************************************)
  (** Для пропозиции man->Prop в общем случае   *)
  (** *******************************************)

  (* (BR)~P -> ~(BR)P *)
  Lemma Rn_nR (P:man->Prop) (m:ГR->man): 
    (forall gr:ГR, ~P(m gr)) -> ~(forall gr:ГR, P(m gr)).
  Proof.
    unfold not.
    intros H1 H2.
    apply (H1 гr (H2 гr)).
  Qed.

  (* то же в контексте ГA *)
  Lemma Rn_nR_ga (P:man->Prop) (m:ГA->man): 
    (forall gr:ГR, ~P(m Ra)) -> ~(forall gr:ГR, P(m Ra)).
  Proof.
    set (mR:=fun gr:ГR => m(Ra)).
    apply (Rn_nR P mR).
  Qed.

  (** применим общий случай к (spy Ab) *)
  Lemma spyb_f: 
    (forall gr:ГR, ~spy(Ab)) -> ~(forall gr:ГR, spy(Ab)).
  Proof.
    apply (Rn_nR_ga spy (@Ab)).
  Qed.

  (** Итог: Ральф верит ~(spy Ab) -> неверно, что Ральф верит (spy Ab)    *)

  (** *******************************************)
  (** Для пропозиции ГR->Prop в общем случае   *)
  (** *******************************************)

  (* (BR)~P -> ~(BR)P *)
  Lemma Rn_nR' (P:ГR->Prop): 
    (forall gr:ГR, ~P(gr)) -> ~(forall gr:ГR, P(gr)).
  Proof.
    unfold not.
    intros H1 H2.
    apply (H1 гr (H2 гr)).
  Qed.

End Ralph_hb.







(** ***********************************************)
(** Модуль: человек в шляпе = человек на пляже  *)

Module Ralph_eq.

  (** Общий контекст *)
  Class ГRA:Type := mkГRA
    {RAh:man;           (* человек в шляпе *)
     RAb:man}.          (* человек на пляже *)

  (** Контекст Ральфа **)
  Class ГR:Type := mkГR
    {Rg:>ГRA;           (* общий контекст *)
     spy_h: spy(RAh);   (* человек в шляпе --- шпион *)
     spy_b: ~spy(RAb)}. (* человек на пляже --- не шпион *)

  (** Актуальный контекст *)
  Class ГA:Type := mkГA
    {Ag:>ГRA;           (* общий контекст *)
     Aeq:RAh=RAb}.      (* человек в шляпе = человек на пляже *)

  (** связывающий контекст *)
  Class ГS:Type := mkГS
    {Sga:>ГA;
     Sgr:>ГR;
     Seq:Ag=Rg}.        (* обший контекст в ГA и ГR совпадает *)

  (** Определения ниже противоречивы *)
  Definition Rh (gr:ГR):man := @RAh (@Rg gr).
  Definition Rb (gr:ГR):man := @RAb (@Rg gr).
  Definition Ah (ga:ГA):man := @RAh (@Ag ga).
  Definition Ab (ga:ГA):man := @RAb (@Ag ga).
  Definition Sh (gs:ГS):man := RAh.
  Definition Sb (gs:ГS):man := RAb.
  (* пропозиция (spy h) в ГA и ГR *)
  Definition spyhR (gr:ГR):Prop := spy (Rh gr).
  Definition spyhA (ga:ГA):Prop := spy (Ah ga).
  (* пропозиция (spy b) в ГA и ГR *)
  Definition spybR (gr:ГR):Prop := spy (Rb gr).
  Definition spybA (ga:ГA):Prop := spy (Ab ga).

  (** Доказываем противоречивость   *)

  Lemma eqShSb: forall gs:ГS, @Sh gs = @Sb gs.
  Proof.
    intros.
    unfold Sh. unfold Sb.
    apply Aeq.
  Qed.

  Lemma eqAhSh: forall gs, @Ah (@Sga gs) = @Sh gs.
  Proof.
    intros.
    unfold Ah. unfold Sh.
    reflexivity.
  Qed.

  Lemma eqRhSh: forall gs, @Rh (@Sgr gs) = @Sh gs.
  Proof.
    intros.
    unfold Rh. unfold Sh.
    rewrite Seq.
    reflexivity.
  Qed.

  Lemma eqAbSb: forall gs, @Ab (@Sga gs) = @Sb gs.
  Proof.
    intros.
    unfold Ab. unfold Sb.
    reflexivity.
  Qed.

  Lemma eqAhAb: forall gs, @Ah (@Sga gs) = @Ab (@Sga gs).
  Proof.
    intros.
    rewrite (eqAhSh gs).
    rewrite (eqAbSb gs).
    apply eqShSb.
  Qed.

  Lemma eqAhRh: forall gs:ГS, @Ah (@Sga gs) = @Rh (@Sgr gs).
  Proof.
    intros.
    rewrite (eqAhSh gs).
    rewrite (eqRhSh gs).
    reflexivity.
  Qed.

  Lemma spyhs: forall gs:ГS, spy (@Ah (@Sga gs)).
  Proof.
    intros.
    rewrite (eqAhRh gs).
    unfold Rh.
    apply spy_h.
  Qed.

  Lemma spybs: forall gs:ГS, ~spy (@Ab (@Sga gs)).
  Proof.
    intros.
    rewrite (eqAbSb gs).
    unfold Sb.
    rewrite Seq.
    apply spy_b.
  Qed.

  Parameter гs:ГS.

  Lemma spybsn: ~forall gs:ГS, spy (@Ab (@Sga gs)).
  Proof.
    unfold not.
    intros.
    apply (spybs гs).
    apply (H гs).
  Qed.

  Lemma spyhsn: ~forall gs:ГS, spy (@Ah (@Sga gs)).
  Proof.
    unfold not.
    intros.
    apply spybsn.
    intros.
    rewrite <-(eqAhAb gs).
    auto.
  Qed.

  (** ПРОТИВОРЕЧИЕ !!  *)

  Theorem contr:False.
  Proof.
    apply spyhsn.
    apply spyhs.
  Qed.

  Theorem contr':False.
  Proof.
    set (H1:=spyhsn).
    set (H2:=spyhs).
    contradiction.
  Qed.

  (* отменяем противоречивые определения  *)
  Reset Rh.

  (* Преобразование из Prop в контексте ГRA в Prop в контекстах ГR, ГA *)

  Definition PRAtoR (P:ГRA->Prop):ГR->Prop :=
    fun gr:ГR => P Rg.
  Definition PRAtoA (P:ГRA->Prop):ГA->Prop :=
    fun ga:ГA => P Ag.

  (* требуется для некоторых доказательств *)
  Parameter гr:ГR.

  (** ********************************************************************)
  (** Мнения de dicto     *)
  (** ********************************************************************)

  (** Мнения для (spy h)  *)

  (** (ГR -> (spy h)) истинно *)
  Fact spyh: forall gr:ГR, spyhR gr.
  Proof.
    intros.
    apply spy_h.
  Qed.

  (** (ГR -> ~(spy h)) ложно *)
  Fact spyhn : ~forall gr:ГR, ~(spyhR gr).
  Proof.
    unfold not.
    intros H.
    apply (H гr). apply spyh.
  Qed.

  (** ГR -> существует m, (spy m) *)
  (** Ральф верит, что существуют шпионы  *)
  Fact spyhm: forall gr:ГR, exists m:ГR->man, spy (m gr).
  Proof.
    intros.
    exists Rh.
    apply spy_h.
  Qed.

  (** Мнения для (spy b)  *)

  (** (ГR -> ~(spy b)) истинно *)
  Fact spyb : forall gr:ГR, ~(spybR gr).
  Proof.
    intros.
    apply spy_b.
  Qed.

  (** (ГR -> (spy b)) ложно *)
  Fact spybn: ~forall gr:ГR, spybR gr.
  Proof.
    unfold not.
    intros H.
    set (H1:=H гr).
    apply spy_b in H1.
    assumption.
  Qed.

  (** ГR -> существует m, ~(spy m) *)
  (** Ральф верит, что существуют НЕ шпионы  *)
  Fact spybm: forall gr:ГR, exists m:ГR->man, ~spy (m gr).
  Proof.
    intros.
    exists Rb.
    apply spy_b.
  Qed.

  (** ********************************************************************)
  (** Мнения de re        *)
  (** ********************************************************************)

  (** существует m в общем контексте, т.ч. ГR -> (spy m) *)
  Fact spyh_A: exists m:ГRA->man, forall gr:ГR, spy (m Rg).
  Proof.
    exists @RAh.
    intros.
    apply spy_h.
  Qed.

  (** существует m в общем контексте, т.ч. ГR -> ~(spy m) *)
  Fact spyb_A: exists m:ГRA->man, forall gr:ГR, ~spy (m Rg).
  Proof.
    exists @RAb.
    intros.
    apply spy_b.
  Qed.

  (** существует человек, о котором Ральф уверен, что он шпион, а мы знаем,
      что это человек на пляже  *)
  Fact spyhb: exists m:ГRA->man, (forall gr:ГR, spy (m Rg) /\
    (forall ga:ГA, Ab ga = m Ag)).
  Proof.
    exists @RAh.
    split.
    - apply spy_h.
    - unfold Ab. symmetry. apply Aeq.
  Qed.

  Fact spyh': exists w:{ m:ГRA->man | forall gr:ГR, spy (m Rg) },
    forall ga:ГA, Ab ga = proj1_sig w Ag.
  Proof.
    assert (H:forall gr:ГR,spy RAh).
    { intros. apply spy_h. }
    exists (exist _ (@RAh) H).
    unfold proj1_sig.
    intros.
    symmetry. apply Aeq.
  Qed.

  Fact spyh'': { w:{ m:ГRA->man | forall gr:ГR, spy (m Rg) } |
    forall ga:ГA, Ab ga = proj1_sig w Ag }.
  Proof.
    assert (H:forall gr:ГR,spy RAh).
    { intros. apply spy_h. }
    exists (exist _ (@RAh) H).
    unfold proj1_sig.
    intros.
    symmetry. apply Aeq.
  Qed.

  (** существует ф-я f ... *)

  (* существует f, (BR)(spy h) *)
  Fact ex_fh : exists (f:ГR->ГRA), forall gr:ГR, spy (@RAh (f gr)).
  Proof.
    exists @Rg.
    apply spyh.
  Qed.

  (* существует f, (BR)~(spy b) *)
  Fact ex_fb : exists (f:ГR->ГRA), forall gr:ГR, ~spy (@RAb (f gr)).
  Proof.
    exists @Rg.
    apply spyb.
  Qed.

  (** *******************************************)
  (** Для пропозиции ГR->Prop в общем случае   *)
  (** *******************************************)

  (* (BR)~P -> ~(BR)P *)
  Lemma Rn_nR_general (P:ГR->Prop): 
    (forall gr:ГR, ~P(gr)) -> ~(forall gr:ГR, P(gr)).
  Proof.
    unfold not.
    intros H1 H2.
    apply (H1 гr (H2 гr)).
  Qed.

  (** *******************************************)
  (** Для пропозиции man->Prop в общем случае   *)
  (** *******************************************)

  (* (BR)~P -> ~(BR)P *)
  Lemma Rn_nR (P:man->Prop) (m:ГR->man): 
    (forall gr:ГR, ~P(m gr)) -> ~(forall gr:ГR, P(m gr)).
  Proof.
    unfold not.
    intros H1 H2.
    apply (H1 гr (H2 гr)).
  Qed.

  (* то же в контексте ГA *)
  Lemma Rn_nR_ga (P:man->Prop) (m:ГA->man) (f:ГR->ГA): 
    (forall gr:ГR, ~P(m (f gr))) -> ~(forall gr:ГR, P(m (f gr))).
  Proof.
    set (mR:=fun gr:ГR => m(f(gr))).
    apply (Rn_nR P mR).
  Qed.

  (* применим общий случай к (spy Ah) *)
  Lemma spyyh_f (f:ГR->ГA): 
    (forall gr:ГR, ~spy(Ah (f gr))) -> ~(forall gr:ГR, spy(Ah (f gr))).
  Proof.
    apply (Rn_nR_ga spy Ah _).
  Qed.

  (** Итог: Ральф верит ~(spy Ah) -> неверно, что Ральф верит (spy Ah)    *)

End Ralph_eq.







(** ***********************************************)
(** Модуль: человек в шляпе = человек на пляже    *)
(**     контекст оценки                           *)

Module Ralph_eq_eval.

  (** Контекст Ральфа **)
  Class ГR:Type := mkГR
    {Rh:man;           (* человек в шляпе *)
     Rb:man;           (* человек на пляже *)
     spy_h: spy(Rh);   (* человек в шляпе шпион *)
     spy_b: ~spy(Rb)}. (* человек на пляже не шпион *)

  (** Контекст оценки *)
  Class ГE:Type := mkГE
    {Er:>ГR;
     Eeq:Rb=Rh}.

  (** определения  ниже притиворечивы *)

  Definition Eh (ge:ГE):man := Rh.
  Definition Eb (ge:ГE):man := Rb.
(*   (* пропозиция (spy h) в ГA и ГR *)
  Definition spyhR (gr:ГR):Prop := spy (Rh).
  Definition spyhA (ga:ГA):Prop := spy (Ah).
  (* пропозиция (spy b) в ГA и ГR *)
  Definition spybR (gr:ГR):Prop := spy (Rb).
  Definition spybA (ga:ГA):Prop := spy (Ab). *)

  (** Докажем противоречивость   *)

  Lemma spyeh: forall ge:ГE, spy (Eh ge).
  Proof.
    intros.
    apply spy_h.
  Qed.

  Lemma spyeb: forall ge:ГE, ~spy (Eb ge).
  Proof.
    intros.
    apply spy_b.
  Qed.

  Parameter гe:ГE.

  Lemma spyebn: ~forall ge:ГE, spy (Eb ge).
  Proof.
    unfold not.
    intro H.
    apply (spyeb гe).
    apply (H гe).
  Qed.

  Lemma EeqE: forall ge:ГE, Eb ge = Eh ge.
  Proof.
    intros.
    unfold Eh. unfold Eb. apply Eeq.
  Qed.

  Lemma spyehn: ~forall ge:ГE, spy (Eh ge).
  Proof.
    unfold not. intros.
    apply (spyeb гe).
    rewrite (EeqE гe).
    trivial.
  Qed.

  (** ПРОТИВОРЕЧИЕ !! *)

  Theorem contr: False.
  Proof.
    apply spyehn.
    apply spyeh.
  Qed.

  Theorem contr': False.
  Proof.
    set (H1:=spyehn).
    set (H2:=spyeh).
    contradiction.
  Qed.

  (* отменяем определения *)
  Reset Eh.

  (* Преобразование из Prop в контексте ГRA в Prop в контекстах ГR, ГA *)

(*   Definition PRAtoR (P:ГRA->Prop):ГR->Prop :=
    fun gr:ГR => P Rg.
  Definition PRAtoA (P:ГRA->Prop):ГA->Prop :=
    fun ga:ГA => P Ag. *)

  (* требуется для некоторых доказательств *)
  Parameter гr:ГR.

  (** ********************************************************************)
  (** Мнения de dicto     *)
  (** ********************************************************************)

  (** Мнения для (spy h)  *)

  (** (ГR -> (spy h)) истинно *)
  Fact spyh: forall gr:ГR, spy Rh.
  Proof.
    intros.
    apply spy_h.
  Qed.

  (** (ГR -> ~(spy h)) ложно *)
  Fact spyhn : ~forall gr:ГR, ~(spy Rh).
  Proof.
    unfold not.
    intros H.
    apply (H гr). apply spyh.
  Qed.

  (** ГR -> существует m, (spy m) *)
  (** Ральф верит, что существуют шпионы  *)
  Fact spyhm: forall gr:ГR, exists m:ГR->man, spy (m gr).
  Proof.
    intros.
    exists @Rh.
    apply spy_h.
  Qed.

  (** Мнения для (spy b)  *)

  (** (ГR -> ~(spy b)) истинно *)
  Fact spyb : forall gr:ГR, ~(spy Rb).
  Proof.
    intros.
    apply spy_b.
  Qed.

  (** (ГR -> (spy b)) ложно *)
  Fact spybn: ~forall gr:ГR, spy Rb.
  Proof.
    unfold not.
    intros H.
    set (H1:=H гr).
    apply spy_b in H1.
    assumption.
  Qed.

  (** ГR -> существует m, ~(spy m) *)
  (** Ральф верит, что существуют НЕ шпионы  *)
  Fact spybm: forall gr:ГR, exists m:ГR->man, ~spy (m gr).
  Proof.
    intros.
    exists @Rb.
    apply spy_b.
  Qed.

  (** ********************************************************************)
  (** Мнения de re        *)
  (** ********************************************************************)

  (** существует m в контексте оценки, т.ч. ГR -> (spy m) *)
  Fact spyh_A: forall ge:ГE, exists m:ГE->man, forall gr:ГR, spy (m ge).
  Proof.
    exists @Eh.
    intros.
    unfold Eh.
    apply spy_h.
  Qed.

  (** существует m в контексте оценки, т.ч. ГR -> ~(spy m) *)
  Fact spyb_A: forall ge:ГE, exists m:ГE->man, forall gr:ГR, ~spy (m ge).
  Proof.
    exists @Eb.
    intros.
    unfold Eb.
    apply spy_b.
  Qed.

  (** существует человек, о котором Ральф уверен, что он шпион, и он
      оценивается как человек на пляже  *)
  Fact spyhb: forall ge:ГE, exists m:ГE->man, 
    (forall gr:ГR, spy (m ge)) /\ m ge = Eb ge.
  Proof.
    exists @Eh.
    split.
    - intros. unfold Eh. apply spy_h.
    - unfold Eh. unfold Eb. symmetry. apply Eeq.
  Qed.

  Fact spyh': forall ge:ГE, exists w:{ m:ГE->man | forall gr:ГR, spy (m ge) },
    Eb ge = proj1_sig w ge.
  Proof.
    intros.
    assert (H:forall gr:ГR, spy (@Eh ge)).
    { intros. apply spy_h. }
    exists (exist _ (@Eh) H).
    unfold proj1_sig.
    unfold Eh. unfold Eb. apply Eeq.
  Qed.

  Fact spyh'': forall ge:ГE, { w:{ m:ГE->man | forall gr:ГR, spy (m ge) } |
    Eb ge = proj1_sig w ge }.
  Proof.
    intros.
    assert (H:forall gr:ГR, spy (@Eh ge)).
    { intros. apply spy_h. }
    exists (exist _ (@Eh) H).
    unfold proj1_sig.
    unfold Eh. unfold Eb. apply Eeq.
  Qed.

  (** существует ф-я f ... *)

  (* существует f, (BR)(spy h) *)
  Fact ex_fh : forall ge:ГE, 
    exists (f:ГE->ГR), forall gr:ГR, spy (@Rh (f ge)).
  Proof.
    exists @Er.
    intros.
    apply spy_h.
  Qed.

  (* существует f, (BR)~(spy b) *)
  Fact ex_fb : forall ge:ГE, 
    exists (f:ГE->ГR), forall gr:ГR, ~spy (@Rb (f ge)).
  Proof.
    exists @Er.
    intros.
    apply spy_b.
  Qed.

End Ralph_eq_eval.





(** **************************************************************)
(** Модуль: в актуальном контексте только Орткутт                *)
(**      контексты оценки                                        *)

Module Ralph_o.

  (** Актуальный контекст *)
  Class ГA:Type :=
    {o:man}.

  (** Контекст Ральфа **)
  Class ГR:Type := 
    {Rh:man;
     Rb:man;
     spy_h : spy(Rh);
     spy_b : ~spy(Rb)}.

  (** контексты оценки *)
  (*   Parameter ГC:Type. *)
  Class ГEH :=
   {EHa:>ГA;
    EHr:>ГR;
    EHeqh:o=Rh}.
  Class ГEB :=
   {EBa:>ГA;
    EBr:>ГR;
    EBeqb:o=Rb}.
  Class ГEC := (* противоречивый, как потом докажем *)
   {ECa:>ГA;
    RСr:>ГR;
    ECeqb:o=Rb;
    ECeqh:o=Rh}.

  Definition EHh (geh:ГEH): man := Rh.
  Definition EHb (geh:ГEH): man := Rb.
  Definition EBh (geb:ГEB): man := Rh.
  Definition EBb (geb:ГEB): man := Rb.

(*   Parameter гr:ГR. *)

  (** контекст ГEC противоречив *)

  Fact cont:forall gec:ГEC, False.
  Proof.
    intros.
    assert (H1:spy o).
    { rewrite ECeqh. apply spy_h. }
    assert (H2:~spy o).
    { rewrite ECeqb. apply spy_b. }
    contradiction.
  Qed.


  (** *************************************************************)
  (**   de dicto                    *)
  (** *************************************************************)
  
  (** докажем spy(h) для всех ГR  --- de dicto *)

  Fact spyh: forall gr:ГR, spy (Rh).
  Proof.
    intros.
    apply spy_h.
  Qed.

  Fact spyh_ex: forall gr:ГR, exists m:ГR->man, spy (m gr).
  Proof.
    intros.
    exists @Rh.
    apply spy_h.
  Qed.

  (** докажем ~spy(b) для всех ГR  --- de dicto *)

  Fact spyb: forall gr:ГR, ~spy (Rb).
  Proof.
    intros.
    apply spy_b.
  Qed.

  Fact spyb_ex: forall gr:ГR, exists m:ГR->man, ~spy (m gr).
  Proof.
    intros.
    exists @Rb.
    apply spy_b.
  Qed.

  (** ********************************************************************)
  (** de re                   *)
  (** ********************************************************************)

  (** spy o истинно в контексте ГEH *)
  Fact spyo_eh: forall geh:ГEH, spy (o).
  Proof.
    intros.
    rewrite EHeqh.
    apply spy_h.
  Qed.

  Parameter гeh:ГEH.
  Parameter гeb:ГEB.
  
  (** неверно, что ~(spy o), в контексте ГEH *)
  Fact spyo_ehn: ~forall geh:ГEH, ~spy (o).
  Proof.
    unfold not.
    intros H.
    apply (H гeh).
    apply spyo_eh.
  Qed.

  (** spy o ложно в контексте ГEB *)
  Fact spyo_eb: forall geb:ГEB, ~spy (o).
  Proof.
    intros.
    rewrite EBeqb.
    apply spy_b.
  Qed.

  (** неверно, что (spy o), в контексте ГEB *)
  Fact spyo_ebn: ~forall geb:ГEB, spy (o).
  Proof.
    unfold not.
    intros.
    set (H1:=H гeb).
    rewrite EBeqb in H1.
    apply spy_b in H1.
    assumption.
  Qed.

  (** существует человек в общем контексте... *)

  Fact spyeh_ex: forall geh:ГEH, exists m:ГEH->man, 
    forall gr:ГR, spy (m geh).
  Proof.
    exists EHh.
    intros.
    apply spy_h.
  Qed.

  Fact spyeb_ex: forall geb:ГEB, exists m:ГEB->man, 
    forall gr:ГR, ~spy (m geb).
  Proof.
    exists EBb.
    intros.
    apply spy_b.
  Qed.

  (** существует ф-я f ... *)

  (* существует f, (BR)(spy o) *)
(*   Fact ex_f : exists (f:ГR->ГA), forall gr:ГR, spy (@o (f gr)).
  Proof.
    exists fh.
    apply spyo_fh.
  Qed.

  (* существует f, (BR)~(spy o) *)
  Fact ex_fn : exists (f:ГR->ГA), forall gr:ГR, ~spy (o (f gr)).
  Proof.
    exists fb.
    apply spyo_fb.
  Qed.

  (* существует f, ~(BR)(spy o) *)
  Fact ex_fn' : exists (f:ГR->ГA), ~forall gr:ГR, spy (o (f gr)).
  Proof.
    exists fb.
    apply spyo_fbn.
  Qed. *)

  (** *******************************************)
  (** Для пропозиции man->Prop в общем случае   *)
  (** *******************************************)

  (* (BR)~P -> ~(BR)P *)
  Lemma Rn_nR (P:man->Prop) (m:ГR->man): 
    (forall gr:ГR, ~P(m gr)) -> ~(forall gr:ГR, P(m gr)).
  Proof.
    unfold not.
    intros H1 H2.
    apply (H1 (@EHr гeh) (H2 EHr)).
  Qed.

  (* то же в контексте ГA *)
  (* предполагаем, что существует f:ГR->ГA !! Но зачем? *)
  Lemma Rn_nR_ga (P:man->Prop) (m:ГA->man) (f:ГR->ГA): 
    (forall gr:ГR, ~P(m (f gr))) -> ~(forall gr:ГR, P(m (f gr))).
  Proof.
    set (mR:=fun gr:ГR => m(f(gr))).
    apply (Rn_nR P mR).
  Qed.

  (* применим общий случай к (spy o) *)
  Lemma spyo_f (f:ГR->ГA): 
    (forall gr:ГR, ~spy(o)) -> ~(forall gr:ГR, spy(o)).
  Proof.
    set (oo:=fun ga:ГA => o).
    apply (Rn_nR_ga spy oo _).
  Qed.

  (** Итог???: Ральф верит ~(spy o) -> неверно, что Ральф верит (spy o)    *)

  (** **********************************************)
  (** Мнения для (spy o) --- с использованием PAtoR *)
  (** **********************************************)

  (* Transforms Prop in ГA into Prop in ГR *)

  Definition PAtoEH (P:ГA->Prop) : ГEH->Prop :=
    fun (geh:ГEH) => P EHa.
  Definition PAtoEB (P:ГA->Prop) : ГEB->Prop :=
    fun (geb:ГEB) => P EBa.

  (* пропозиция (spy o) в ГA *)
  Definition spyo:ГA->Prop := fun (ga:ГA) => spy (@o ga).

  (** (ГR -> (spy o)) истинно *)
  Fact spyo_h_inR: forall (geh:ГEH), (PAtoEH spyo) geh.
  Proof.
    unfold PAtoEH.
    intros.
    unfold spyo.
    rewrite EHeqh.
    apply spy_h.
  Qed.

  (** (ГR -> (spy o)) ложно *)
  Fact spyo_b_inR : ~ forall (geb:ГEB), (PAtoEB spyo) geb.
  Proof.
    unfold not.
    unfold PAtoEB.
    intros H.
    set (H1:=H гeb).
    unfold spyo in H1.
    rewrite EBeqb in H1.
    apply spy_b in H1.
    assumption.
  Qed.

  (** существует ГA->man, ГR ... *)

  (* при некотором ГR мы верим, что существует человек, о котором Ральф верит, 
     что он шпион *)
  Fact ex_man: forall ga:ГA, exists m:ГA->man, forall geh:ГEH, spy (m (EHa)).
  Proof.
    intros.
    exists @o.
    apply spyo_eh.
  Qed.

  (* то же с PAtoR *)
  Fact ex_man': forall ga:ГA, exists m:ГA->man, forall geh:ГEH, (PAtoEH spyo) geh.
  Proof.
    intros.
    exists @o.
    apply spyo_eh.
  Qed.

  (* при некотором ГR мы верим, что существует человек, о котором Ральф верит, 
     что он НЕ шпион *)
  Fact ex_mann: forall ga:ГA, exists m:ГA->man, forall geb:ГEB, ~spy (m (EBa)).
  Proof.
    intros.
    exists @o.
    apply spyo_eb.
  Qed.

  (* то же с PAtoR *)
  Definition spyA (m:ГA->man):ГA->Prop := fun (ga:ГA) => spy (m ga).

  Fact ex_mann': forall ga:ГA, 
    exists m:ГA->man, forall geb:ГEB, ~(PAtoEB (spyA m)) geb.
  Proof.
    apply ex_mann.
  Qed.

  Fact ex_mann'': forall ga:ГA, 
    exists m:ГA->man, ~forall geb:ГEB, (PAtoEB (spyA m)) geb.
  Proof.
    intros.
    exists @o.
    apply spyo_ebn.
  Qed.

End Ralph_o.