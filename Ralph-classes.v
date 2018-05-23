(** Фраза Куайна "Ральф верит, что кто-то шпион" *)

(**   Используем typeclasses  *)

(* Сигнатура  *)
Parameter man:Set.
Parameter spy: man->Prop.

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
  (* пропозиция (spy h) в ГA и ГR *)
  Definition spyhR (gr:ГR):Prop := spy (Rh gr).
  Definition spyhA (ga:ГA):Prop := spy (Ah).
  (* пропозиция (spy b) в ГA и ГR *)
  Definition spybR (gr:ГR):Prop := spy (Rb gr).
  Definition spybA (ga:ГA):Prop := spy (Ab).

  (* Преобразование из Prop в контексте ГA в Prop в контексте ГR *)

  Definition PAtoR (P:ГA->Prop):ГR->Prop :=
    fun gr:ГR => P Ra.

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

  Parameter гr:ГR.

  (** ********************************************************************)
  (** Мнения для (spy Ah)  *)
  (** ********************************************************************)

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

  (** ********************************************************************)
  (** Мнения для (spy Ab)  *)
  (** ********************************************************************)

  (** (ГR -> ~(spy Ab)) истинно *)
  Fact spyb_A : forall gr:ГR, ~((PAtoR spybA) gr).
  Proof.
    unfold not.
    unfold PAtoR.
    intros gr.
    apply spy_b.
  Qed.

  (** (ГR -> (spy Ab)) ложно *)
  Fact spyb_An: ~forall gr:ГR, (PAtoR spybA) gr.
  Proof.
    unfold not.
    unfold PAtoR.
    unfold spybA.
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
     spy_h: spy(RAh);   (* человек в шляпе шпион *)
     spy_b: ~spy(RAb)}. (* человек на пляже не шпион *)

  (** Актуальный контекст *)
  Class ГA:Type := mkГA
    {Ag:>ГRA;           (* общий контекст *)
     Aeq:RAh=RAb}.      (* человек в шляпе = человек на пляже *)

  (* вспомогательные определения *)
  Definition Rh (gr:ГR):man := @RAh (@Rg gr).
  Definition Rb (gr:ГR):man := @RAb (@Rg gr).
  Definition Ah (ga:ГA):man := @RAh (@Ag ga).
  Definition Ab (ga:ГA):man := @RAb (@Ag ga).
  (* пропозиция (spy h) в ГA и ГR *)
  Definition spyhR (gr:ГR):Prop := spy (Rh gr).
  Definition spyhA (ga:ГA):Prop := spy (Ah ga).
  (* пропозиция (spy b) в ГA и ГR *)
  Definition spybR (gr:ГR):Prop := spy (Rb gr).
  Definition spybA (ga:ГA):Prop := spy (Ab ga).

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


(** **************************************************************)
(** Модуль: в актуальном контексте только Орткутт                *)
(**      две функции преобразования контекстов                   *)

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

  (** контексты связи *)
  (*   Parameter ГC:Type. *)
  Class ГRH :=
   {RHa:>ГA;
    RHr:>ГR;
    RHeqh:o=Rh}.
  Class ГRB :=
   {RBa:>ГA;
    RBr:>ГR;
    RBeqb:o=Rb}.

(*   Parameter гr:ГR. *)

  (** докажем spy(h) для всех ГR  --- de dicto *)

  Fact spyh: forall gr:ГR, spy (Rh).
  Proof.
    intros.
    apply spy_h.
  Qed.

  (** докажем ~spy(b) для всех ГR  --- de dicto *)

  Fact spyb: forall gr:ГR, ~spy (Rb).
  Proof.
    intros.
    apply spy_b.
  Qed.

  (** ********************************************************************)
  (** Мнения для (spy o)  *)
  (** ********************************************************************)

  (** spy o истинно в контексте ГRH *)
  Fact spyo_rh: forall grh:ГRH, spy (o).
  Proof.
    intros.
    rewrite RHeqh.
    apply spy_h.
  Qed.

  Parameter гrh:ГRH.
  Parameter гrb:ГRB.
  
  (** неверно, что ~(spy o), в контексте ГRH *)
  Fact spyo_rhn: ~forall grh:ГRH, ~spy (o).
  Proof.
    unfold not.
    intros H.
    apply (H гrh).
    apply spyo_rh.
  Qed.

  (** spy o ложно в контексте ГRB *)
  Fact spyo_rb: forall grb:ГRB, ~spy (o).
  Proof.
    intros.
    rewrite RBeqb.
    apply spy_b.
  Qed.

  (** неверно, что (spy o), в контексте ГRB *)
  Fact spyo_rbn: ~forall grb:ГRB, spy (o).
  Proof.
    unfold not.
    intros.
    set (H1:=H гrb).
    rewrite RBeqb in H1.
    apply spy_b in H1.
    assumption.
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
    apply (H1 (@RHr гrh) (H2 RHr)).
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

  Definition PAtoRH (P:ГA->Prop) : ГRH->Prop :=
    fun (grh:ГRH) => P RHa.
  Definition PAtoRB (P:ГA->Prop) : ГRB->Prop :=
    fun (grb:ГRB) => P RBa.

  (* пропозиция (spy o) в ГA *)
  Definition spyo:ГA->Prop := fun (ga:ГA) => spy (@o ga).

  (** (ГR -> (spy o)) истинно *)
  Fact spyo_h_inR: forall (grh:ГRH), (PAtoRH spyo) grh.
  Proof.
    unfold PAtoRH.
    intros.
    unfold spyo.
    rewrite RHeqh.
    apply spy_h.
  Qed.

  (** (ГR -> (spy o)) ложно *)
  Fact spyo_b_inR : ~ forall (grb:ГRB), (PAtoRB spyo) grb.
  Proof.
    unfold not.
    unfold PAtoRB.
    intros H.
    set (H1:=H гrb).
    unfold spyo in H1.
    rewrite RBeqb in H1.
    apply spy_b in H1.
    assumption.
  Qed.

  (** существует ГA->man, ГR ... *)

  (* при некотором ГR мы верим, что существует человек, о котором Ральф верит, 
     что он шпион *)
  Fact ex_man: forall ga:ГA, exists m:ГA->man, forall grh:ГRH, spy (m (RHa)).
  Proof.
    intros.
    exists @o.
    apply spyo_rh.
  Qed.

  (* то же с PAtoR *)
  Fact ex_man': forall ga:ГA, exists m:ГA->man, forall grh:ГRH, (PAtoRH spyo) grh.
  Proof.
    intros.
    exists @o.
    apply spyo_rh.
  Qed.

  (* при некотором ГR мы верим, что существует человек, о котором Ральф верит, 
     что он НЕ шпион *)
  Fact ex_mann: forall ga:ГA, exists m:ГA->man, forall grb:ГRB, ~spy (m (RBa)).
  Proof.
    intros.
    exists @o.
    apply spyo_rb.
  Qed.

  (* то же с PAtoR *)
  Definition spyA (m:ГA->man):ГA->Prop := fun (ga:ГA) => spy (m ga).

  Fact ex_mann': forall ga:ГA, 
    exists m:ГA->man, forall grb:ГRB, ~(PAtoRB (spyA m)) grb.
  Proof.
    apply ex_mann.
  Qed.

  Fact ex_mann'': forall ga:ГA, 
    exists m:ГA->man, ~forall grb:ГRB, (PAtoRB (spyA m)) grb.
  Proof.
    intros.
    exists @o.
    apply spyo_rbn.
  Qed.

End Ralph_o.