(** Фраза Куайна "Ральф верит, что кто-то шпион" *)

(** Сигнатура  **)
Parameter man:Set.
Parameter spy: man->Prop.



(** Модуль: в актуальном контексте человек в шляпе и на пляже *)

Module Ralph_hb.

  (** Контекст Ральфа **)
  Record ГR:Type := mkГR
    {xh:man;           (* человек в шляпе *)
     xb:man;           (* человек на пляже *)
     spy_h: spy(xh);   (* человек в шляпе --- шпион *)
     spy_b: ~spy(xb)}. (* человек на пляже --- не шпион *)

  (** Актуальный контекст *)
  Record ГA:Type := mkГA
    {yh:man;       (* человек в шляпе *)
     yb:man}.      (* человек на пляже *)

  (** Докажем spy(xh) для всех ГR --- de dicto *)

  Fact gr_h_spy: forall gr:ГR, spy (xh gr).
  Proof.
    apply spy_h.
  Qed.


  (** функция связи контекстов  ГR -> ГA *)

  Definition fhb (gr:ГR) : ГA := mkГA (xh(gr)) (xb(gr)).

  (** ********************************************************************)
  (** Мнения для (spy yh)  *)
  (** ********************************************************************)

  (** (ГR -> (spy yh)) истинно для функции fhb *)
  Fact spyyh_fhb: forall gr:ГR, spy (yh (fhb gr)).
  Proof.
    apply spy_h.
  Qed.

  (** (ГR -> ~(spy yh)) ложно для функции fhb *)
  Fact spyyh_fhbn (gr0:ГR): ~forall gr:ГR, ~spy (yh (fhb gr)).
  Proof.
    unfold not.
    intros.
    apply (H gr0). apply spyyh_fhb.
  Qed.

  (** ********************************************************************)
  (** Мнения для (spy yb)  *)
  (** ********************************************************************)

  (** (ГR -> ~(spy yb)) истинно для функции fhb *)
  Fact spyyb_fhb : forall gr:ГR, ~spy (yb (fhb gr)).
  Proof.
    unfold not.
    intros.
    apply (spy_b gr).
    assumption.
  Qed.

  (** (ГR -> (spy yb)) ложно для функции fhb *)
  Fact spyyb_fhbn (gr0:ГR): ~forall gr:ГR, spy (yb (fhb gr)).
  Proof.
    unfold not.
    intros.
    apply (spy_b gr0).
    apply H.
  Qed.

  (** ********************************************************************)
  (** существует ф-я f ... *)
  (** ********************************************************************)

  (* существует f, такая, что Ральф верит, что (spy yh) *)
  Fact ex_f : exists (f:ГR->ГA), forall gr:ГR, spy (yh (f gr)).
  Proof.
    exists fhb.
    apply spyyh_fhb.
  Qed.

  (* существует f, такая, что Ральф верит, что ~(spy yb) *)
  Fact ex_fn : exists (f:ГR->ГA), forall gr:ГR, ~spy (yb (f gr)).
  Proof.
    unfold not.
    exists fhb.
    apply spyyb_fhb.
  Qed.

  (* существует f, такая, что неверно, что Ральф верит, что (spy yb) *)
  Fact ex_fn' (gr0:ГR): exists (f:ГR->ГA), ~forall gr:ГR, spy (yb (f gr)).
  Proof.
    exists fhb.
    apply (spyyb_fhbn gr0).
  Qed.

  (** *******************************************)
  (** Для пропозиции man->Prop в общем случае   *)
  (** *******************************************)

  (* (B)~P -> ~(B)P *)
  Lemma Rn_nR (gr0:ГR) (P:man->Prop) (m:ГR->man): 
    (forall gr:ГR, ~P(m gr)) -> ~(forall gr:ГR, P(m gr)).
  Proof.
    unfold not.
    intros H1 H2.
    apply (H1 gr0 (H2 gr0)).
  Qed.

  (* то же в контексте ГA *)
  Lemma Rn_nR_ga (gr0:ГR) (P:man->Prop) (m:ГA->man) (f:ГR->ГA): 
    (forall gr:ГR, ~P(m (f gr))) -> ~(forall gr:ГR, P(m (f gr))).
  Proof.
    set (mR:=fun gr:ГR => m(f(gr))).
    apply (Rn_nR gr0 P mR).
  Qed.

  (** применим общий случай к (spy yb) *)
  Lemma spyb_f (gr0:ГR) (f:ГR->ГA): 
    (forall gr:ГR, ~spy(yb (f gr))) -> ~(forall gr:ГR, spy(yb (f gr))).
  Proof.
    apply (Rn_nR_ga gr0 spy yb f).
  Qed.

  (** Итог: Ральф верит ~(spy yb) -> неверно, что Ральф верит (spy yb)    *)

  (** *******************************************)
  (** Для пропозиции ГR->Prop в общем случае   *)
  (** *******************************************)

  (* (B)~P -> ~(B)P *)
  Lemma Rn_nR' (gr0:ГR) (P:ГR->Prop): 
    (forall gr:ГR, ~P(gr)) -> ~(forall gr:ГR, P(gr)).
  Proof.
    unfold not.
    intros H1 H2.
    apply (H1 gr0 (H2 gr0)).
  Qed.

  (** ***********************************************)
  (** Мнения для (spy y) --- с использованием PAtoR *)
  (** ***********************************************)

  (* Преобразование из Prop в контексте ГA в Prop в контексте ГR *)

  Definition PAtoR (P:ГA->Prop) (f:ГR->ГA) : ГR->Prop :=
    fun (gr:ГR) => P (f gr).

  (* пропозиция (spy yh) в ГA *)
  Definition spyyh:ГA->Prop := fun (ga:ГA) => spy (yh ga).
  (* пропозиция (spy yb) в ГA *)
  Definition spyyb:ГA->Prop := fun (ga:ГA) => spy (yb ga).

  (** (ГR -> (spy yh)) истинно для функции fhb *)
  Fact spyy_fhb_inR: forall (gr:ГR), (PAtoR spyyh fhb) gr.
  Proof.
    unfold PAtoR.
    apply spy_h.
  Qed.

  (** (ГR -> (spy yb)) ложно для функции fhb) *)
  Lemma spyy_fb_inR (gr0:ГR) : ~ forall (gr:ГR), (PAtoR spyyb fhb) gr.
  Proof.
    unfold not.
    unfold PAtoR.
    unfold spyyb.
    unfold fhb.
    unfold yb.
    apply (Rn_nR_ga gr0 spy yb fhb).
    apply spyyb_fhb.
  Qed.

  (** существует ГA->man, f ... *)

  (* при некотором f мы верим, что существует человек, о котором Ральф верит, 
     что он шпион *)
  Fact ex_man: exists f:ГR->ГA, 
    forall ga:ГA, exists m:ГA->man, forall gr:ГR, spy (m (f gr)).
  Proof.
    exists fhb.
    exists yh.
    apply spy_h.
  Qed.

  (* то же с PAtoR *)
  Fact ex_man': exists f:ГR->ГA, 
    forall ga:ГA, exists m:ГA->man, forall gr:ГR, (PAtoR spyyh f) gr.
  Proof.
    exists fhb.
    exists yh.
    apply spy_h.
  Qed.

  (* при некотором f мы верим, что существует человек, о котором Ральф верит, 
     что он НЕ шпион *)
  Fact ex_mann: exists f:ГR->ГA, 
    forall ga:ГA, exists m:ГA->man, forall gr:ГR, ~spy (m (f gr)).
  Proof.
    exists fhb.
    exists yb.
    apply spy_b.
  Qed.

  (* то же с PAtoR *)
  Definition spyA (m:ГA->man):ГA->Prop := fun (ga:ГA) => spy (m ga).

  Fact ex_mann': exists f:ГR->ГA, 
    forall ga:ГA, exists m:ГA->man, forall gr:ГR, ~(PAtoR (spyA m) f) gr.
  Proof.
    exists fhb.
    exists yb.
    apply spy_b.
  Qed.

  (* при некотором f существует человек, о котором неверно, что Ральф верит, 
     что он шпион *)
  Fact ex_mann''' (gr0:ГR): exists f:ГR->ГA, 
    exists m:ГA->man, ~forall gr:ГR, (PAtoR (spyA m) f) gr.
  Proof.
    unfold not.
    exists fhb.
    exists yb.
    apply (Rn_nR_ga gr0 spy yb fhb).
    apply spy_b.
  Qed.

End Ralph_hb.





(** ***********************************************)
(** Модуль: человек в шляпе = человек на пляже    *)
(**     противоречивая попытка                    *)

Module Ralph_eq_contr.

  (** Контекст Ральфа **)
  Record ГR:Type := mkГR
    {xh:man;           (* человек в шляпе *)
     xb:man;           (* человек на пляже *)
     spy_h: spy(xh);   (* человек в шляпе --- шпион *)
     spy_b: ~spy(xb)}. (* человек на пляже --- не шпион *)

  (** Актуальный контекст *)
  Record ГA:Type := mkГA
    {yh:man;
     yb:man;
     yeq:yh=yb}.       (* человек в шляпе = человек на пляже *)

  (** просто приравняем переменные  *)

  Axiom Aeqh: forall ga:ГA, forall gr:ГR, xh gr = yh ga.
  Axiom Aeqb: forall ga:ГA, forall gr:ГR, xb gr = yb ga.

  (** Докажем противоречивость   *)

  Lemma spy_yh: forall ga:ГA, forall gr:ГR, spy (yh ga).
  Proof.
    intros.
    rewrite <- (Aeqh ga gr).
    apply spy_h.
  Qed.

  Lemma spy_yhn: forall gr0:ГR, 
    forall ga:ГA, ~forall gr:ГR, spy (yh ga).
  Proof.
    unfold not.
    intros.
    rewrite yeq in H.
    rewrite <- (Aeqb ga gr0) in H.
    apply (spy_b gr0).
    auto.
  Qed.

  (** ПРОТИВОРЕЧИЕ В ГA !! *)

  (* если существует любой контекст ГR, то контекст ГA противоречив *)
  Theorem contr: forall gr0:ГR, forall ga:ГA, False.
  Proof.
    intros.
    apply (spy_yhn gr0 ga).
    apply spy_yh.
  Qed.

End Ralph_eq_contr.




(** ***********************************************)
(** Модуль: человек в шляпе = человек на пляже  *)

Module Ralph_eq.

  (** Контекст Ральфа **)
  Record ГR:Type := mkГR
    {xh:man;           (* человек в шляпе *)
     xb:man;           (* человек на пляже *)
     spy_h: spy(xh);   (* человек в шляпе --- шпион *)
     spy_b: ~spy(xb)}. (* человек на пляже --- не шпион *)

  (** Актуальный контекст *)
  Record ГA:Type := mkГA
    {yh:man;
     yb:man;
     yeq:yh=yb}.       (* человек в шляпе = человек на пляже *)

  (** Общий контекст *)
  Record ГRA:Type := mkГRA
    {zh:man;
     zb:man}.

  (** функции связи контекстов *)

  Definition f (gr:ГR) : ГRA := mkГRA (xh(gr)) (xb(gr)).
  Definition g (ga:ГA) : ГRA := mkГRA (yh(ga)) (yb(ga)).

  (** ********************************************************************)
  (**     de dicto      *)
  (** ********************************************************************)

  Fact spyh: forall gr:ГR, spy (xh gr).
  Proof.
    apply spy_h.
  Qed.

  Fact spyb: forall gr:ГR, ~spy (xb gr).
  Proof.
    apply spy_b.
  Qed.

  (* Ральф верит, что существует кто-то... *)
  Fact spyh_ex: forall gr:ГR, exists m:ГR->man, spy (m gr).
  Proof.
    exists xh.
    apply spy_h.
  Qed.

  Fact spyb_ex: forall gr:ГR, exists m:ГR->man, ~spy (m gr).
  Proof.
    exists xb.
    apply spy_b.
  Qed.

  (** ********************************************************************)
  (**     de re         *)
  (** ********************************************************************)

  (** Вспомомогательные определения. *)

  (* Перевод терма типа T из ГRA в ГR и ГA  *)
  Definition tRAtoR {T:Type} (t:ГRA->T): ГR->T := fun gr:ГR => t (f gr).
  Definition tRAtoA {T:Type} (t:ГRA->T): ГA->T := fun ga:ГA => t (g ga).
  (* перевод man из ГRA в ГR и ГA *)
  Definition mR (m:ГRA->man) : ГR->man := tRAtoR m.
  Definition mA (m:ГRA->man) : ГA->man := tRAtoA m.
  (* перевод пропозиции P из ГRA в ГR и ГA *)
  Definition PRAtoR (P:ГRA->Prop) : ГR->Prop := tRAtoR P.
  Definition PRAtoA (P:ГRA->Prop) : ГA->Prop := tRAtoA P.

  (* существует чел. в общем контексте, о ктр. Ральф верит, что он шпион *)
  Fact ex_spy: 
    {m:ГRA->man| forall gr:ГR, (PRAtoR (fun gra:ГRA => spy (m gra))) gr}.
  Proof.
    intros.
    exists zh.
    intros.
    unfold PRAtoR.
    apply spy_h.
  Defined.    (* should be Defined to use reflexivity below!! *)

  (* существует чел. в общем контексте, о ктр. Ральф верит, что он шпион,
     и он существует в нашем контексте *)
  Fact ex_spy_ex: 
    exists w:{m:ГRA->man| forall gr:ГR, (PRAtoR (fun gra:ГRA => spy (m gra))) gr},
    forall ga:ГA, exists ma:ГA->man, 
      ma ga = (fun ga:ГA => (proj1_sig w) (g ga)) ga.
  Proof.
    exists ex_spy.
    intros.
    exists yh.
    reflexivity.
  Qed.

  (* существует чел. в общем контексте, о ктр. Ральф верит, что он шпион,
     а мы знаем, что он --- чел. на пляже *)
  Fact ex_spy_eq: 
    exists w:{m:ГRA->man| forall gr:ГR, (PRAtoR (fun gra:ГRA => spy (m gra))) gr},
    forall ga:ГA, yb ga = (fun ga:ГA => (proj1_sig w) (g ga)) ga.
  Proof.
    intros.
    exists ex_spy.
    intros.
    assert (H:proj1_sig (ex_spy) =zh).
    { reflexivity. }
    rewrite H.
    rewrite <- yeq.
    auto.
  Qed.

  (** то же, что выше, но с использованием вспомогательных определений *)

  (* существует чел. в общем контексте, о ктр. Ральф верит, что он шпион *)
  Fact ex_spy': {m:ГRA->man| forall gr:ГR, spy ((mR m) gr)}.
  Proof.
    intros.
    exists zh.
    intros.
    unfold mR.
    apply spy_h.
  Qed.

  (* существует чел. в общем контексте, о ктр. Ральф верит, что он шпион,
     и он существует в нашем контексте *)
  Fact ex_spy_ex': exists w:{m:ГRA->man| forall gr:ГR, spy ((mR m) gr)},
    forall ga:ГA, exists ma:ГA->man, ma ga = (mA (proj1_sig w)) ga.
  Proof.
    exists ex_spy.
    intros.
    exists yh.
    reflexivity.
  Qed.

  (* существует чел. в общем контексте, о ктр. Ральф верит, что он шпион,
     а мы знаем, что он --- чел. на пляже *)
  Fact ex_spy_eq': exists w:{m:ГRA->man| forall gr:ГR, spy ((mR m) gr)},
    forall ga:ГA, yb ga = (mA (proj1_sig w)) ga.
  Proof.
    apply ex_spy_eq.
  Qed.

  (** Мнения для (spy z)  *)

  (** (ГR -> (spy zh)) истинно для функции f *)
  Fact spyzh_f: forall gr:ГR, spy (mR(zh) gr).
  Proof.
    apply spy_h.
  Qed.

  (** (ГR -> ~(spy zh)) ложно для функции f *)
  Fact spyzh_fn (gr0:ГR): ~forall gr:ГR, ~spy (mR(zh) gr).
  Proof.
    unfold not.
    intros H.
    apply (H gr0). apply spyzh_f.
  Qed.

  (** (ГR -> ~(spy zb)) истинно для функции f *)
  Fact spyzb_f : forall gr:ГR, ~spy (mR(zb) gr).
  Proof.
    unfold not.
    apply spy_b.
  Qed.

  (** (ГR -> (spy zb)) ложно для функции f *)
  Fact spyzb_fn (gr0:ГR): ~forall gr:ГR, spy (mR(zb) gr).
  Proof.
    unfold not.
    intros H.
    apply (spy_b gr0).
    apply H.
  Qed.

  Fact eqzhb: forall ga:ГA, mA(zh) ga = mA(zb) ga.
  Proof.
    intros.
    unfold zb. unfold zh. unfold g.
    apply yeq.
  Qed.

  (** существует ф-я f ... *)

  (* существует f, BR(spy zh) *)
  Fact ex_f : exists (f:ГR->ГRA), forall gr:ГR, spy (mR(zh) gr).
  Proof.
    exists f.
    apply spyzh_f.
  Qed.

  (** *******************************************)
  (** Для пропозиции ГR->Prop в общем случае    *)
  (** *******************************************)

  (* (B)~P -> ~(B)P *)
  Lemma Rn_nR_general (gr0:ГR) (P:ГR->Prop): 
    (forall gr:ГR, ~P(gr)) -> ~(forall gr:ГR, P(gr)).
  Proof.
    unfold not.
    intros H1 H2.
    apply (H1 gr0 (H2 gr0)).
  Qed.

  (** *******************************************)
  (** Для пропозиции man->Prop в общем случае   *)
  (** *******************************************)

  (* (B)~P -> ~(B)P *)
  Lemma Rn_nR (gr0:ГR) (P:man->Prop) (m:ГR->man): 
    (forall gr:ГR, ~P(m gr)) -> ~(forall gr:ГR, P(m gr)).
  Proof.
    unfold not.
    intros H1 H2.
    apply (H1 gr0 (H2 gr0)).
  Qed.

  (* то же в контексте ГA *)
  Lemma Rn_nR_ga (gr0:ГR) (P:man->Prop) (m:ГA->man) (fra:ГR->ГA): 
    (forall gr:ГR, ~P(m (fra gr))) -> ~(forall gr:ГR, P(m (fra gr))).
  Proof.
    set (mR:=fun gr:ГR => m(fra(gr))).
    apply (Rn_nR gr0 P mR).
  Qed.

  (* применим общий случай к (spy yh) *)
  Lemma spyyh_f (gr0:ГR) (fra:ГR->ГA): 
    (forall gr:ГR, ~spy(yh (fra gr))) -> ~(forall gr:ГR, spy(yh (fra gr))).
  Proof.
    apply (Rn_nR_ga gr0 spy yh _).
  Qed.

  (** Итог: Ральф верит ~(spy yh) -> неверно, что Ральф верит (spy yh)    *)
  (**     если существует ГR->ГA !!!                                      *)

End Ralph_eq.



(** **************************************************************)
(** Модуль: в актуальном контексте только Орткутт                *)
(**      две функции преобразования контекстов                   *)

Module Ralph_o.

  (** Контекст Ральфа **)
  Record ГR:Type := mkГR
    {xh:man;
     xb:man;
     spy_h: spy(xh);
     spy_b: ~spy(xb)}.

  (** Актуальный контекст *)
  Record ГA:Type := mkГA
    {o:man}.

  (** Две функции связи контекстов R, A *)

  Definition fh (gr:ГR) : ГA :=
    mkГA (xh(gr)).
  Definition fb (gr:ГR) : ГA :=
    mkГA (xb(gr)).

  Parameter гr:ГR.

  (** докажем spy(xh) для всех ГR  --- de dicto *)

  Fact gr_h_spy: forall gr:ГR, spy (xh gr).
  Proof.
    apply spy_h.
  Qed.

  (** ********************************************************************)
  (** Мнения для (spy o)  *)
  (** ********************************************************************)

  (** (ГR -> (spy o)) истинно для функции fh *)
  Fact spyo_fh: forall gr:ГR, spy (o (fh gr)).
  Proof.
    apply spy_h.
  Qed.

  (** (ГR -> ~(spy o)) ложно для функции fh *)
  Fact spyo_fhn : ~forall gr:ГR, ~spy (o (fh gr)).
  Proof.
    unfold not.
    intros H.
    apply (H гr). apply spyo_fh.
  Qed.

  (** (ГR -> ~(spy o)) истинно для функции fb *)
  Fact spyo_fb : forall gr:ГR, ~spy (o (fb gr)).
  Proof.
    unfold not.
    apply spy_b.
  Qed.

  (** (ГR -> (spy o)) ложно для функции fb *)
  Fact spyo_fbn: ~forall gr:ГR, spy (o (fb gr)).
  Proof.
    unfold not.
    intros H.
    apply (spy_b гr).
    apply H.
  Qed.

  (** существует ф-я f ... *)

  (* существует f, BR(spy o) *)
  Fact ex_f : exists (f:ГR->ГA), forall gr:ГR, spy (o (f gr)).
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

  (* применим общий случай к (spy o) *)
  Lemma spyo_f (f:ГR->ГA): 
    (forall gr:ГR, ~spy(o (f gr))) -> ~(forall gr:ГR, spy(o (f gr))).
  Proof.
    apply (Rn_nR_ga spy o f).
  Qed.

  (** Итог: Ральф верит ~(spy o) -> неверно, что Ральф верит (spy o)    *)



  (** **********************************************)
  (** Мнения для (spy o) --- с использованием PAtoR *)
  (** **********************************************)

  (* Transforms Prop in ГA into Prop in ГR *)

  Definition PAtoR (P:ГA->Prop) (f:ГR->ГA) : ГR->Prop :=
    fun (gr:ГR) => P (f gr).

  (* пропозиция (spy o) в ГA *)
  Definition spyo:ГA->Prop := fun (ga:ГA) => spy (o ga).

  (** (ГR -> (spy o)) истинно для функции fh *)
  Fact spyo_fh_inR: forall (gr:ГR), (PAtoR spyo fh) gr.
  Proof.
    unfold PAtoR.
    apply spy_h.
  Qed.

  (** (ГR -> (spy o)) ложно для функции fb) *)
  Fact spyo_fb_inR : ~ forall (gr:ГR), (PAtoR spyo fb) gr.
  Proof.
    unfold not.
    unfold PAtoR.
    unfold spyo.
    unfold fb.
    unfold o.
    apply (Rn_nR_ga spy o fb).
    apply spyo_fb.
  Qed.

  (** существует ГA->man, f ... *)

  (* при некотором f мы верим, что существует человек, о котором Ральф верит, 
     что он шпион *)
  Fact ex_man: exists f:ГR->ГA, 
    forall ga:ГA, exists m:ГA->man, forall gr:ГR, spy (m (f gr)).
  Proof.
    exists fh.
    exists o.
    apply spy_h.
  Qed.

  (* то же с PAtoR *)
  Fact ex_man': exists f:ГR->ГA, 
    forall ga:ГA, exists m:ГA->man, forall gr:ГR, (PAtoR spyo f) gr.
  Proof.
    exists fh.
    exists o.
    apply spy_h.
  Qed.

  (* при некотором f мы верим, что существует человек, о котором Ральф верит, 
     что он НЕ шпион *)
  Fact ex_mann: exists f:ГR->ГA, 
    forall ga:ГA, exists m:ГA->man, forall gr:ГR, ~spy (m (f gr)).
  Proof.
    exists fb.
    exists o.
    apply spy_b.
  Qed.

  (* то же с PAtoR *)
  Definition spyA (m:ГA->man):ГA->Prop := fun (ga:ГA) => spy (m ga).

  Fact ex_mann': exists f:ГR->ГA, 
    forall ga:ГA, exists m:ГA->man, forall gr:ГR, ~(PAtoR (spyA m) f) gr.
  Proof.
    exists fb.
    exists o.
    apply spy_b.
  Qed.


  Fact ex_mann'': exists f:ГR->ГA, 
    forall ga:ГA, exists m:ГA->man, ~forall gr:ГR, (PAtoR (spyA m) f) gr.
  Proof.
    exists fb.
    exists o.
    apply (Rn_nR_ga spy o fb).
    apply spy_b.
  Qed.

  Fact ex_mann''': exists f:ГR->ГA, 
    exists m:ГA->man, ~forall gr:ГR, (PAtoR (spyA m) f) gr.
  Proof.
    exists fb.
    exists o.
    apply (Rn_nR_ga spy o fb).
    apply spy_b.
  Qed.

End Ralph_o.