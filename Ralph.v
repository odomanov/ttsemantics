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

  Parameter гr:ГR.

  (** функция связи контекстов  ГR -> ГA *)

  Definition fhb (gr:ГR) : ГA :=
    mkГA (xh(gr)) (xb(gr)).

  (** ********************************************************************)
  (** Мнения для (spy yh)  *)
  (** ********************************************************************)

  (** (ГR -> (spy yh)) истинно для функции fhb *)
  Fact spyyh_fhb: forall gr:ГR, spy (yh (fhb gr)).
  Proof.
    apply spy_h.
  Qed.

  (** (ГR -> ~(spy yh)) ложно для функции fhb *)
  Fact spyyh_fhbn : ~forall gr:ГR, ~spy (yh (fhb gr)).
  Proof.
    unfold not.
    intros.
    apply (H гr). apply spyyh_fhb.
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
  Fact spyyb_fhbn: ~forall gr:ГR, spy (yb (fhb gr)).
  Proof.
    unfold not.
    intros.
    apply (spy_b гr).
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
  Fact ex_fn' : exists (f:ГR->ГA), ~forall gr:ГR, spy (yb (f gr)).
  Proof.
    exists fhb.
    apply spyyb_fhbn.
  Qed.

  (** *******************************************)
  (** Для пропозиции man->Prop в общем случае   *)
  (** *******************************************)

  (* (B)~P -> ~(B)P *)
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

  (** применим общий случай к (spy yb) *)
  Lemma spyb_f (f:ГR->ГA): 
    (forall gr:ГR, ~spy(yb (f gr))) -> ~(forall gr:ГR, spy(yb (f gr))).
  Proof.
    apply (Rn_nR_ga spy yb f).
  Qed.

  (** Итог: Ральф верит ~(spy yb) -> неверно, что Ральф верит (spy yb)    *)

  (** *******************************************)
  (** Для пропозиции ГR->Prop в общем случае   *)
  (** *******************************************)

  (* (B)~P -> ~(B)P *)
  Lemma Rn_nR' (P:ГR->Prop): 
    (forall gr:ГR, ~P(gr)) -> ~(forall gr:ГR, P(gr)).
  Proof.
    unfold not.
    intros H1 H2.
    apply (H1 гr (H2 гr)).
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
  Lemma spyy_fb_inR : ~ forall (gr:ГR), (PAtoR spyyb fhb) gr.
  Proof.
    unfold not.
    unfold PAtoR.
    unfold spyyb.
    unfold fhb.
    unfold yb.
    apply (Rn_nR_ga spy yb fhb).
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
  Fact ex_mann''': exists f:ГR->ГA, 
    exists m:ГA->man, ~forall gr:ГR, (PAtoR (spyA m) f) gr.
  Proof.
    unfold not.
    exists fhb.
    exists yb.
    apply (Rn_nR_ga spy yb fhb).
    apply spy_b.
  Qed.

End Ralph_hb.


(** ***********************************************)
(** Модуль: человек в шляпе = человек на пляже  *)

Module Ralph_eq.

  (** Контекст Ральфа **)
  Record ГR:Type := mkГR
    {xh:man;           (* человек в шляпе *)
     xb:man;           (* человек на пляже *)
     spy_h: spy(xh);   (* человек в шляпе шпион *)
     spy_b: ~spy(xb)}. (* человек на пляже не шпион *)

  (** Актуальный контекст *)
  Record ГA:Type := mkГA
    {yh:man;
     yb:man;
     yeq:yh=yb}.       (* человек в шляпе = человек на пляже *)

  (** Общий контекст *)
  Record ГRA:Type := mkГRA
    {zh:man;
     zb:man}.

  Parameter гr:ГR.

  (** функции связи контекстов R, A, RA *)

  Definition f (gr:ГR) : ГRA :=
    mkГRA (xh(gr)) (xb(gr)).
  Definition g (ga:ГA) : ГRA :=
    mkГRA (yh(ga)) (yb(ga)).

  (** ********************************************************************)
  (** Мнения для (spy h)  *)
  (** ********************************************************************)

  (** (ГR -> (spy zh)) истинно для функции f *)
  Fact spyzh_f: forall gr:ГR, spy (zh (f gr)).
  Proof.
    apply spy_h.
  Qed.

  (** (ГR -> ~(spy zh)) ложно для функции f *)
  Fact spyzh_fn : ~forall gr:ГR, ~spy (zh (f gr)).
  Proof.
    unfold not.
    intros H.
    apply (H гr). apply spyzh_f.
  Qed.

  (** (ГR -> ~(spy zb)) истинно для функции f *)
  Fact spyzb_f : forall gr:ГR, ~spy (zb (f gr)).
  Proof.
    unfold not.
    apply spy_b.
  Qed.

  (** (ГR -> (spy zb)) ложно для функции f *)
  Fact spyzb_fn: ~forall gr:ГR, spy (zb (f gr)).
  Proof.
    unfold not.
    intros H.
    apply (spy_b гr).
    apply H.
  Qed.

  (** существует ф-я f ... *)

  (* существует f, BR(spy zh) *)
  Fact ex_f : exists (f:ГR->ГRA), forall gr:ГR, spy (zh (f gr)).
  Proof.
    exists f.
    apply spyzh_f.
  Qed.

  (** *******************************************)
  (** Для пропозиции ГR->Prop в общем случае   *)
  (** *******************************************)

  (* (B)~P -> ~(B)P *)
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

  (* (B)~P -> ~(B)P *)
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

  (* применим общий случай к (spy yh) *)
  Lemma spyyh_f (f:ГR->ГA): 
    (forall gr:ГR, ~spy(yh (f gr))) -> ~(forall gr:ГR, spy(yh (f gr))).
  Proof.
    apply (Rn_nR_ga spy yh f).
  Qed.

  (** Итог: Ральф верит ~(spy o) -> неверно, что Ральф верит (spy o)    *)

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