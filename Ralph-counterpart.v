(** Фраза Куайна "Ральф верит, что кто-то шпион" *)
(** С использованием counterpart relation        *)


(** Сигнатура  **)
Parameter man:Set.
Parameter spy: man->Prop.



Module Ralph_counterpart.

  (** Контекст Ральфа **)
  Record ГR:Type := mkГR
    {xh:man;           (* человек в шляпе *)
     xb:man;           (* человек на пляже *)
     spy_h: spy(xh);   (* человек в шляпе --- шпион *)
     spy_b: ~spy(xb)}. (* человек на пляже --- не шпион *)

  (** Актуальный контекст *)
  Record ГA:Type := mkГA
    {o:man}.

  (** counterpart relation  *)

  Definition Cpart:= (ГA->man) -> (ГR->man) -> Prop.
  Inductive C : Cpart :=
    | coh : C o xh
    | cob : C o xb.

  (* типы двойников *)
  Definition cinA (x:ГR->man): Type := { m:ГA->man | C m x }.
  Definition cinR (x:ГA->man): Type := { m:ГR->man | C x m }.

  (* Тип cinR(o) непуст. Доказываем это построением термов *)
  Lemma mmh:cinR(o).
  Proof.
    unfold cinR.
    exists xh.
    apply coh.
  Defined.

  Lemma mmb:cinR(o).
  Proof.
    unfold cinR.
    exists xb.
    apply cob.
  Defined.

  (* среди двойников есть шпион *)
  Fact ex: exists m:cinR(o), forall gr:ГR, spy ((proj1_sig m) gr).
  Proof.
    intros.
    unfold cinR.
    exists mmh.
    unfold proj1_sig.
    apply spy_h.
  Qed.

  (* и есть НЕ шпион *)
  Fact exn: exists m:cinR(o), forall gr:ГR, ~spy ((proj1_sig m) gr).
  Proof.
    intros.
    unfold cinR.
    exists mmb.
    unfold proj1_sig.
    apply spy_b.
  Qed.


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

  (* существует чел. в нашем контексте, такой, что существует его двойник,
     о котором Ральф верит, что он --- шпион  *)
  Fact exh: exists ma:ГA->man, exists mc:cinR(ma), 
    forall gr:ГR, spy ((proj1_sig mc) gr).
  Proof.
    exists o.
    exists mmh.
    apply spy_h.
  Qed.

  (* существует чел. в нашем контексте, такой, что существует его двойник,
     о котором Ральф верит, что он --- НЕ шпион  *)
  Fact exb: exists ma:ГA->man, exists mc:cinR(ma), 
    forall gr:ГR, ~spy ((proj1_sig mc) gr).
  Proof.
    exists o.
    exists mmb.
    apply spy_b.
  Qed.

  (* Мы верим, что Ральф верит, что Орткут шпион  *)
  Fact oh: forall ga:ГA, exists mc:cinR(o), 
    forall gr:ГR, spy ((proj1_sig mc) gr).
  Proof.
    exists mmh.
    apply spy_h.
  Qed.

  (* Мы верим, что Ральф НЕ верит, что Орткут шпион  *)
  Fact ob: forall ga:ГA, exists mc:cinR(o), 
    forall gr:ГR, ~spy ((proj1_sig mc) gr).
  Proof.
    exists mmb.
    apply spy_b.
  Qed.

End Ralph_counterpart.
