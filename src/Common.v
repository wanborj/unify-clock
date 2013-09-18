(*
The MIT License (MIT)

Copyright (c) 2013 Yucheng Zhang

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*)


Require Import List Omega BinPos Pnat.
Require Import FMapPositive FMapFacts Structures.OrderedTypeEx.
Require Import Ltac_ext.

(** Common utilities *)

Lemma nth_error_ok : (* TODO: remove this *)
  forall A i (l:list A),
    i < length l ->
    nth_error l i <> None.
  Proof.
    intros.
    revert dependent i.
    induction l.

    intros. absurd (i < 0). omega. assumption.
    intros. destruct i.
      discriminate.
      simpl in H. 
      assert (i < length l). omega.
      apply IHl in H0.
      simpl. assumption.
  Qed.

Lemma list_nth_some :
  forall A (l:list A) i,
    i < length l ->
    exists x, nth_error l i = Some x.
Proof.
  intros A l.
  induction l; intros; simpl in *.
  + omega.
  + destruct i.
    - exists a. auto.
    - assert (i < length l) by omega.
      simpl.
      eauto.
Qed.

Lemma list_nth_none:
  forall A (l:list A) i,
    length l <= i ->
    nth_error l i = None.
Proof.
  intros A l.
  induction l; intros; simpl in *.
  + destruct i; reflexivity.
  + destruct i.
    - omega.
    - assert (length l <= i) by omega.
      simpl. auto.
Qed.

Lemma option_exist : (* TODO: remove this *)
  forall A (o:option A),
    o <> None ->
    exists a, o = Some a.
  Proof.
    intros.
    destruct o.
    exists a. reflexivity.
    contradict H. reflexivity.
  Qed.

Lemma list_nth_eq :
  forall A (la:list A) lb,
    ( forall i, nth_error la i = nth_error lb i) ->
    la = lb.
Proof.
  intros A la.
  induction la; intros.
  + specialize (H 0).
    destruct lb; try discriminate.
    reflexivity.
  + assert (H' := H 0).
    destruct lb as [ | b lb ]; try discriminate.
    simpl in H'. injection H'; clear H'. intro; subst.
    f_equal.
    apply IHla.
    intro i. specialize (H (S i)). simpl in H.
    assumption.
Qed.

Lemma list_nth_some' :
  forall A (l:list A) i x,
    List.nth_error l i = Some x ->
    i < length l.
Proof.
  intros A l.
  induction l; intros; simpl in *.
  + destruct i; discriminate.
  + destruct i.
    - omega.
    - cut (i < length l).
        omega.

      eapply IHl; eauto.
Qed.

Lemma list_exist :
  forall A n (P:nat -> A -> Prop),
    ( forall i, i < n -> exists x, P i x ) ->
    exists l,
      length l = n /\
      (forall i x, nth_error l i = Some x -> P i x).
Proof.
  intros A n P HP.

  cut ( forall ma mb,
          ma + mb = n ->
          exists l,
            length l = mb /\
            (forall i x, nth_error l i = Some x -> P (ma + i) x) ).
    intro H. specialize (H 0 n).
    apply H. omega.

  intros ma mb. revert ma.
  induction mb; intros.
  + exists nil. split.
    - trivial.
    - intros.
      assert (nth_error (@nil A) i = None).
        apply list_nth_none. simpl. omega.
      congruence.
  + specialize (IHmb (S ma)).
    destruct IHmb as [ l [ Hl1 Hl2 ] ]; [ omega | ].
    specialize (HP ma).
    destruct HP as [x Hx ]; [ omega | ].

    exists (x :: l); split.
    - simpl. omega.
    - intros.
      destruct i.
      * injection H0; clear H0; intro; subst x0.
        cutrewrite (ma + 0 = 0 + ma); [ | omega ].
        assumption.
      * cutrewrite (ma + S i = S ma + i); [ | omega ].
        apply Hl2.
        simpl in H0.
        assumption.
Qed.

Module M := PositiveMap.
Module MF := WFacts_fun PositiveOrderedTypeBits PositiveMap.
Module MP := WProperties_fun PositiveOrderedTypeBits PositiveMap.

Hint Unfold M.In.

Ltac simpl' :=
  repeat match goal with
    | [ H:?A /\ ?B |- _ ] => destruct H
    | [ H:True |- _ ] => clear H
    | [ H:?A, H':?A |- _ ] => clear H'
    | [ H:?A->?B, H':?A |- _ ] => specialize (H H')
    | [ H:?A->?B |- _ ] =>
      let HHH:=fresh "HHH" in
        try (assert (HHH: A); [ solve [ eauto ] | specialize (H HHH) ])
    | [ H:Some ?x = Some ?y |- _ ] =>
        injection H; intro; clear H
    | [ H:?x = ?x |- _ ] => clear H
  end.

Ltac map_trivial' :=
  match goal with
    (* empty map *)
    | [ H: M.In _ (M.empty _) |- _ ] =>
      apply MF.empty_in_iff in H; destruct H
    | [ H: M.MapsTo _ _ (M.empty _) |- _ ] =>
      apply MF.empty_mapsto_iff in H; destruct H

    (* duplicated claim of the same key *)
    | [ H1: M.MapsTo ?x ?va ?m, H2: M.MapsTo ?x ?vb ?m |- _ ] =>
      let HH := fresh "HHH" in
      assert (HH: va=vb) by (eapply MF.MapsTo_fun; eauto);
      clear H2;
      try (subst va || subst vb);
      try discriminate

    (* [M.add] in goal *)
    | [ |- M.MapsTo ?x ?y (M.add ?x' ?z ?m) ] =>
      let HH1 := fresh "HHH" in
      let HH2 := fresh "HHH" in
      assert (HH1: x' = x) by congruence;
      cut (y = z);
      [ intro HH2; try rewrite HH2; apply M.add_1; assumption
      | clear HH1; try congruence ]

    | [ |- M.MapsTo ?x ?y (M.add ?x' ?z ?m) ] =>
      let HH := fresh "HHH" in
      assert (HH: x' <> x) by congruence;
      apply <- MF.add_neq_mapsto_iff; [ clear HH | assumption ]

    | [ |- M.In ?x (M.add ?x' ?z ?m) ] =>
      let HH := fresh "HHH" in
      assert (HH: x' = x) by congruence;
      apply <- MF.add_in_iff; left; assumption

    | [ |- M.In ?x (M.add ?x' ?z ?m) ] =>
      let HH := fresh "HHH" in
      assert (HH: x' <> x) by congruence;
      apply <- MF.add_in_iff; right;
      clear HH

    (* [M.add] in hypothesis *)
    | [ H: M.MapsTo ?x ?y (M.add ?x' ?z ?m) |- _ ] =>
      let HH := fresh "HHH" in
      assert (HH: x' = x) by congruence;
      assert (M.MapsTo x z (M.add x' z m)) by (apply M.add_1; assumption);
      clear HH;
      map_trivial';
      clear H

    | [ H: M.MapsTo ?x ?y (M.add ?x' ?z ?m) |- _ ] =>
      let HH := fresh "HHH" in
      assert (HH: x' <> x) by congruence;
      assert (M.MapsTo x y m) by
        (rewrite MF.add_neq_mapsto_iff in H; assumption);
      clear HH H

    | [ H: M.MapsTo ?x ?y (M.add ?x' ?z ?m) |- _ ] =>
      let HH := fresh "HHH" in
      apply -> MF.add_mapsto_iff in H;
      destruct H as [ [ HH H ] | [ HH H ] ];
      [ try (subst x || subst x');
        try (subst y || subst z );
        try discriminate
      | try discriminate ]

    | [ H: M.In ?x (M.add ?x' ?z ?m) |- _ ] =>
      let HH := fresh "HHH" in
      assert (HH: x' = x) by congruence;
      clear HH H

    | [ H: M.In ?x (M.add ?x' ?z ?m) |- _ ] =>
      let HH := fresh "HHH" in
      assert (HH: x' <> x) by congruence;
      assert (M.In x m) by (rewrite MF.add_neq_in_iff in H; assumption);
      clear HH H

    | [ H: M.In ?x (M.add ?x' ?z ?m) |- _ ] =>
      apply -> MF.add_in_iff in H;
      destruct H as [ H | H ];
      [ try (subst x || subst x');
        try discriminate
      | ]

    (* [M.find] *)
    | [ |- M.MapsTo ?x ?y ?m ] =>
      assert (M.find x m = Some y) by
        ( congruence || assumption || symmetry; assumption );
      apply <- MF.find_mapsto_iff; assumption

    | [ |- ~ M.In ?x ?m ] =>
      assert (M.find x m = None) by
        ( congruence || assumption || symmetry; assumption );
      apply <- MF.not_find_in_iff; assumption
  end.

Ltac map_trivial :=
  try map_trivial';
  trivial.

Lemma map_Equal_0 :
  forall T (m1 m2: M.t T),
    ( forall x, M.In x m1 <-> M.In x m2 ) ->
    ( forall x t1 t2,
        M.MapsTo x t1 m1 ->
        M.MapsTo x t2 m2 ->
        t1 = t2 ) ->
    M.Equal m1 m2.
Proof.
  intros.
  apply MF.Equal_mapsto_iff.
  intros x t; split.
  + intros.
    assert (HH1 : M.In x m1) by eauto.
    assert (HH2 : M.In x m2) by firstorder.
    destruct HH2 as [ t2 HH2 ].
    cut ( t = t2 ); [ congruence | ].
    eapply H0; eauto.
  + intros.
    assert (HH1 : M.In x m2) by eauto.
    assert (HH2 : M.In x m1) by firstorder.
    destruct HH2 as [ t1 HH2 ].
    cut ( t1 = t ); [ congruence | ].
    eapply H0; eauto.
Qed.

Lemma map_exist :
  forall A B (mm: M.t B) (P: M.key -> A -> Prop) (Q: B -> Prop),
  ( forall b, { Q b } + { ~ Q b } ) ->
  ( forall x b, M.MapsTo x b mm -> Q b -> exists a, P x a ) ->
  exists m,
    ( forall x,
        (exists b, M.MapsTo x b mm /\ Q b) <->
        M.In x m ) /\
    ( forall x a,
        M.MapsTo x a m ->
        P x a ).
Proof.
  intros. revert mm H. intro.
  change M.t with PositiveMap.t in mm.
  induction mm using MP.map_induction_bis; intros.

  - rewrite MF.Equal_mapsto_iff in H.
    destruct IHmm1.
      intros. eapply H0; eauto.
      apply H. assumption.

    simpl'.
    exists x; split.
    + intros. rewrite <- H1. split.
      * { intros [ b [ Hb1 Hb2 ]].
          exists b. split.
          * eapply H; eauto.
          * assumption. }
      * { intros [ b [ Hb1 Hb2 ]].
          exists b. split.
          * eapply H; eauto.
          * assumption. }
    + assumption.

  - exists (M.empty A); split; intros; simpl'.
    + split; intros; simpl'.
      * destruct H0 as [ b [ Hb1 Hb2 ] ].
        map_trivial.
      * map_trivial.
    + map_trivial.

  - rename e into b.

    destruct IHmm as [m [ Hm1 Hm2 ] ].
      intros.
      apply H0 with (b0:=b0); [ | assumption ].
      assert (x <> x0).
        intro; subst x0.
        assert (M.In x mm) by eauto.
        contradiction.
      map_trivial.

    destruct (X b).
    + assert (H1 := H0).
      specialize (H1 x b).
      destruct H1 as [ a Ha ]; [ map_trivial | assumption | ].

      exists (M.add x a m); split; intros.
      * { split; intros; simpl'.
          - destruct H1 as [ b0 [ Hb1 Hb2 ]].
            map_trivial.
            * map_trivial.
            * map_trivial.
              apply -> Hm1; eauto.
          - map_trivial.
            * exists b. split; [ map_trivial | auto ].
            * assert (H2 := H1).
              apply Hm1 in H2. destruct H2 as [ b0 [ Hb1 Hb2 ]].
              exists b0. split.
              + assert (x0 <> x).
                  intro; subst x0.
                  assert (M.In x mm) by eauto.
                  contradiction.
                map_trivial.
              + assumption. }
      * map_trivial.
        apply Hm2.
        assumption.

    + exists m. split; intros; simpl'.
      * { split; intros.
          + destruct H1 as [ b0 [ Hb1 Hb2 ]].
            map_trivial.
            * contradiction.
            * apply Hm1. eauto.
          + apply Hm1 in H1.
            destruct H1 as [ b0 [ Hb1 Hb2 ]].
            exists b0. split.
            * assert (x <> x0).
                intro; subst x0.
                assert (M.In x mm) by eauto.
                contradiction.
              map_trivial.
            * assumption. }
      * apply Hm2; auto.
Qed.

Ltac destruct_ex :=
  repeat match goal with
    | [ H: @ex _ _ |- _ ] => destruct H
  end.

Ltac rewrite_tuple :=
  repeat match goal with
    | [ H: (?x, ?y) = (?x', ?y') |- _ ] =>
        assert (x = x'); [ congruence | idtac ];
        assert (y = y'); [ congruence | idtac ];
        clear H;
        subst; simpl in *
  end.

Module PN := Pos2Nat.

Ltac pomega' :=
  repeat match goal with
    | [ |- ~ _ ] =>
      intro

    | [ H : Pos.lt ?a ?b |- _ ] =>
      assert ((Pos.to_nat a < Pos.to_nat b) % nat);
        [ apply PN.inj_lt; assumption | clear H ]

    | [ H : Pos.le ?a ?b |- _ ] =>
      assert ((Pos.to_nat a <= Pos.to_nat b) % nat);
        [ apply PN.inj_le; assumption | clear H ]

    | [ |- Pos.lt ?a ?b ] =>
      cut ((Pos.to_nat a < Pos.to_nat b) % nat);
        [ intro; apply <- PN.inj_lt; assumption | ]

    | [ |- Pos.le ?a ?b ] =>
      cut ((Pos.to_nat a <= Pos.to_nat b) % nat);
        [ intro; apply <- PN.inj_le; assumption | ]

    | [ H : @eq positive ?a ?b |- _ ] =>
      assert (Pos.to_nat a = Pos.to_nat b);
        [ f_equal; assumption | clear H ]

    | [ H : ~ @eq positive ?a ?b |- _ ] =>
      assert (Pos.to_nat a <> Pos.to_nat b);
        [ contradict H; apply PN.inj; assumption | clear H ]

    | [ |- @eq positive ?a ?b ] =>
      cut (Pos.to_nat a = Pos.to_nat b); [ apply PN.inj | ]

    | [ |- ~ @eq positive ?a ?b ] =>
      cut (Pos.to_nat a <> Pos.to_nat b);
        [ let HH := fresh "HH" in
          intro HH; contradict HH; f_equal; assumption | ]
  end;

  ( iter_tac ( fun x => match type of x with
    | positive => let HHH := fresh "HHH" in
                  assert (HHH := PN.is_pos x)
    | _ => idtac
  end ) );

  repeat progress first [ rewrite PN.inj_add in *
                        | rewrite PN.inj_mul in * ];

  unfold Pos.to_nat in *;
  simpl in *.

Ltac pomega := pomega'; omega.
