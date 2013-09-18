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


Require Import Common SingleNode.
Require Import Program List SetoidList BinPos.

(** Decidability proof the well-formedness property *)

Program Definition check_option
    P Q
    T (x: option T) (f: forall y, Some y = x -> {P}+{Q})
    (g: None = x -> Q )
  : {P}+{Q} :=
  match x with
    | Some y => f y _
    | None => in_right
  end.

Program Definition check_dec
    P Q P' Q'
    (x: {P}+{Q}) (f: P -> {P'}+{Q'})
    (g: Q -> Q' )
  : {P'}+{Q'} :=
  if x then f _ else in_right.

Notation "'some' X <- A ; B" :=
  (check_option _ _ _ A (fun X _ => B) _)
    (at level 200, X ident, A at level 100, B at level 200).

Notation "'check' A ; B" :=
  (check_dec _ _ _ _ A (fun _ => B) _)
    (at level 200, A at level 100, B at level 200).

Notation "'check2' A ; B" :=
  (check_dec A (~A) _ _ _ (fun _ => B) _)
    (at level 200, A at level 100, B at level 200).



Lemma map_InA :
  forall T x l,
    InA (@M.eq_key_elt T) x l <->
    In x l.
Proof.
  intros.

  unfold M.eq_key_elt in *.
  unfold M.E.eq in *.

  split.

  - intros; induction H.
    + simpl'.
      assert (x = y).
        destruct x; destruct y. simpl in *; congruence.
      subst. constructor. reflexivity.
    + constructor 2. assumption.

  - intros. apply In_InA; try assumption.

    repeat constructor; simpl in *; simpl'; try congruence.
Qed.

Lemma map_NoDupA :
  forall T l,
    NoDupA (@M.eq_key_elt T) l <->
    NoDup l.
Proof.
  intros.
  
  unfold M.eq_key_elt in *.
  unfold M.E.eq in *.

  split.

  - intros; induction H.
    * constructor.
    * constructor; auto.
      rewrite <- map_InA.
      assumption.

  - intros. induction H.
    * constructor.
    * constructor; auto.
      rewrite map_InA.
      assumption.
Qed.

Lemma dec_type (ta tb : type)
  : { ta = tb } + { ~ ta = tb }.
Proof.
  decide equality.
Qed.

Lemma dec_clock (ca cb : clock)
  : { ca = cb } + { ~ ca = cb }.
Proof.
  decide equality.
  apply Pos.eq_dec.
Qed.

Program Definition dec_well_type_val u t
  : { well_type_val u t } + { ~ well_type_val u t } :=

  match u with
    | Vz _ => match t with
                | Tz => in_left
                | Tbool => in_right
              end
    | Vbool _ => match t with
                   | Tz => in_right
                   | Tbool => in_left
                 end
  end.
Next Obligation.
  constructor.
Qed.
Next Obligation.
  intro.
  inversion H.
Qed.
Next Obligation.
  intro.
  inversion H.
Qed.
Next Obligation.
  constructor.
Qed.

Program Fixpoint dec_well_type
    T C e
  : { well_type T C e } + { ~ well_type T C e } :=
  match e with
    | Evar x t c =>
        some t' <- M.find x T;
        some c' <- M.find x C;
        check (dec_type t t');
        check (dec_clock c c');
        in_left

    | Econst u t c =>
        check (dec_well_type_val u t);
        check (dec_clock c None);
        in_left

    | Ewhen e x t c =>
        check (dec_well_type T C e);
        some t' <- M.find x T;
        some c' <- M.find x C;
        check (dec_type Tbool t');
        check (dec_clock (clockof e) c');
        check (dec_type (typeof e) t);
        check (dec_clock (Some x) c);
        in_left

    | Ecurr e x ui t c =>
        check (dec_well_type T C e);
        some t' <- M.find x T;
        some c' <- M.find x C;
        check (dec_type Tbool t');
        check (dec_clock c c');
        check (dec_type (typeof e) t);
        check (dec_clock (clockof e) (Some x));
        check (dec_well_type_val ui t);
        in_left

    | Efby ea eb t c =>
        check (dec_well_type T C ea);
        check (dec_well_type T C eb);
        check (dec_type (typeof ea) t);
        check (dec_type (typeof eb) t);
        check (dec_clock (clockof ea) c);
        check (dec_clock (clockof eb) c);
        in_left

    | Edata1 o ea t c =>
        match o with
          | Onot => check (dec_well_type T C ea);
                    check (dec_type (typeof ea) t);
                    check (dec_clock (clockof ea) c);
                    check (dec_type t Tbool);
                    in_left

          | Oopp => check (dec_well_type T C ea);
                    check (dec_type (typeof ea) t);
                    check (dec_clock (clockof ea) c);
                    check (dec_type t Tz);
                    in_left

          | _ => in_right
        end

    | Edata2 o ea eb t c =>
        match typeof ea with
          | Tz => match t with
                    | Tz => check (dec_well_type T C ea);
                            check (dec_well_type T C eb);
                            check (dec_type (typeof ea) t);
                            check (dec_type (typeof eb) t);
                            check (dec_clock (clockof ea) c);
                            check (dec_clock (clockof eb) c);
                            check (dec_type t Tz);
                            check2 (o = Oplus \/ o = Ominus \/
                                    o = Omul \/ o = Odiv \/ o = Omod);
                            in_left

                    | Tbool => check (dec_well_type T C ea);
                               check (dec_well_type T C eb);
                               check (dec_type (typeof ea) Tz);
                               check (dec_type (typeof eb) Tz);
                               check (dec_clock (clockof ea) c);
                               check (dec_clock (clockof eb) c);
                               check (dec_type t Tbool);
                               check2 (o = Ole \/ o = Olt \/ o = Oge \/
                                       o = Ogt \/ o = Oeq \/ o = One);
                               in_left
                  end

          | Tbool => match t with
                       | Tbool => check (dec_well_type T C ea);
                                  check (dec_well_type T C eb);
                                  check (dec_type (typeof ea) t);
                                  check (dec_type (typeof eb) t);
                                  check (dec_clock (clockof ea) c);
                                  check (dec_clock (clockof eb) c);
                                  check (dec_type t Tbool);
                                  check2 (o = Oand \/ o = Oor \/
                                          o = Oeq \/ o = One);
                                  in_left

                        | Tz => in_right
                      end
        end

    | Edata3 o ea eb ec t c =>
        check (dec_well_type T C ea);
        check (dec_well_type T C eb);
        check (dec_well_type T C ec);
        check (dec_type (typeof ea) Tbool);
        check (dec_type (typeof eb) t);
        check (dec_type (typeof ec) t);
        check (dec_clock (clockof ea) c);
        check (dec_clock (clockof eb) c);
        check (dec_clock (clockof ec) c);
        check2 (o = Oif);
        in_left
  end.

Solve Obligations using
  program_simpl;
  match goal with
    | [ H: ~ _ |- _ ] =>
        contradict H; inversion H; eauto; congruence

    | [ H: None = M.find ?x ?X |- _ ] =>
        assert (HH: ~ M.In x X) by map_trivial;
        contradict HH;
        inversion HH;
        eauto
  end.

Solve Obligations using
  intros; constructor; eauto; ( map_trivial || congruence ).

Solve Obligations using
  intros; solve
            [ eapply WDbinZZ; eauto; congruence
            | eapply WDbinZB; eauto; congruence
            | eapply WDbinBB; eauto; congruence ].

Solve Obligations using
  program_simpl; repeat split; discriminate.

Solve Obligations using
  program_simpl;
  clear;
  destruct o;
  solve [ left; auto 30
        | right; intro H;
          repeat destruct H as [H2 | H];
          discriminate ].

Obligation Tactic := idtac.
Next Obligation.
  intros.
  intro.
  inversion H; subst; congruence.
Qed.

Next Obligation.
  intros. subst; constructor; eauto.
Qed.


Lemma list_remove_0 :
  forall T a (la: list T) (lb lc: list T),
    ( forall x y: T, {x=y} + {x<>y} ) ->
    ~ In a la ->
    ~ In a lb ->
    ( forall x, In x (a::la) -> In x (lb ++ lc)) ->
    exists ld,
         S (length ld) = length (lb ++ lc)
      /\ ( forall x, In x la -> In x ld ).
Proof.
  intros.

  revert dependent lb.

  induction lc.
  + intros.
    assert (In a lb).
      rewrite <- app_nil_r.
      apply H1.
      simpl; auto.
    contradiction.

  + intros.
    destruct (X a a0).
    - subst a0.
      exists (lb++lc). split.
      * repeat rewrite app_length.
        simpl; auto.
      * intros.
        assert (In x (lb ++ a :: lc)).
          apply H1.
          simpl; auto.
        apply in_app_or in H3. simpl in H3.
        repeat destruct H3 as [ HH1 | H3 ]; auto with datatypes.
        subst. contradiction.

    - destruct IHlc with (lb := a0 :: lb).
      * contradict H0.
        destruct H0; auto; congruence.
      * intros.
        apply H1 in H2.
        apply in_or_app. simpl.
        apply in_app_or in H2; simpl in H2.
        tauto.
      * simpl'. exists x.
        { split.
          + rewrite app_length.
            rewrite app_length in H2.
            simpl in *. omega.
          + auto. }
Qed.

Lemma list_nodup_length :
  forall T (la lb: list T),
    ( forall x y:T, {x=y} + {x<>y} ) ->
    NoDup la ->
    ( forall x, In x la -> In x lb ) ->
    length la <= length lb.
Proof.
  induction la.
  + intros.
    simpl; omega.
  + intros.
    assert (HH: exists ld,
              S (length ld) = length ([] ++ lb) /\
              (forall x, In x la -> In x ld) ).
      apply list_remove_0 with (a:=a); auto.
      inversion H; auto.

    destruct HH as [ ld [ HH1 HH2 ] ].
    rewrite app_nil_l in HH1.

    assert (length la <= length ld).
      apply IHla; auto.
      inversion H. auto.

    simpl in *. omega.
Qed.

Obligation Tactic := program_simpl.
Program Fixpoint dec_clk_nocyc
    C x
    (l: {l: list ident |
            (forall x, In x l -> ~ M.MapsTo x None C ) /\
            (forall x' y, In x' l -> M.MapsTo x' (Some y) C -> In y l \/ y = x) /\
            (NoDup l) /\
            (~ In x l) /\
            (forall x, In x l -> M.In x C ) } )

    { measure (M.cardinal C - length l) }

    : { clk_nocyc C x } + { ~ clk_nocyc C x } :=

  match M.find x C with
    | None => in_right
    | Some None => in_left
    | Some (Some y) =>
        if in_dec _ y (x::l)
          then in_right
          else if dec_clk_nocyc C y (x::l)
                  then in_left
                  else in_right
  end.

Next Obligation.
  assert (~ M.In x C) by map_trivial.
  contradict H.
  inversion H; eauto.
Qed.

Next Obligation.
  constructor.
  map_trivial.
Qed.

Next Obligation.
  apply Pos.eq_dec.
Qed.

Next Obligation.
  clear dec_clk_nocyc.
  rename n into HH1.
  rename o into HH2.
  rename n0 into HH3.
  rename n1 into HH4.
  rename i into HH10.

  assert (HH5: forall x' y',
                 In x' (y::x::l) ->
                 M.MapsTo x' (Some y') C ->
                 In y' (y::x::l) ).
  { intros.
    simpl in H0.
    repeat destruct H0 as [ HH6 | H0 ].
    - subst. destruct H.
      + subst.
        assert (M.MapsTo x' (Some x') C) by map_trivial.
        map_trivial.
        injection HHH; simpl; auto.
      + edestruct HH2; eauto.
        * simpl; auto.
        * simpl; auto.
    - subst.
      assert (M.MapsTo x' (Some y) C) by map_trivial.
      map_trivial. injection HHH; intro. subst.
      simpl; auto.
    - destruct HH2 with (x':=x') (y:=y'); auto.
      simpl; auto.
      simpl; auto. }

  assert (HH6: In x (y :: x :: l)).
    simpl; auto.

  assert (HH7: forall x', In x' (y :: x :: l) -> ~ M.MapsTo x' None C).
  { intros.
    simpl in H0.
    repeat destruct H0 as [ HH8 | H0 ]; subst.

    + destruct H.
      - subst.
        assert (M.MapsTo x' (Some x') C) by map_trivial.
        intro. map_trivial.
      - apply HH1. assumption.

    + assert (M.MapsTo x' (Some y) C) by map_trivial.
      intro. map_trivial.

    + apply HH1; eauto. }

  set (l' := y :: x :: l) in *. clearbody l'.
  clear - HH5 HH6 HH7.
  intro. induction H.
  + assert (HH8 := HH7 x HH6).
    contradiction.
  + apply IHclk_nocyc.
    eapply HH5; eauto.
Qed.

Next Obligation.
  rename n into HH1.
  rename o into HH2.
  rename n0 into HH3.
  rename n1 into HH4.
  rename i into HH10.

  repeat split; intros.
  - destruct H0.
    + subst.
      assert (M.MapsTo x0 (Some y) C) by map_trivial.
      intro. map_trivial.
    + apply HH1; auto.
  
  - destruct H0.
    + subst. right.
      assert (M.MapsTo x' (Some y) C) by map_trivial.
      map_trivial.
      injection HHH; trivial.
    + left. destruct HH2 with (x':=x') (y:=y0); auto.

  - constructor; eauto.

  - contradict H. auto.

  - destruct H0.
    + subst x0.
      assert (M.MapsTo x (Some y) C) by map_trivial.
      eauto.
    + apply HH10. auto.
Qed.

Next Obligation.
  rename n into HH1.
  rename o into HH2.
  rename n0 into HH3.
  rename n1 into HH4.
  rename i into HH10.

  cut (length (x::l) <= M.cardinal C).
    intros; simpl in *. omega.

  assert (NoDup (x::l)).
    constructor; auto.

  rewrite M.cardinal_1.

  rewrite <- map_length with
    (f := fun z : M.key * clock => let (x, e) := z in x).

  set (la := x :: l) in *.
  set (lb := map (fun z : M.key * clock =>
                    let (x0, _) := z in x0) (M.elements C)).

  assert (forall x, In x la -> In x lb).
    intros.

    { destruct H1.
      - subst x0.

        assert (HH7: M.MapsTo x (Some y) C) by map_trivial.

        apply in_map_iff.
        exists (x, Some y); split; auto.

        apply map_InA.
        apply MF.elements_mapsto_iff.
        auto.

      - apply HH10 in H1.
        destruct H1 as [ c H1 ].

        apply in_map_iff.
        exists (x0, c); split; auto.

        apply map_InA.
        apply MF.elements_mapsto_iff.
        auto. }

  clear - H0 H1. clearbody la lb.
  apply list_nodup_length; auto.
  apply Pos.eq_dec.
Qed.
  
Next Obligation.
  constructor 2 with (x':=y); eauto; map_trivial.
Qed.

Next Obligation.
  contradict H0.
  inversion H0.
  - assert (M.MapsTo x (Some y) C) by map_trivial.
    map_trivial.
  - assert (M.MapsTo x (Some y) C) by map_trivial.
    map_trivial.
    congruence.
Qed.

Lemma dec_clk_nocyc' :
  forall C x,
    { clk_nocyc C x } + { ~ clk_nocyc C x }.
Proof.
  intros.
  apply dec_clk_nocyc. exists (@nil ident). repeat split; intros.
  + inversion H.
  + inversion H.
  + constructor.
  + intro H. inversion H.
  + inversion H.
Qed.


Inductive dep_nocyc : ident -> expr -> Prop :=
  | DNvar : forall x t c,
              dep_nocyc x (Evar x t c)

  | DNwhenA : forall e x t c,
                dep_nocyc x (Ewhen e x t c)

  | DNwhenB : forall e x t c x',
                dep_nocyc x' e ->
                dep_nocyc x' (Ewhen e x t c)

  | DNcurrA : forall e x ui t c,
                dep_nocyc x (Ecurr e x ui t c)

  | DNcurrB : forall e x ui t c x',
                dep_nocyc x' e ->
                dep_nocyc x' (Ecurr e x ui t c)

  | DNfby : forall ea eb t c x,
              dep_nocyc x ea ->
              dep_nocyc x (Efby ea eb t c)

  | DNdata1 : forall o ea t c x,
                dep_nocyc x ea ->
                dep_nocyc x (Edata1 o ea t c)

  | DNdata2A : forall o ea eb t c x,
                 dep_nocyc x ea ->
                 dep_nocyc x (Edata2 o ea eb t c)

  | DNdata2B : forall o ea eb t c x,
                 dep_nocyc x eb ->
                 dep_nocyc x (Edata2 o ea eb t c)
  
  | DNdata3A : forall o ea eb ec t c x,
                 dep_nocyc x ea ->
                 dep_nocyc x (Edata3 o ea eb ec t c)

  | DNdata3B : forall o ea eb ec t c x,
                 dep_nocyc x eb ->
                 dep_nocyc x (Edata3 o ea eb ec t c)

  | DNdata3C : forall o ea eb ec t c x,
                 dep_nocyc x ec ->
                 dep_nocyc x (Edata3 o ea eb ec t c)

  .

Hint Constructors dep_nocyc : constr.

Program Fixpoint extract_dep
        ( e : expr )
      : { ld : list ident | forall x, dep_nocyc x e <-> In x ld } :=
  match e with
    | Evar x t c => [x]
    | Econst u t c => nil
    | Ewhen e x t c => x :: extract_dep e
    | Ecurr e x ui t c => x :: extract_dep e
    | Efby ea eb t c => extract_dep ea
    | Edata1 o ea t c => extract_dep ea
    | Edata2 o ea eb t c => extract_dep ea ++ extract_dep eb
    | Edata3 o ea eb ec t c => extract_dep ea ++ extract_dep eb ++ extract_dep ec
  end.
Next Obligation.
  split; intros.
  + inversion H; auto.
  + destruct H.
    - subst. eauto with constr.
    - contradiction.
Qed.
Next Obligation.
  split; intros.
  + inversion H.
  + contradiction.
Qed.
Next Obligation.
  split; intros.
  + inversion H; subst; auto.
    right. apply i. auto.
  + destruct H.
    - subst.
      constructor.
    - apply i in H.
      constructor. auto.
Defined.
Next Obligation.
  split; intros.
  + inversion H; subst; auto.
    right. apply i. auto.
  + destruct H.
    - subst.
      constructor.
    - apply i in H.
      constructor. auto.
Defined.
Next Obligation.
  split; intros.
  + inversion H. subst. apply i in H2. auto.
  + apply i in H. constructor. auto.
Defined.
Next Obligation.
  split; intros.
  + inversion H. subst. apply i in H2. auto.
  + apply i in H. constructor. auto.
Defined.
Next Obligation.
  rewrite in_app_iff.
  split; intros.
  + inversion H; subst; firstorder.
  + destruct H; [ eapply DNdata2A | eapply DNdata2B ]; firstorder.
Defined.
Next Obligation.
  do 2 rewrite in_app_iff.
  split; intros.
  + inversion H; subst; [ left | right; left | right; right ]; firstorder.
  + repeat destruct H as [H2 | H];
    [ eapply DNdata3A | eapply DNdata3B | eapply DNdata3C ]; firstorder.
Defined.

Lemma dep_nocyc_0 :
  forall K E e,
    ( forall x, dep_nocyc x e -> nocycX K E x) ->
    nocyc K E e.
Proof.
  intros.
  induction e; eauto 30 with constr.
Qed.

Lemma dep_nocyc_1 :
  forall K E e x,
    nocyc K E e ->
    dep_nocyc x e ->
    nocycX K E x.
Proof.
  intros.
  induction e;
  match goal with
    [ H : nocyc _ _ _ |- _ ] => inversion H
  end;
  match goal with
    [ H : dep_nocyc _ _ |- _ ] => inversion H
  end; eauto.
Qed.

Obligation Tactic := program_simpl.

Program Fixpoint dec_nocycX
    K E
    xa
    (lp: {lp: list ident |
              (forall x, In x lp -> ~ M.MapsTo x Kin K) /\
              (forall x e,
                 In x lp ->
                 M.MapsTo x e E ->
                 exists y,
                   dep_nocyc y e /\
                   ( In y lp \/ y = xa ) ) /\
              (NoDup lp) /\
              (~ In xa lp) /\
              (forall x, In x lp -> M.In x E ) } )
    (lc0: { lc: list ident | forall x, In x lc -> nocycX K E x} )

    { measure (M.cardinal E - length lp) }

    : ( { nocycX K E xa } + { ~ nocycX K E xa } ) *
      ( { lc : list ident | forall x, In x lc -> nocycX K E x} ) :=

  let dec_nocyc' :=
      fix dec_nocyc
            (Hx: ~ M.MapsTo xa Kin K)
            (e: expr) (He: M.MapsTo xa e E)
            (ld: list ident)
            (le: list ident)
            (Hde : forall x, dep_nocyc x e <-> In x ld \/ In x le)
            (Hle : forall x, In x le -> nocycX K E x)
            (lc: { lc: list ident | forall x, In x lc -> nocycX K E x} )

            { struct ld }
        : ( { nocyc K E e } + { ~ nocyc K E e } ) *
          ( { lc : list ident | forall x, In x lc -> nocycX K E x} ) :=
    match ld with
      | nil => (in_left, lc)
      | xb :: ld' =>
          if in_dec _ xb (xa::lp) then (in_right, lc)
          else
            let (res, lc') := dec_nocycX K E xb (xa::lp) lc in
            if res then
              let (res', lc'') := dec_nocyc Hx e He ld' (xb::le) _ _ lc' in
              if res' then (in_left, lc'') else (in_right, lc'')
            else
              (in_right, lc')
    end in


  if in_dec _ xa lc0
  then (in_left, lc0)
  else
    match M.find xa K with
      | Some Kin => (in_left, xa::lc0)
      | _ =>
        match M.find xa E with
          | None => (in_right, lc0)
          | Some e =>
            let (res, lc0') := dec_nocyc' _ e _ (extract_dep e) nil _ _ lc0 in
            if res then (in_left, xa::lc0') else (in_right, lc0')
        end
    end.

Next Obligation.
  apply dep_nocyc_0.
  intros.
  apply Hde in H1.
  destruct H1; [ destruct H1 | ]; auto.
Defined.

Next Obligation.
  apply Pos.eq_dec.
Defined.

Next Obligation.
  rename n into Hlp1.
  rename e0 into Hlp2.
  rename n0 into Hlp3.
  rename n1 into Hlp4.
  rename i into Hlp5.

  set (ll := xb :: xa :: lp).

  assert (Hll1 : forall x,
                   In x ll ->
                   ~ M.MapsTo x Kin K ).
  { intros.
    subst ll. simpl in H2. repeat destruct H2 as [HH1 | H2].
    + destruct H.
      - congruence.
      - apply Hlp1; congruence.
    + congruence.
    + apply Hlp1. auto. }

  assert (Hll2 : forall x e,
                   In x ll ->
                   M.MapsTo x e E ->
                   exists y,
                     dep_nocyc y e /\ In y ll).
  { intros.
    subst ll. simpl in H2. repeat destruct H2 as [HH1 | H2].
    + destruct H.
      - subst.
        map_trivial.
        exists x. split.
        * apply Hde. left. simpl; auto.
        * simpl; auto.
      - subst.
        destruct Hlp2 with (x:=x) (e:=e0); auto. simpl'.
        exists x0. split.
        * auto.
        * destruct H4; simpl; auto.
    + subst. map_trivial.
      exists xb. split.
      - apply Hde. left. simpl; auto.
      - simpl; auto.
    + destruct Hlp2 with (x:=x) (e:=e0); auto. simpl'.
      exists x0; split.
      - auto.
      - destruct H5; simpl; auto. }

  assert (Hll3: In xa ll).
    subst ll; simpl; auto.

  clearbody ll. clear - Hll1 Hll2 Hll3 He.
  intro.

  assert (forall x, nocycX K E x -> In x ll -> False ).
  { clear - Hll1 Hll2.

    refine (InocycX K E
      ( fun e _ => forall x, dep_nocyc x e -> In x ll -> False )
      ( fun x _ => In x ll -> False )
      _ _ _ _ _ _ _ _ _ _ ); (* apply does not work.. *)

    intros;

    try match goal with
      [ H : dep_nocyc _ _ |- _ ] => inversion H
    end; subst; try contradiction; eauto.

    + specialize (Hll1 x H). contradiction.
    + destruct Hll2 with (x := x) (e := e); auto.
      destruct H1. eapply H; eauto. }

  destruct Hll2 with (x:=xa) (e:=e); auto. simpl'.
  assert (nocycX K E x).
    eapply dep_nocyc_1; eauto.
  eauto.
Defined.

Next Obligation.
  rename n into Hlp1.
  rename e0 into Hlp2.
  rename n0 into Hlp3.
  rename n1 into Hlp4.
  rename i into Hlp5.

  repeat split; intros.
  + destruct H2.
    - congruence.
    - apply Hlp1; auto.
  + destruct H2.
    - exists xb. split.
      * subst; map_trivial. apply Hde.
        left. simpl; auto.
      * right; auto.
    - destruct Hlp2 with (x:=x) (e:=e0); auto. simpl'.
      exists x0; destruct H5; split; auto.
  + constructor; auto.
  + auto.
  + destruct H2.
    - subst. eauto.
    - apply Hlp5; auto.
Defined.
  
Next Obligation.
  rename n into Hlp1.
  rename e0 into Hlp2.
  rename n0 into Hlp3.
  rename n1 into Hlp4.
  rename i into Hlp5.

  cut (length (xa::lp) <= M.cardinal E).
    intros; simpl in *. omega.

  assert (NoDup (xa::lp)).
    constructor; auto.

  rewrite M.cardinal_1.

  rewrite <- map_length with
    (f := fun z : M.key * expr => let (x, e) := z in x).

  set (la := xa :: lp) in *.
  set (lb := map (fun z : M.key * expr =>
                    let (x0, _) := z in x0) (M.elements E)).

  assert (forall x, In x la -> In x lb).
    intros.

    { destruct H3.
      - subst x.

        apply in_map_iff.
        exists (xa, e); split; auto.

        apply map_InA.
        apply MF.elements_mapsto_iff.
        auto.

      - apply Hlp5 in H3.
        destruct H3 as [ e' H3 ].

        apply in_map_iff.
        exists (x, e'); split; auto.

        apply map_InA.
        apply MF.elements_mapsto_iff.
        auto. }

  clearbody la lb. clear - H2 H3.
  apply list_nodup_length; auto.
  apply Pos.eq_dec.
Defined.

Next Obligation.
  rewrite Hde. subst.
  simpl. tauto.
Defined.

Next Obligation.
  destruct H1.
  + congruence.
  + auto.
Defined.

Next Obligation.
  contradict H0.
  eapply dep_nocyc_1; eauto.
  apply Hde. left. subst; simpl; auto.
Defined.

Next Obligation.
  apply Pos.eq_dec.
Defined.

Next Obligation.
  constructor. map_trivial.
Qed.

Next Obligation.
  destruct H0.
  + subst xa. constructor. map_trivial.
  + auto.
Qed.

Next Obligation.
  intro. inversion H2.
  + congruence.
  + congruence.
Qed.

Next Obligation.
  map_trivial.
Qed.

Next Obligation.
  destruct (extract_dep e); simpl in *.
  firstorder.
Qed.

Next Obligation.
  contradiction.
Qed.

Next Obligation.
  constructor 2 with (e:=e); auto.
  map_trivial.
Qed.

Next Obligation.
  destruct H2.
  - constructor 2 with (e:=e); auto.
    map_trivial.
  - auto.
Qed.

Next Obligation.
  contradict H1.
  inversion H1.
  + contradict H0.
    auto.
  + assert (M.MapsTo xa e E) by map_trivial.
    map_trivial.
Qed.

Lemma dec_nocycX' :
  forall K E x,
    { nocycX K E x } + { ~ nocycX K E x }.
Proof.
  intros.
  apply dec_nocycX.
  + exists (@nil ident).
    repeat split; intros; simpl in *; try contradiction.
    constructor.
    auto.
  + exists (@nil ident).
    intros.
    simpl in H. contradiction.
Defined.

Program Fixpoint dec_list
    T (l: list T)
    ( P : T -> Prop )
    ( Pdec : forall x, { P x } + { ~ P x } ):

    { forall x, In x l -> P x } +
    { ~ forall x, In x l -> P x } :=

  match l with
    | nil => in_left
    | x::xs =>
        if Pdec x then
          if dec_list T xs P Pdec then
            in_left
          else
            in_right
        else
          in_right
  end.
Next Obligation.
  destruct H.
Qed.
Next Obligation.
  destruct H1.
  + congruence.
  + eauto.
Qed.

Program Definition dec_map
    T ( m:M.t T )
    ( P: M.key -> T -> Prop )
    ( Pdec: forall x e, { P x e } + { ~ P x e } ):

    { forall x e, M.MapsTo x e m -> P x e } +
    { ~ forall x e, M.MapsTo x e m -> P x e } :=

  if dec_list _ (M.elements m) (fun xx => let (x,e) := xx in P x e) _ then
    in_left
  else
    in_right.
Next Obligation.
  specialize (H (x,e)).

  assert (In (x,e) (M.elements m)).
    apply map_InA.
    apply M.elements_1.
    assumption.

  simpl'. simpl in H. assumption.
Qed.
Next Obligation.
  contradict H.

  intros. destruct x as [x e].
  apply H.

  apply M.elements_2.
  apply map_InA.

  assumption.
Qed.


Program Definition dec_PconsistentT K T :
    { PconsistentT K T } + { ~ PconsistentT K T } :=

  check (dec_map _ K (fun x k => M.In x T) _);
  check (dec_map _ T (fun x k => M.In x K) _);
  in_left.

Next Obligation.
  apply MF.In_dec.
Qed.
Next Obligation.
  apply MF.In_dec.
Qed.
Next Obligation.
  split; intros; destruct H1; [ eapply H0 | eapply H ]; eauto.
Qed.
Next Obligation.
  contradict H0.
  unfold PconsistentT in H0.

  intros.
  specialize (H0 x).
  apply H0.
  eauto.
Qed.
Next Obligation.
  contradict H.
  unfold PconsistentT in H.

  intros.
  specialize (H x).
  apply H.
  eauto.
Qed.

Program Definition dec_PconsistentC K C :
    { PconsistentC K C } + { ~ PconsistentC K C } :=

  check (dec_map _ K (fun x k => M.In x C) _);
  check (dec_map _ C (fun x k => M.In x K) _);
  in_left.

Next Obligation.
  apply MF.In_dec.
Qed.
Next Obligation.
  apply MF.In_dec.
Qed.
Next Obligation.
  split; intros; destruct H1; [ eapply H0 | eapply H ]; eauto.
Qed.
Next Obligation.
  contradict H0.
  unfold PconsistentC in H0.

  intros.
  specialize (H0 x).
  apply H0.
  eauto.
Qed.
Next Obligation.
  contradict H.
  unfold PconsistentC in H.

  intros.
  specialize (H x).
  apply H.
  eauto.
Qed.

Program Definition dec_PconsistentE K E :
    { PconsistentE K E } + { ~ PconsistentE K E } :=

  check (dec_map _ K (fun x k => k = Kout \/ k = Kloc -> M.In x E) _);
  check (dec_map _ E (fun x k => M.MapsTo x Kout K \/ M.MapsTo x Kloc K) _);
  in_left.

Next Obligation.
  destruct e.
  + left.
    intros.
    destruct H; discriminate.
  + destruct (MF.In_dec E x).
    - left. intros; eauto.
    - right. intros. contradict n.
      apply n. right. eauto.
  + destruct (MF.In_dec E x).
    - left. intros; eauto.
    - right. intros. contradict n.
      apply n. left. eauto.
Qed.
Next Obligation.
  case_eq (M.find x K).
  + intros.
    assert (M.MapsTo x k K) by map_trivial.
    destruct k.
    - right.
      intro; destruct H2; map_trivial.
    - left. auto.
    - left. auto.
  + intros.
    assert (~ M.In x K) by map_trivial.
    right. contradict H1.
    destruct H1; eauto.
Qed.
Next Obligation.
  split.
  + intros [e HH]; eapply H0; eauto.
  + intros.
    destruct H1.
    - eapply H; eauto.
    - eapply H; eauto.
Qed.
Next Obligation.
  contradict H0.
  unfold PconsistentE in H0.

  intros.
  specialize (H0 x).
  apply H0.
  eauto.
Qed.
Next Obligation.
  contradict H.
  unfold PconsistentE in H.

  intros.
  specialize (H x).
  apply H.
  destruct H1; [ left | right ]; congruence.
Qed.


Program Definition dec_Pwell_type T C E :
    { Pwell_type T C E } + { ~ Pwell_type T C E } :=

  check (dec_map _ E (fun x e => well_type T C e) _);
  in_left.

Next Obligation.
  apply dec_well_type.
Qed.


Program Definition dec_Pwell_type_t T E :
    { Pwell_type_t T E } + { ~ Pwell_type_t T E } :=

  check (dec_map _ E (fun x e =>
                        forall t, M.MapsTo x t T -> typeof e = t ) _);
  in_left.

Next Obligation.
  case_eq (M.find x T).
  - intros.
    assert (M.MapsTo x t T) by map_trivial.
    destruct (dec_type (typeof e) t).
    + left. intros. map_trivial.
    + right. contradict n. eauto.
  - intros.
    left.
    assert (~ M.In x T) by map_trivial.
    intros. contradict H0. eauto.
Qed.

Next Obligation.
  firstorder.
Qed.

Next Obligation.
  contradict H.
  firstorder.
Qed.


Program Definition dec_Pwell_type_c C E :
    { Pwell_type_c C E } + { ~ Pwell_type_c C E } :=

  check (dec_map _ E (fun x e =>
                        forall c, M.MapsTo x c C -> clockof e = c ) _);
  in_left.

Next Obligation.
  case_eq (M.find x C).
  - intros.
    assert (M.MapsTo x c C) by map_trivial.
    destruct (dec_clock (clockof e) c).
    + left. intros. map_trivial.
    + right. contradict n. eauto.
  - intros.
    left.
    assert (~ M.In x C) by map_trivial.
    intros. contradict H0. eauto.
Qed.

Next Obligation.
  firstorder.
Qed.

Next Obligation.
  contradict H.
  firstorder.
Qed.

    
Program Definition dec_Pclk_bool_inp K T C :
    { Pclk_bool_inp K T C } + { ~ Pclk_bool_inp K T C } :=

  check (dec_map _ K (fun x k =>
                        k = Kin ->
                        forall x',
                          M.MapsTo x (Some x') C ->
                          M.MapsTo x' Tbool T ) _);
  in_left.

Next Obligation.
  case_eq e; intro.
  * case_eq (M.find x C).
    - intros.
      assert (M.MapsTo x c C) by map_trivial.
      + { destruct c as [ x' | ].
          + case_eq (M.find x' T); intros.
            - destruct t.
              * left. intros. map_trivial. simpl'. subst x'0. map_trivial.
              * right. intro.
                assert (M.MapsTo x' Tbool T).
                  apply H3; eauto.
                assert (M.MapsTo x' Tz T) by map_trivial.
                map_trivial.
            - right.
              assert (~ M.In x' T) by map_trivial.
              contradict H3.
              exists Tbool; apply H3; eauto.

          + left. intros.
            map_trivial. }

    - left. intros.
      assert (~ M.In x C) by map_trivial.
      contradict H3. eauto.

  * left. intros. discriminate.
  * left. intros. discriminate.
Qed.

Next Obligation.
  firstorder.
Qed.

Next Obligation.
  contradict H. intros. subst e.
  firstorder.
Qed.


Program Definition dec_Pout_clk_in K C :
    { Pout_clk_in K C } + { ~ Pout_clk_in K C } :=

  check (dec_map _ K (fun x k =>
                        k = Kout ->
                        forall x',
                          M.MapsTo x (Some x') C ->
                          M.MapsTo x' Kin K ) _);
  in_left.

Next Obligation.
  case_eq e; intro.
  * left. intros. discriminate.
  * left. intros. discriminate.
  * case_eq (M.find x C).
    - intros.
      assert (M.MapsTo x c C) by map_trivial.
      + { destruct c as [ x' | ].
          + case_eq (M.find x' K); intros.
            - destruct k.
              * left. intros. map_trivial. simpl'. subst; map_trivial.
              * right. intro.
                assert (M.MapsTo x' Kin K).
                  apply H3; eauto.
                assert (M.MapsTo x' Kloc K) by map_trivial.
                map_trivial.
              * right. intro.
                assert (M.MapsTo x' Kin K).
                  apply H3; eauto.
                assert (M.MapsTo x' Kout K) by map_trivial.
                map_trivial.
            - right.
              assert (~ M.In x' K) by map_trivial.
              contradict H3.
              exists Kin; apply H3; eauto.

          + left. intros.
            map_trivial. }

    - left. intros.
      assert (~ M.In x C) by map_trivial.
      contradict H3. eauto.
Qed.

Next Obligation.
  firstorder.
Qed.

Next Obligation.
  contradict H. intros. subst e.
  firstorder.
Qed.

Program Definition dec_Pin_clk_in K C :
    { Pin_clk_in K C } + { ~ Pin_clk_in K C } :=

  check (dec_map _ K (fun x k =>
                        k = Kin ->
                        forall x',
                          M.MapsTo x (Some x') C ->
                          M.MapsTo x' Kin K ) _);
  in_left.

Next Obligation.
  case_eq e; intro.
  * case_eq (M.find x C).
    - intros.
      assert (M.MapsTo x c C) by map_trivial.
      + { destruct c as [ x' | ].
          + case_eq (M.find x' K); intros.
            - destruct k.
              * left. intros. map_trivial. simpl'. subst; map_trivial.
              * right. intro.
                assert (M.MapsTo x' Kin K).
                  apply H3; eauto.
                assert (M.MapsTo x' Kloc K) by map_trivial.
                map_trivial.
              * right. intro.
                assert (M.MapsTo x' Kin K).
                  apply H3; eauto.
                assert (M.MapsTo x' Kout K) by map_trivial.
                map_trivial.
            - right.
              assert (~ M.In x' K) by map_trivial.
              contradict H3.
              exists Kin; apply H3; eauto.

          + left. intros.
            map_trivial. }

    - left. intros.
      assert (~ M.In x C) by map_trivial.
      contradict H3. eauto.
  * left. intros. discriminate.
  * left. intros. discriminate.
Qed.

Next Obligation.
  firstorder.
Qed.

Next Obligation.
  contradict H. intros. subst e.
  firstorder.
Qed.


Program Definition dec_Pclk_nocyc_inp K C:
    { Pclk_nocyc_inp K C } + { ~ Pclk_nocyc_inp K C } :=

  check (dec_map _ K (fun x k =>
                        k = Kin ->
                        clk_nocyc C x ) _ );
  in_left.
Next Obligation.
  destruct e.
  + destruct (dec_clk_nocyc' C x).
    - left. auto.
    - right. contradict n. auto.
  + left. discriminate.
  + left. discriminate.
Qed.
Next Obligation.
  firstorder.
Qed.
Next Obligation.
  contradict H.
  intros; subst; firstorder.
Qed.

Program Definition dec_Pnocyc K E:
    { Pnocyc K E } + { ~ Pnocyc K E } :=

  check (dec_map _ K (fun x _ => nocycX K E x ) _ );
  in_left.
Next Obligation.
  apply dec_nocycX'.
Qed.
Next Obligation.
  firstorder.
Qed.
Next Obligation.
  contradict H.
  intros; subst; firstorder.
Qed.

Program Definition dec_WellFormed :
  forall p : Program,
    { WellFormed p } + { ~ WellFormed p } :=

  fun p =>

  let K := KK p in
  let T := TT p in
  let C := CC p in
  let E := EE p in

  check (dec_PconsistentT K T);
  check (dec_PconsistentC K C);
  check (dec_PconsistentE K E);
  check (dec_Pwell_type T C E);
  check (dec_Pwell_type_t T E);
  check (dec_Pwell_type_c C E);
  check (dec_Pnocyc K E);
  check (dec_Pclk_nocyc_inp K C);
  check (dec_Pclk_bool_inp K T C);
  check (dec_Pout_clk_in K C);
  check (dec_Pin_clk_in K C);
  in_left.

Next Obligation.
  constructor; auto.
Qed.

Solve Obligations using
  program_simpl;
  match goal with
    [ H: ~ _ |- _ ] =>
      contradict H; inversion H; auto
  end.


Require Import ClockUnifyImpl.

(** Statically check a program, and perform the clock-unifying transformation *)
Program Definition translate_failable (p : Program) : option Program :=
  if dec_WellFormed p
  then Some (TranslationImpl.translate p _)
  else None.

(* We do not depend on the axioms implicitly imported by 'Import Program' *)
Print Assumptions translate_failable.
