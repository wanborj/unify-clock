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


Require Import Common SingleNode ClockUnify.

(** A proof that the specification preserves semantics *)

Module TranslationProof (Import T : Translation) <: TranslationFacts T.
  Module RF := Refinement.

  Theorem T2 :
    forall p q n Ip Iq,
    forall WF: WellFormed p,
      T.translate p WF = q ->
      ValidInput p n Ip ->
      RF.refining (TT p) Ip Iq ->
      ValidInput q n Iq.
  Proof.
    intros.
    eapply RF.RF_0; eauto; subst; intros.
    + eapply trans_i; eauto.
    + eapply trans_t; eauto.
    + eapply trans_c; eauto.
  Qed.

  Section PROOF.
    Variable n : time.
    Variables p : Program.
    Variables Ip Iq : Eio.

    Hypothesis WFp : WellFormed p.
    Hypothesis VIp : ValidInput p n Ip.

    Let q := translate p WFp.
    Hypothesis RF_inp : RF.refining (TT p) Ip Iq.

    Lemma VIq' : ValidInput q n Iq.
    Proof.
      eapply T2; unfold q; eauto.
    Qed.

    Lemma WFq' : WellFormed q.
    Proof.
      eapply GoodProperties; eauto.
      reflexivity.
    Qed.

    Notation evalXP     := (evalX (EE p) Ip).
    Notation evalEP     := (eval (EE p) Ip).
    Notation evalXQ     := (evalX (EE q) Iq).
    Notation evalEQ     := (eval (EE q) Iq).
    Notation well_typeP := (well_type (TT p) (CC p)).
    Notation well_typeQ := (well_type (TT q) (CC q)).

    Notation evalP'  := (evalP (EE p) Ip).
    Notation trans'  := (trans  p q).
    Notation transC' := (transC p q).
    Notation transF' := (transF p q).
    Notation transR' := (transR p q).

    Notation clk_nocyc'     := (clk_nocyc (CC p)).
    Notation conform_clock' := (conform_clock (EE p) Ip).
    Notation nocyc_strong'  := (nocyc_strong (KK p) (CC p) (EE p)).
    Notation nocyc_strongX' := (nocyc_strongX (KK p) (CC p) (EE p)).
    Notation nocyc_strongC' := (nocyc_strongC (KK p) (CC p) (EE p)).

    Ltac init :=
      assert (WFq: WellFormed q) by apply WFq';
      assert (VIq: ValidInput q n Iq) by apply VIq'.

    Ltac kind_consistent :=
      destructP;
      kind_consistent'.
    
    Ltac kind_attach x K :=
      progress (
        try (assert (M.MapsTo x Kin K) by kind_consistent);
        try (assert (M.MapsTo x Kout K \/ M.MapsTo x Kloc K) by kind_consistent)
      ) || (
        try (assert (M.In x K) by kind_consistent)
      ).

    Definition PM_on i xp xq :=
      forall u,
        evalXP xp i [u] ->
        evalXQ xq i [u].

    Definition PM_on_EE i ep eq :=
      forall u,
        evalEP ep i [u] ->
        evalEQ eq i [u].

    Definition PM_keep i xp xq :=
      forall j u,
        S j = i ->
        evalXP xp i Vbot ->
        evalXQ xq j [u] ->
        evalXQ xq i [u].

    Definition PM_keep_EE i xp xq :=
      forall j u,
        S j = i ->
        evalEP xp i Vbot ->
        evalEQ xq j [u] ->
        evalEQ xq i [u].

    Definition PM_false i xp xq :=
        evalXP xp i Vbot ->
        evalXQ xq i [Vbool false].

    Definition PM_on_QEX i xc eq xq :=
      forall u,
        evalXQ xc i [Vbool true] ->
        evalEQ eq i [u] ->
        evalXQ xq i [u].

    Definition PM_keep_Q i xc xq :=
      forall j u,
        S j = i ->
        evalXQ xc i [Vbool false] ->
        evalXQ xq j [u] ->
        evalXQ xq i [u].

    Lemma inp_PM_on :
      forall i x,
        i < n ->
        M.MapsTo x Kin (KK p) ->
        PM_on i x x.
    Proof.
      init. unfold PM_on; intros.

      assert (HH: M.MapsTo x Kin (KK q)).
        apply trans_k; assumption.

      assert (HH2: M.In x Iq) by kind_consistent.
      destruct HH2 as [ sq HH2 ].

      assert (HH3: M.In x Ip) by kind_consistent.
      destruct HH3 as [ sp HH3 ].

      eapply RVin; eauto.
      inversion RF_inp. eapply RF_on; eauto.
      inversion H1.
      + map_trivial.

      + (* impossible case *)
        kind_attach x (KK p).
        kind_case; map_trivial.
    Qed.

    Lemma transC_none :
      forall i xc,
        transC' None xc ->
        evalXQ xc i [Vbool true].
    Proof.
      init. intros.
      inversion H; clear H; subst. 

      eauto with constr.
    Qed.

    Lemma transC_on :
      forall i x xc,
        PM_on i x x ->
        ( forall x' xc',
            M.MapsTo x (Some x') (CC p) ->
            transC' (Some x') xc' ->
            PM_on i x' xc' ) ->
        transC' (Some x) xc ->
        PM_on i x xc.
    Proof.
      intros.
      rename H into Hx.
      rename H0 into HH.
      rename H1 into HH2.

      inversion HH2; subst; clear HH2.

      destruct c as [ x' | ].

      (* base clock = Some x' *)
      specialize (HH x' xc0). simpl'.
      
      unfold PM_on. intros.
      
      assert (evalEQ (Evar x Tbool None) i [u]).
        apply Rvar.
        apply Hx.
        assumption.
      
      assert (HH2: conform_clock' [u] (Some x') i) by program_trivial.
      inversion HH2. subst.
      
      assert (evalEQ (Evar xc0 Tbool None) i [Vbool true]).
        apply Rvar.
        apply HH; try assumption.
      
      assert (evalEQ (Econst (Vbool false) Tbool None) i [Vbool false]).
        apply Rconst.
      
      eapply RVdef; eauto.
      eapply Rdata3; eauto.
      constructor.
      
      (* base clock = None *)
      assert (evalEQ (Evar xc0 Tbool None) i [Vbool true]).
        apply Rvar.
        apply transC_none; assumption.
      
      unfold PM_on. intros.
      
      assert (evalEQ (Evar x Tbool None) i [u]).
        apply Rvar.
        apply Hx.
        assumption.
      
      assert (evalEQ (Econst (Vbool false) Tbool None) i [Vbool false]).
        apply Rconst.
      
      eauto with constr.
    Qed.

    Lemma transC_false :
      forall i x xc,
        i < n ->
        PM_on i x x ->
        ( forall x' xc',
            M.MapsTo x (Some x') (CC p) ->
            transC' (Some x') xc' ->
            PM_on i x' xc' /\ PM_false i x' xc' ) ->
        transC' (Some x) xc ->
        PM_false i x xc.
    Proof.
      init. intros.
      rename H into Hi.
      rename H0 into Hx.
      rename H1 into HHH.
      rename H2 into HH.

      inversion HH; subst; clear HH.
     
      destruct c as [x' | ]. specialize (HHH x' xc0). simpl'.
     
      (* base clock = Some x' *)
      
      unfold PM_false. intros.

      assert (M.In x (KK p)) by kind_consistent.
      assert (M.In x (KK q)).
        destruct H5 as [ xk H5 ]. exists xk.
        eapply trans_k; eauto.

      assert (HH: exists v, evalXQ x i v) by program_trivial.
      destruct HH as [xqv HH].
     
      assert (HH3: conform_clock (EE q) Iq xqv None i).
        cut (M.MapsTo x None (CC q)).
          intros; program_trivial.
        cut (M.In x (KK q)).
          intro.
          assert (HH4: M.In x (CC q)).
            kind_consistent.
          destruct HH4 as [ xqc HH4 ].
          assert (xqc = None).
            eapply trans_c with (p:=p); eauto.
          subst. assumption.
        inversion HH; kind_consistent.
      inversion HH3; subst; clear HH3.
     
      assert (evalEQ (Evar x Tbool None) i [u]).
        apply Rvar; assumption.
     
      assert (evalEQ (Econst (Vbool false) Tbool None) i [Vbool false]).
        apply Rconst.
     
      assert (HH2: conform_clock' Vbot (Some x') i) by program_trivial.
      inversion HH2; clear HH2; subst.
     
        (* x' -> [false] *)
     
      assert (evalEQ (Evar xc0 Tbool None) i [Vbool false]).
        apply Rvar. eapply H. assumption.
     
      eapply RVdef; eauto.
      eapply Rdata3; eauto.
      constructor.
     
        (* x' -> [true] *)
     
      assert (evalEQ (Evar xc0 Tbool None) i [Vbool false]).
        apply Rvar. eapply H3. assumption.
     
      eapply RVdef; eauto.
      eapply Rdata3; eauto.
      constructor.
     
      (* base clock = None *)
      unfold PM_false. intros.
     
      assert (HH2: conform_clock' Vbot None i) by program_trivial.
      inversion HH2.
    Qed.

    Lemma transR_on :
      forall i eq xc ui xr,
        i < n ->
        transR p q eq xc ui xr ->
        PM_on_QEX i xc eq xr.
    Proof.
      init. intros.
      inversion H0; clear H0; subst.
      
      unfold PM_on_QEX. intros.
      
      set (ec := (Efby (Econst ui (typeof eq) None)
                       (Evar xr (typeof eq) None)
                       (typeof eq)
                       None)) in *.
      
      assert (well_type (TT q) (CC q) ec).
        destructP.
        eapply WFwell_type in H1.
        inversion H1.
        assumption.
      
      assert (HH: forall i, i < n -> exists v, evalEQ ec i v).
        assert (PexistenceE (TT q) (CC q) (EE q) Iq n).
          program_trivial.
      
        intros.
        apply H4; try assumption.
      
      specialize (HH i). simpl'.
      destruct HH as [vc HH].
      
      assert (HH2: exists uc, vc = [uc]).
        assert (HH3: Pgood_val_cE (TT q) (CC q) (EE q) Iq).
          program_trivial.
      
        unfold Pgood_val_cE in *.
        specialize (HH3 ec i vc). simpl'.
        inversion HH3.
      
        eauto.
      
      destruct HH2 as [uc HH2]. subst vc.
      
      assert (evalEQ (Evar xc Tbool None) i [Vbool true]).
        constructor; eauto.
      
      eapply RVdef with
        (e := Edata3 Oif
                     (Evar xc Tbool None)
                     eq
                     ec
                     (typeof eq)
                     None); eauto.
      
      eapply Rdata3; eauto.
      
      constructor.
    Qed.

    Lemma transR_keep :
      forall i eq xc ui xr,
        i < n ->
        transR p q eq xc ui xr ->
        PM_keep_Q i xc xr.
    Proof.
      init. intros.

      unfold PM_keep_Q; intros.

      inversion H0; clear H0; subst.

      set (ec := Efby (Econst ui (typeof eq) None)
                      (Evar xr (typeof eq) None) (typeof eq) None) in *.

      assert (evalEQ ec (S j) [u]).
        eapply Rfby; [ constructor | ].
        eapply RPval.
        eapply Rvar.
        assumption.

      assert (HH: well_typeQ (Edata3 Oif (Evar xc Tbool None) eq ec (typeof eq) None)).
        destructP; eapply WFwell_type; eauto.

      assert (HH1: well_typeQ eq).
        inversion HH. assumption.

      assert (HH2: clockof eq = None).
        inversion HH. congruence.

      assert (HH3: forall i, i < n -> exists v, evalEQ eq i v).
        assert (HH4: PexistenceE (TT q) (CC q) (EE q) Iq n).
          program_trivial.
      
        intros.
        apply HH4; try assumption.
      
      specialize (HH3 (S j)). simpl'.
      destruct HH3 as [ vb HH3 ].

      assert (HH5: exists ub, vb = [ub]).
        assert (HH6: Pgood_val_cE (TT q) (CC q) (EE q) Iq).
          program_trivial.
      
        unfold Pgood_val_cE in *.
        specialize (HH6 eq (S j) vb). simpl'.
        rewrite HH2 in *.

        inversion HH6.
        eauto.

      destruct HH5 as [ ub HH5 ].

      subst.

      eauto with constr.
    Qed.

    Lemma transR_keep_2:
      forall i ep eq c xc ui xr t,
        i < n ->
        well_typeP ep ->
        clockof ep = c ->
        ( forall x, c = Some x -> PM_on i x xc /\ PM_false i x xc ) ->
        transR p q eq xc ui xr ->
        PM_keep_EE i ep (Evar xr t None).
    Proof.
      intros.
    
      unfold PM_keep_EE; intros; subst i.
    
      assert (evalXQ xc (S j) [Vbool false]).
        assert (HH: conform_clock' Vbot c (S j)).
          rewrite <- H1.
          program_trivial.
        inversion HH;
        clear H1; subst;
        specialize (H2 x); simpl'.
    
          (* x -> [false] *)
        eapply H1.
        assumption.
    
          (* x -> bot *)
        eapply H2.
        assumption.
    
      inversion H6; subst.
      eapply Rvar.
      eapply transR_keep; eauto.
    Qed.

    Lemma transR_prev_0 :
      forall e xc ui xr i,
        i < n ->
        well_typeQ e ->
        clockof e = None ->
        ( forall j, j <= i -> evalXQ xc j [ Vbool false ] ) ->
        transR' e xc ui xr ->
        evalXQ xr i [ui].
    Proof.
      init. intros.
      rename H into Hi.
      rename H0 into He.
      rename H1 into He2.
      rename H2 into HH.
      rename H3 into HH'.
      induction i.

      (* 0th instance *)
      inversion HH'; subst. clear HH'.

      assert (HH1: exists v, evalEQ e 0 v) by program_trivial.
      destruct HH1 as [ v HH1 ].

      assert (HH3: conform_clock (EE q) Iq v None 0).
        assert (HH4: Pgood_val_cE (TT q) (CC q) (EE q) Iq) by program_trivial.

        rewrite <- He2.
        eapply HH4; eauto.
      inversion HH3; subst.

      assert (HH2: evalXQ xc 0 [Vbool false]).
        eauto.

      assert (HH5: evalEQ (Econst ui (typeof e) None) 0 [ui]).
        eapply Rconst. eauto.

      eapply RVdef; eauto.
      eapply Rdata3; eauto.
        eapply Rvar; eauto.
        eapply Rfby; eauto.
        eapply RPinit; eauto.
        constructor.

      (* (i+1)th instance *)
      assert (evalXQ xc (S i) [Vbool false]).
        eauto.

      assert (evalXQ xr i [ui]).
        apply IHi; try omega; firstorder.

      eapply transR_keep; eauto.
    Qed.

    Lemma transR_prev_1 :
      forall e xc ui xr i j u,
        i < n ->
        well_typeQ e ->
        clockof e = None ->
        j <= i ->
        evalXQ xc j [Vbool true] ->
        evalEQ e j [u] ->
        ( forall k, j < k <= i -> evalXQ xc k [Vbool false] ) ->
        transR' e xc ui xr ->
        evalXQ xr i [u].
    Proof.
      intros.
      induction i.

      (* 0th instance *)
      assert (j = 0) by omega.
      subst; clear H2.

      eapply transR_on; eauto.

      (* (i+1)th instance *)
      assert (HH: j = S i \/ j <= i) by omega.
      destruct HH.

        (* j = i+1 *)
      subst.
      eapply transR_on; eauto.

        (* j <= i *)
      assert (HH: evalXQ xr i [u]).
        apply IHi; auto; try omega; firstorder.

      assert (HH2: evalXQ xc (S i) [Vbool false]).
        apply H5; omega.

      eapply transR_keep; eauto.
    Qed.

    Lemma transF_prev_0 :
      forall x xr i,
        ( forall j, j < i -> evalXQ x j [Vbool false] ) ->
        transF' x xr ->
        evalXQ xr i [Vbool true].
    Proof.
      intros.
      induction i.

      (* 0th instance *)
      inversion H0; subst; clear H0.

      eapply RVdef; eauto.
      eapply Rfby; eauto.
        eapply Rconst; eauto.
        eapply RPinit; eauto.

      (* (i+1)th instance *)
      assert (HH1: forall j, j < i -> evalXQ x j [Vbool false]).
        eauto.
      assert (HH2: evalXQ x i [Vbool false]).
        eauto.
      clear H. simpl'.

      inversion H0; subst; clear H0.

      eapply RVdef; eauto.
      eapply Rfby; eauto.
        eapply Rconst; eauto.
        eapply RPval; eauto.
          eapply Rdata3; eauto.
            eapply Rvar; eauto.
            eapply Rconst; eauto.
            eapply Rvar; eauto.
            constructor.
    Qed.

    Lemma transF_prev_1 :
      forall x xr i j,
        i < n ->
        j < i ->
        evalXQ x j [Vbool true] ->
        ( forall k, j < k < i -> evalXQ x k [Vbool false] ) ->
        transF' x xr ->
        evalXQ xr i [Vbool false].
    Proof.
      init. intros.
      induction i.

      (* 0th instance *)
      omega.

      (* (i+1)th instance *)
      assert (HH: j = i \/ j < i) by omega.
      destruct HH.

        (* j = i *)
      subst.

      inversion H3; subst; clear H3.

      assert (HH2: exists u, evalXQ xr i [u]).
        cut (exists v, evalXQ xr i v).
          intros [v Hv].
          assert (HH1: conform_clock (EE q) Iq v None i).
            assert (HH: M.In xr (CC q)).
              kind_attach xr (KK q).
              kind_case; kind_consistent.
            destruct HH as [ c HH ].
            assert (c = None).
              eapply trans_c with (p:=p); eauto.
            subst.
            program_trivial.
          inversion HH1; subst.
          eexists; eauto.

        eapply program_Pexistence; eauto.
        omega. kind_consistent.
      destruct HH2 as [xru HH2].

      eapply RVdef; eauto.
      eapply Rfby; eauto.
        eapply Rconst; eauto.
        eapply RPval; eauto.
          eapply Rdata3; eauto.
            eapply Rvar; eauto.
            eapply Rconst; eauto.
            eapply Rvar; eauto.
            constructor.

        (* j < i *)
      assert (HH1: forall k, j < k < i -> evalXQ x k [Vbool false]).
        intros. eapply H2. omega.
      assert (HH2: evalXQ x i [Vbool false]).
        intros. eapply H2. omega.
      clear H2.

      assert (HH3: i < n).
        omega.
      simpl'.

      inversion H3; subst; clear H3.

      eapply RVdef; eauto.
      eapply Rfby; eauto.
        eapply Rconst; eauto.
        eapply RPval; eauto.
          eapply Rdata3; eauto.
            eapply Rvar; eauto.
            eapply Rconst; eauto.
            eapply Rvar; eauto.
            constructor.
    Qed.

    Lemma trans_prev_0 :
      forall ep eq i j u,
        j <= i ->
        evalEP ep j [u] ->
        ( forall k, j < k <= i -> evalEP ep k Vbot ) ->
        ( forall k, k <= i -> PM_on_EE k ep eq /\ PM_keep_EE k ep eq) ->
        evalEQ eq i [u].
    Proof.
      intros.
      rename H into Hj.
      rename H0 into Hep1.
      rename H1 into Hep2.
      rename H2 into Hm.

      induction i.

      (* 0th instance *)
      assert (j = 0) by omega.
      subst.

      assert (HH: PM_on_EE 0 ep eq).
        eapply Hm; eauto.
      eapply HH; eauto.

      (* (i+1)th instance *)
      assert (HH: j = S i \/ j <= i) by omega.
      destruct HH.

        (* j = i + 1 *)
      subst.
      assert (HH: PM_on_EE (S i) ep eq).
        eapply Hm; eauto.
      eapply HH; eauto.

        (* j <= i *)
      assert (evalEQ eq i [u]).
        eapply IHi.
          assumption.
          intros; eapply Hep2; omega.
          intros; eapply Hm; omega.
          
      set (Hm (S i)). simpl'.
      eapply H2; eauto.
        eapply Hep2; eauto. omega.
    Qed.

    Theorem trans_0 :
      forall i j,
        i <= n ->
        j < i ->
        ( forall ep eq,
            well_typeP ep ->
            well_typeQ eq ->
            trans' ep eq ->
            PM_on_EE j ep eq /\ PM_keep_EE j ep eq ) /\
        ( forall x,
            M.In x (KK p) ->
            PM_on j x x ).
    Proof.
      init.
    
      induction i; intros.
      (* Case: n = 0 *)
      contradict H0. omega.
    
      (* Case: n = S i *)
      assert (HH: j = i \/ j < i) by omega.
      destruct HH; [ | subst; eapply IHi; eauto; omega ].
    
      subst. clear H0.
      assert (Hi: i < n) by omega.
      clear H.
    
      assert ( IHi' : forall j ep eq, j < i ->
                                      well_typeP ep ->
                                      well_typeQ eq ->
                                      trans' ep eq ->
                                      PM_on_EE j ep eq /\ PM_keep_EE j ep eq ).
        intros; eapply IHi; try assumption; omega.
      assert ( IHi'x : forall j x, j < i ->
                                   M.In x (KK p) ->
                                   PM_on j x x ).
        intros; eapply IHi; try assumption; omega.
      clear IHi.
    
      cut ( ( forall ep,
                nocyc_strong' ep ->
                forall eq,
                  well_typeP ep ->
                  well_typeQ eq ->
                  trans' ep eq ->
                  PM_on_EE i ep eq /\ PM_keep_EE i ep eq) /\
            ( forall x,
                nocyc_strongX' x ->
                ( PM_on i x x /\
                  ( forall j x' xc,
                      j <= i ->
                      M.MapsTo x (Some x') (CC p) ->
                      transC' (Some x') xc ->
                      PM_on j x' xc /\ PM_false j x' xc ) ) ) ).
        intuition;
        try solve [
          assert (nocyc_strong' ep);
            [ program_trivial | firstorder ]
        | assert (nocyc_strongX' x);
            [ program_trivial | firstorder ]
        ].
    
      apply CInocyc_strongX with
        ( P := fun ep _ => forall eq,
                             well_typeP ep ->
                             well_typeQ eq ->
                             trans' ep eq ->
                             PM_on_EE i ep eq /\ PM_keep_EE i ep eq )
        ( P0 := fun x _ => PM_on i x x /\
                           ( forall j x' xc,
                               j <= i ->
                               M.MapsTo x (Some x') (CC p) ->
                               transC' (Some x') xc ->
                               PM_on j x' xc /\ PM_false j x' xc ) )
        ( P1 := fun c _ => forall j xc x,
                             j <= i ->
                             transC' c xc ->
                             c = Some x ->
                             PM_on j x xc /\ PM_false j x xc ) ;
    
      intros;
    
      try match goal with
        [ H: trans _ _ _ _ |- _ ] => inversion H; subst; clear H
      end;
    
      repeat split; try discriminate; simpl';
    
      (* transC : passing properties *)
    
      try solve [
          map_trivial; apply H; auto
        | map_trivial; apply H0; auto ];
    
      (* PM_keep from transR *)
      try solve [ eapply transR_keep_2; eauto; inversion_WT; eauto; inversion_WT; eauto ];

      (* Edata1/2/3 *)
      try (
        match goal with
          | [ |- context [ Edata1 ] ] => idtac
          | [ |- context [ Edata2 ] ] => idtac
          | [ |- context [ Edata3 ] ] => idtac
        end;
    
        inversion_WT;

        try match goal with
          | [ |- context [ Edata2 ] ] =>
            repeat destruct H18 as [ HHH1 | H18 ];
            repeat destruct H30 as [ HHH2 | H30 ];
            try congruence
        end;
    
        solve [
          intros u HH;
          inversion HH; subst; clear HH;
    
          econstructor; eauto; instantiate; firstorder
    
        | intros j u Hj HH1 HH2;
          inversion HH1; subst; clear HH1;
          inversion HH2; subst; clear HH2;
    
          econstructor; eauto; instantiate; firstorder ] ).
    
      (* Evar *)
         (* PM_on *)
      unfold PM_on_EE; intros.
      inversion H4; subst.
      assert (evalXQ x i [u]) by (apply H; auto).

      eapply Rvar; eauto.

      { eapply transR_on; eauto.
        + destruct c as [ xb | ].
          - assert (evalXP xb i [Vbool true]).
              inversion H1.
              assert (HH: conform_clock' [u] (Some xb) i).
                program_trivial.
              inversion HH; assumption.
            eapply H0; eauto.
          - apply transC_none; auto.
        + eapply Rvar; eauto. }
    
      (* Econst *)
        (* PM_on *)
      unfold PM_on_EE; intros.
      inversion H2; subst.
      eapply Rconst; eauto.
    
        (* PM_keep (actually not possible) *)
      unfold PM_keep_EE; intros.
      inversion H4; subst.
      eapply Rconst; eauto.
    
      (* Ewhen, PM_on *)
      unfold PM_on_EE; intros.
      inversion H5; subst; clear H5.
      eapply Rvar; eauto.
    
      eapply transR_on; eauto;
      [ | apply H; inversion_WT; eauto ].
    
      inversion H2; subst; clear H2.
      eapply H1; eauto.
    
      (* Ecurr, PM_on *)
      unfold PM_on_EE; intros.
      inversion H5; subst; clear H5.
    
        (* clock = true *)
      eapply Rvar; eauto.
      eapply transR_on; eauto;
      [ | apply H; inversion_WT; eauto ].
    
      assert (HH: PM_on i x xc).
        eapply transC_on; eauto.
        intros; eapply H4; eauto.
      eapply HH; eauto.
    
        (* clock = false *)
      assert (HHp: forall j, j < i -> exists v, evalEP e j v).
        intros.
        eapply program_PexistenceE; eauto. omega.
        inversion_WT; eauto.
      destruct (prev_0 _ _ _ _ HHp).
    
          (* all previous values are Vbot *)
      assert (HH1: evalP' e i ui ui).
        eapply evalP_prev_0; eauto.
    
      assert (HH2: ui = u).
        eapply program_PdeterminismP with (p:=p); eauto.
      subst u.
    
      assert (HH3: forall j, j < i -> evalXQ xc j [Vbool false]).
        intros.
        inversion H2; subst.
    
        specialize (H5 j); simpl'.
        assert (HH4: conform_clock' Vbot (Some x) j).
          rewrite <- H18.
          program_trivial.
        inversion HH4; subst.
    
            (* x -> [false] *)
        eapply transC_on; eauto.
        eapply IHi'x; eauto.
          inversion n1; kind_consistent.
          intros; eapply H4; eauto; omega.
    
            (* x -> Vbot *)
        eapply transC_false; eauto.
          omega.
          eapply IHi'x; eauto.
            inversion n1; kind_consistent.
            intros; eapply H4; eauto; omega.
    
      assert (HH4: forall j, j <= i -> evalXQ xc j [Vbool false]).
        intros.
        assert (HH5: j < i \/ j = i).
          omega.
        destruct HH5 ; [ auto | ].
        subst.
        assert (HH6: PM_on i x xc).
          eapply transC_on; eauto.
          intros. eapply H4; eauto.
        eapply HH6; eauto.
    
      assert (clockof eq0 = None).
        eapply transR_clockof; eauto.
    
      eapply Rvar; eauto.
      apply transR_prev_0 with (e:=eq0) (xc:=xc); eauto.
    
          (* exists one of previous values that is not Vbot *)
    
      destruct H5 as [j [u' [ Hj [ He1 He2 ] ] ] ].
    
      assert (HH1: evalP' e i ui u').
        eapply evalP_prev_1; eauto.
    
      assert (HH2: u' = u).
        eapply program_PdeterminismP with (p:=p); eauto.
      subst u'. simpl'.
    
      assert (HH3: evalXQ xc j [Vbool true]).
        eapply transC_on; eauto.
          intros; eapply IHi'x; eauto.
            inversion n1; kind_consistent.
          intros; eapply H4; eauto. omega.
    
        assert (HH4: conform_clock' [u] (Some x) j).
          inversion H2; subst.
          rewrite <- H14.
          program_trivial.
        inversion HH4; subst.
    
        assumption.
    
      assert (HH4: evalEQ eq0 j [u]).
        cut (PM_on_EE j e eq0).
          intro HHH; eapply HHH; eauto.
        eapply IHi'; eauto.
        inversion_WT; eauto.
    
      assert (HH5: forall k, j < k < i -> evalXQ xc k [Vbool false]).
        intros.
        specialize (He2 k). simpl'.
    
        assert (HH6: conform_clock' Vbot (Some x) k).
          inversion H2; subst.
          rewrite <- H18.
          program_trivial.
        inversion HH6; subst.
    
            (* x -> [false] *)
        eapply transC_on; eauto.
        eapply IHi'x; eauto.
          inversion n1; kind_consistent.
          intros; eapply H4; eauto; omega.
    
            (* x -> Vbot *)
        eapply transC_false; eauto.
          omega.
          eapply IHi'x; eauto.
            inversion n1; kind_consistent.
            intros; eapply H4; eauto; omega.
    
      assert (HH6: forall k, j < k <= i -> evalXQ xc k [Vbool false]).
        intros.
        assert (HH7: j < k < i \/ k = i).
          omega.
        destruct HH7; [ auto | ].
    
        subst.
        assert (HH8: PM_on i x xc).
          eapply transC_on; eauto.
          intros. eapply H4; eauto.
        eapply HH8; eauto.
    
      assert (clockof eq0 = None).
        eapply transR_clockof; eauto.
        inversion_WT; eauto.
    
      eapply Rvar; eauto.
      eapply transR_prev_1 with (e:=eq0) (xc:=xc) (j:=j); eauto; omega.
    
      (* Ecurr, PM_keep *)
      unfold PM_keep_EE; intros. subst.
      inversion H6; subst; clear H6.
      eapply Rvar; eauto.
      eapply transR_keep; eauto;
      [ | inversion H7; assumption ].
    
      assert (HH: PM_false (S j) x xc).
        eapply transC_false; eauto.
      apply HH; eauto.
    
      (* Efby, PM_on *)
      unfold PM_on_EE; intros.
      inversion H3; subst; clear H3.
    
      assert (HHp: forall j, j < i -> exists v, evalEP eb j v).
        intros.
        eapply program_PexistenceE; eauto. omega.
        inversion_WT; eauto.
      destruct (prev_0 _ _ _ _ HHp).
    
          (* all previous values are Vbot (the first instance of the clock) *)
      assert (HH1: evalP' eb i ui0 ui0).
        eapply evalP_prev_0; eauto.
    
      assert (HH2: ui0 = u).
        eapply program_PdeterminismP with (p:=p); eauto.
      subst u. simpl'.
    
      assert (HH3: forall j, j < i -> evalXQ xc j [Vbool false]).
        intros.
    
        specialize (H3 j); simpl'.
        assert (HH4: conform_clock' Vbot c j).
          inversion H1; subst.
          rewrite <- H20.
          program_trivial.
        inversion HH4; subst.
    
            (* clock -> [false] *)
        assert (HH5: PM_on j x xc).
          eapply H0; eauto. omega.
        eapply HH5; eauto.
    
            (* clock -> Vbot *)
        assert (HH5: PM_false j x xc).
          eapply H0; eauto. omega.
        eapply HH5; eauto.
    
      assert (HH4: evalXQ xf i [Vbool true]).
        eapply transF_prev_0; eauto.
    
      assert (HH5: evalXQ xc i [Vbool true]).
        assert (HH6: conform_clock' [ui0] c i).
          inversion H1; subst.
          program_trivial.
        inversion HH6; subst.
    
            (* c = none *)
        eapply transC_none; eauto.
    
            (* c = Some x *)
        eapply H0; eauto.
    
      set (e := Efby (Econst ui t None) ebq t None) in *.
      assert (HH11: exists u, evalEQ e i [u]).
        assert (HH9: well_typeQ e).
          eapply transR_well_type in H11; inversion H11; assumption.
    
        cut (exists v, evalEQ e i v).
          intros [v HH8].
          assert (HH10: conform_clock (EE q) Iq v None i).
            inversion HH9.
            eapply program_Pgood_val_cE with (e:=e); eauto.
          inversion HH10. subst; eauto.
    
        program_trivial.
      destruct HH11 as [ ue HH11 ].
    
      eapply Rvar; eauto.
      eapply transR_on; eauto.
      eapply Rdata3; eauto.
        eapply Rvar; eauto.
    
        assert (HH6: PM_on_EE i ea eaq).
          eapply H; eauto.
          inversion H1; assumption.
          apply transR_well_type in H11; inversion H11; assumption.
        eapply HH6; eauto.
    
        constructor.
    
          (* exists a previous value that is not Vbot
              (not the first instance of the clock)   *)
    
      destruct H3 as [j [ ub [ Hj [ Heb1 Heb2 ] ] ] ].
      
      assert (HH10: evalP' eb i ui0 ub).
        eapply evalP_prev_1; eauto.
    
      assert (HH12: u = ub).
        eapply program_PdeterminismP with (p:=p); eauto.
        
      subst u. simpl'.
    
      assert (HH1: evalXQ xc j [Vbool true]).
        assert (HH4: conform_clock' [ub] c j).
          inversion H1; subst.
          rewrite <- H18.
          program_trivial.
        inversion HH4; subst.
    
            (* clock = None *)
        eapply transC_none; eauto.
    
            (* clock = Some x *)
        eapply H0; eauto. omega.
    
      assert (HH3: forall k, j < k < i -> evalXQ xc k [Vbool false]).
        intros.
    
        specialize (Heb2 k); simpl'.
        assert (HH4: conform_clock' Vbot c k).
          inversion H1; subst.
          rewrite <- H20.
          program_trivial.
        inversion HH4; subst.
    
            (* clock -> [false] *)
        assert (HH5: PM_on k x xc).
          eapply H0; eauto. omega.
        eapply HH5; eauto.
    
            (* clock -> Vbot *)
        assert (HH5: PM_false k x xc).
          eapply H0; eauto. omega.
        eapply HH5; eauto.
    
      assert (HH4: evalXQ xf i [Vbool false]).
        eapply transF_prev_1; eauto.
    
      assert (HH5: evalXQ xc i [Vbool true]).
        assert (HH6: conform_clock' [ui0] c i).
          inversion H1; subst.
          program_trivial.
        inversion HH6; subst.
    
            (* c = None *)
        eapply transC_none; eauto.
    
            (* c = Some x *)
        eapply H0; eauto.
    
      assert (HH11: evalEQ eaq i [ui0]).
        assert (HH9: well_typeQ eaq).
          eapply transR_well_type in H11; inversion H11; assumption.
    
        assert (HH8: PM_on_EE i ea eaq).
          apply H; auto.
          inversion_WT; eauto.
    
        eapply HH8; eauto.
    
      assert (HH9: exists i', S i' = i).
        exists (pred i). omega.
      destruct HH9 as [i' HH9]. subst i.
    
      assert (HH13: forall k, j < k <= i' -> evalEP eb k Vbot).
        intros.
        eapply Heb2; eauto.
        omega.
    
      assert (HH14: forall k, k <= i' -> PM_on_EE k eb ebq /\ PM_keep_EE k eb ebq).
        intros.
        eapply IHi'; eauto; try omega; inversion_WT; eauto.
        eapply transR_well_type in H11; inversion H11. inversion H17; assumption.
        assumption.
    
      assert (HH15: evalEQ ebq i' [ub]).
        eapply trans_prev_0 with (j:=j) (i:=i'); eauto.
        omega.
    
      eapply Rvar; eauto.
      eapply transR_on; eauto.
      eapply Rdata3; eauto.
        eapply Rvar; eauto.
        eapply Rfby; eauto.
          eapply Rconst; eauto.
          eapply RPval; eauto.
          constructor.
    
      (* transX *)
    
        (* input *)
          (* PM_on *)
      eapply inp_PM_on; eauto.
    
        (* output *)
          (* PM_on *)
      assert (HH: M.In x (EE q)).
        assert (M.MapsTo x Kout (KK q) \/ M.MapsTo x Kloc (KK q)).
          kind_attach x (KK p).
          kind_case; [ left | right ];
          eapply trans_k; eauto.
        kind_consistent.
      destruct HH as [ eq HH ].
    
      assert (well_typeP e).
        destructP; eauto.
    
      assert (well_typeQ eq).
        destructP; eauto.
    
      assert (trans' e eq).
        eapply trans_e; eauto.
    
      unfold PM_on; intros.
      eapply RVdef; eauto.
      inversion H4; [ kind_attach x (KK p); kind_case; map_trivial
                    | subst; clear H4; map_trivial ].
      apply H; try assumption.
    
      (* transC *)
    
        (* PM_on *)
      subst x0. eapply transC_on; eauto;
      [ | intros; eapply H3; eauto ].
    
      assert (HH: j = i \/ j < i) by omega.
      destruct HH.
    
          (* j = i *)
      subst; assumption.
    
          (* j < i *)
      eapply IHi'x; eauto.
      inversion n0; kind_consistent.
    
        (* PM_false *)
      subst x0. eapply transC_false; eauto;
      [ omega | ].
    
      assert (HH: j = i \/ j < i) by omega.
      destruct HH.
    
          (* j = i *)
      subst; assumption.
    
          (* j < i *)
      eapply IHi'x; eauto.
      inversion n0; kind_consistent.
    Qed.
  End PROOF.

  Theorem T0 :
    forall (p: Program) (WF: WellFormed p) q n i x u Ip Iq,
      ValidInput p n Ip ->
      RF.refining (TT p) Ip Iq ->
      T.translate p WF = q ->
      i < n ->
      evalX (EE p) Ip x i [u] ->
      evalX (EE q) Iq x i [u].
  Proof.
    intros.
    assert (HH: PM_on p Ip Iq WF i x x).
      eapply trans_0; eauto.
      eapply program_eval_in; eauto.
    subst. eapply HH; eauto.
  Qed.

  Theorem T1 :
    forall p q n Ip Iq Op Oq,
    forall WF: WellFormed p,
      T.translate p WF = q ->
      ValidInput p n Ip ->
      ProgramEval p n Ip Op ->
      ProgramEval q n Iq Oq ->
      RF.refining (TT p) Ip Iq ->
      RF.refining (TT p) Op Oq.
  Proof.
    intros.

    assert (HH1: WellFormed q).
      eapply T.GoodProperties; eauto.
    
    assert (HH2: ValidInput q n Iq).
      eapply T2; eauto.
    
    assert (HH3: ValidOutput q n Iq Oq).
      eapply program_valid; eauto.

    constructor.
    + intro.

      destruct H1.
      destruct H2. rename p0 into q.
      rewrite <- H1.
      rewrite <- H2.

      rewrite T.trans_o.
      subst q. reflexivity.

    + intros ? ? ? ? ?.

      destruct H1.
      destruct H2. rename p0 into q.
      erewrite H6; eauto.
      erewrite H8; eauto.

    + intro. intros.

      assert (i < n).
        assert (length sp = n).
          destruct H1; eauto.

        subst n.

        eapply list_nth_some'; eauto.

      eapply program_out_nth with (x:=x) (p:=q); eauto.
      - destruct H1.
        eapply H9 in H6; eauto.

        eapply T0 with (p:=p); eauto.

    + intro. intros.

      assert (M.MapsTo x t (TT q)).
        assert (HH5: M.MapsTo x Kout (KK q)).
          destruct H2. apply H2. eauto.

        assert (HH6: M.MapsTo x Kout (KK p)).
          subst q.
          apply T.trans_o in HH5; auto.

        assert (HH7: M.In x (TT q)).
          kind_consistent.
        destruct HH7 as [ t' HH7 ].

        assert (t = t').
          subst q.
          eapply T.trans_t; eauto.

        congruence.

      destruct HH3.
      eapply VOgood_io_val_t; eauto.

    + intro. intros.

      assert (M.MapsTo x None (CC q)).
        assert (M.In x (KK q)).
          assert (M.MapsTo x Kout (KK q)).
            destruct H2. apply H2. eauto.
          eauto.
        assert (HH: M.In x (CC q)).
          kind_consistent.
        destruct HH as [ c HH ].
        assert (c = None).
          subst q. eapply T.trans_c; eauto.
        subst c; assumption.

      destruct HH3.
      unfold Pgood_io_val_c in *.
      eapply VOgood_io_val_c with (x:=x) (i:=i) (s:=s) (c:=None) in H6; eauto.

      inversion H6; subst.
      exists u. eauto.
  Qed.
End TranslationProof.
