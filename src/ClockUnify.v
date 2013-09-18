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
Require Import List.

(** This file gives the specification of the clock-unifying transformation, and
    gives the semantics preserving goal. *)

(** [transC] corresponds to the meta-function B in the paper, and [trans]
corresponds to the meta-function Z in the paper. *)

Inductive transF (p q: Program) : ident -> ident -> Prop :=
  | EFdef : forall x xf,
              M.MapsTo xf (Efby (Econst (Vbool true) Tbool None)
                                (Edata3 Oif
                                        (Evar x Tbool None)
                                        (Econst (Vbool false) Tbool None)
                                        (Evar xf Tbool None)
                                        Tbool
                                        None)
                                Tbool
                                None) (EE q) ->
              transF p q x xf.

Inductive transR (p q: Program) : expr -> ident -> val -> ident -> Prop :=
  | ERfix: forall eq xc ui xr,
             M.MapsTo xr (Edata3 Oif
                                 (Evar xc Tbool None)
                                 eq
                                 (Efby
                                    (Econst ui (typeof eq) None)
                                    (Evar xr (typeof eq) None)
                                    (typeof eq)
                                    None)
                                 (typeof eq)
                                 None ) (EE q) ->
             transR p q eq xc ui xr.

Inductive transC (p q: Program) : clock -> ident -> Prop :=
  | ECglobal : forall x,
                 M.MapsTo x (Econst (Vbool true) Tbool None) (EE q) ->
                 transC p q None x

  | ECnested : forall x xc xc' c,
                 M.MapsTo x c (CC p) ->
                 transC p q c xc ->
                 M.MapsTo xc' (Edata3 Oif
                                      (Evar xc Tbool None)
                                      (Evar x Tbool None)
                                      (Econst (Vbool false) Tbool None)
                                      Tbool
                                      None ) (EE q) ->
                 transC p q (Some x) xc'.

Inductive trans (p q: Program) : expr -> expr -> Prop :=
  | TRvar : forall x xc ui xr t c,
              transR p q (Evar x t None) xc ui xr ->
              transC p q c xc ->
              trans p q (Evar x t c) (Evar xr t None)

  | TRconst : forall u t c,
                trans p q (Econst u t c) (Econst u t None)

  | TRwhen : forall ep eq x t c xc xr ui,
               trans p q ep eq ->
               transR p q eq xc ui xr ->
               transC p q c xc ->
               trans p q (Ewhen ep x t c) (Evar xr t None)

  | TRcurr : forall ep eq x t c ui xc xr,
               trans p q ep eq ->
               transR p q eq xc ui xr ->
               transC p q (Some x) xc ->
               trans p q (Ecurr ep x ui t c) (Evar xr t None)

  | TRfby : forall eap eaq ebp ebq xc xf xr t c ui,
              trans p q eap eaq ->
              trans p q ebp ebq ->
              transR p q (Edata3 Oif
                                 (Evar xf Tbool None)
                                 eaq
                                 (Efby (Econst ui t None)
                                       ebq
                                       t
                                       None)
                                 t
                                 None) xc ui xr ->
              transC p q c xc ->
              transF p q xc xf ->
              trans p q (Efby eap ebp t c) (Evar xr t None)

  | TRdata1 : forall eap eaq o t c,
                trans p q eap eaq ->
                trans p q (Edata1 o eap t c) (Edata1 o eaq t None)

  | TRdata2 : forall eap eaq ebp ebq o t c,
                trans p q eap eaq ->
                trans p q ebp ebq ->
                trans p q (Edata2 o eap ebp t c) (Edata2 o eaq ebq t None)

  | TRdata3 : forall eap eaq ebp ebq ecp ecq o t c,
                trans p q eap eaq ->
                trans p q ebp ebq ->
                trans p q ecp ecq ->
                trans p q (Edata3 o eap ebp ecp t c) (Edata3 o eaq ebq ecq t None)
  .

Inductive global_clock_expr : expr -> Prop :=
  | GCvar :
      forall x t c,
        c = None ->
        global_clock_expr (Evar x t c)

  | GCconst :
      forall u t c,
        c = None ->
        global_clock_expr (Econst u t c)

  | GCfby :
      forall ea eb t c,
        global_clock_expr ea ->
        global_clock_expr eb ->
        c = None ->
        global_clock_expr (Efby ea eb t c)

  | GCdata1 :
      forall o ea t c,
        global_clock_expr ea ->
        c = None ->
        global_clock_expr (Edata1 o ea t c)

  | GCdata2 :
      forall o ea eb t c,
        global_clock_expr ea ->
        global_clock_expr eb ->
        c = None ->
        global_clock_expr (Edata2 o ea eb t c)

  | GCdata3 :
      forall o ea eb ec t c,
        global_clock_expr ea ->
        global_clock_expr eb ->
        global_clock_expr ec ->
        c = None ->
        global_clock_expr (Edata3 o ea eb ec t c)
  .

Hint Constructors trans transC transR transF global_clock_expr : constr.

Lemma trans_type :
  forall p q ep eq,
    trans p q ep eq ->
    typeof ep = typeof eq.
Proof.
  intros. induction H; eauto.
Qed.

Lemma trans_clock :
  forall p q ep eq,
    trans p q ep eq ->
    clockof eq = None.
Proof.
  intros.
  inversion H; subst; eauto.
Qed.

Lemma trans_gc_expr :
  forall p q ep eq,
    trans p q ep eq ->
    global_clock_expr eq.
Proof.
  intros. induction H; eauto with constr.
Qed.

Lemma transR_well_type :
  forall p q eq xc xr ui,
    WellFormed q ->
    transR p q eq xc xr ui ->
    well_type (TT q) (CC q) eq.
Proof.
  intros.
  inversion H0; subst.

  destructP. apply WFwell_type in H1.
  inversion H1. assumption.
Qed.

Hint Resolve trans_type trans_clock transR_well_type.

Lemma transR_clockof :
  forall p q eq xc xr ui,
    WellFormed q ->
    transR p q eq xc xr ui ->
    clockof eq = None.
Proof.
  intros.
  inversion H0; subst.

  destructP. apply WFwell_type in H1.
  inversion H1. congruence.
Qed.

Module Type Translation.

(** [translate] must take a [WellFormed p] as an argument, otherwise it is not
    guaranteed to finish *)

  Parameter translate :
    forall p: Program,
      WellFormed p ->
      Program.

  Axiom trans_k :
    forall p WF x k,
      M.MapsTo x k (KK p) ->
      M.MapsTo x k (KK (translate p WF)).

  Axiom trans_i :
    forall p WF x,
      M.MapsTo x Kin (KK p) <->
      M.MapsTo x Kin (KK (translate p WF)).

  Axiom trans_o :
    forall p WF x,
      M.MapsTo x Kout (KK p) <->
      M.MapsTo x Kout (KK (translate p WF)).

  Axiom trans_t :
    forall p WF x tp tq,
      M.MapsTo x tp (TT p) ->
      M.MapsTo x tq (TT (translate p WF)) ->
      tp = tq.

  Axiom trans_c :
    forall p WF x c,
      M.MapsTo x c (CC (translate p WF)) ->
      c = None.

  Axiom trans_e :
    forall p WF x ep eq,
      M.MapsTo x ep (EE p) ->
      M.MapsTo x eq (EE (translate p WF)) ->
      trans p (translate p WF) ep eq.

  Axiom GoodProperties :
    forall p WF q,
      translate p WF = q ->
      WellFormed q.

  Axiom GlobalClockExpressions :
    forall p WF x e,
      M.MapsTo x e (EE (translate p WF)) ->
      global_clock_expr e.
End Translation.

Module Refinement.
  Definition Pgood_io_val_c' (IO: Eio) :=
    forall x s v i,
      M.MapsTo x s IO ->
      nth_error s i = Some v ->
      exists u, v = [u].

  Definition PM_keys (Ip Iq: Eio) :=
    forall x, M.In x Ip <-> M.In x Iq.

  Definition PM_lens (Ip Iq: Eio) :=
    forall x sp sq, M.MapsTo x sp Ip -> M.MapsTo x sq Iq -> length sp = length sq.

  Definition PM_on (Ip Iq: Eio) :=
    forall x sp sq i u,
      M.MapsTo x sp Ip ->
      M.MapsTo x sq Iq ->
      nth_error sp i = Some [u] ->
      nth_error sq i = Some [u].

  Record refining (Tp: Etyp) (Ip Iq: Eio) :=
    mkMatchInp {
      RF_keys: PM_keys Ip Iq;
      RF_lens: PM_lens Ip Iq;
      RF_on: PM_on Ip Iq;
      RFgood_inp_val_t: Pgood_io_val_t Tp Iq;
      RFgood_inp_val_c': Pgood_io_val_c' Iq
    }.

  Lemma RF_1 :
    forall p q Ip Iq n,
      ValidInput p n Ip ->
      refining (TT p) Ip Iq ->
      (forall x, M.MapsTo x Kin (KK p) <-> M.MapsTo x Kin (KK q) ) ->
      PconsistentI (KK q) Iq.
  Proof.
    intros.
    assert (PconsistentI (KK p) Ip).
      destructP. eauto.
    assert (PM_keys Ip Iq).
      inversion H0. eauto.
    unfold PconsistentI in *.
    unfold PM_keys in *.
    intros.
    rewrite <- H3. rewrite <- H1. rewrite <- H2.
    intuition.
  Qed.

  Theorem RF_0 :
    forall p Ip q Iq n,
      WellFormed p ->
      ValidInput p n Ip ->
      refining (TT p) Ip Iq ->
      (forall x, M.MapsTo x Kin (KK p) <-> M.MapsTo x Kin (KK q) ) ->
      (forall x tp tq, M.MapsTo x tp (TT p) -> M.MapsTo x tq (TT q) -> tp = tq ) ->
      (forall x c, M.MapsTo x c (CC q) -> c = None ) ->
      ValidInput q n Iq.
  Proof.
    intros. constructor.
  
    (* PconsistentI *)
    + eapply RF_1; eauto.
  
    (* Pinp_long Iq n *)
    + assert (PM_lens Ip Iq).
        inversion H1. assumption.
      unfold PM_lens in *.
  
      assert (Pinp_long Ip n).
        inversion H0. assumption.
      unfold Pinp_long in *.
  
      intros x sq. intros.
  
      assert (HH: exists sp, M.MapsTo x sp Ip).
        change (M.In x Ip).
        assert (HH2: PM_keys Ip Iq).
          inversion H1; assumption.
        eapply HH2.
        eauto.
      destruct HH as [sp HH].
      
      specialize (H6 x sp).
      specialize (H5 x sp sq).
      simpl'.
      intuition.

    (* Pgood_io_val_t *)
    + assert (Pgood_io_val_t (TT p) Iq).
      inversion H1; assumption.
  
      unfold Pgood_io_val_t in *.
      intros x s tq u i. intros.
    
      assert (M.In x (TT p)).
        assert (M.MapsTo x Kin (KK q)).
          assert (PconsistentI (KK q) Iq).
            eapply RF_1; eauto.
          kind_consistent.
        assert (M.MapsTo x Kin (KK p)) by (rewrite H2; auto).
        kind_consistent.
      destruct H9 as [tp H9].
    
      specialize (H3 x tp tq).
      simpl'. subst.
    
      eauto.
    
      (* Pgood_io_val_c' *)
    + assert (Pgood_io_val_c' Iq).
        inversion H1. assumption.
      unfold Pgood_io_val_c' in *.
    
      unfold Pgood_io_val_c. intros.
      specialize (H4 x c).
      specialize (H5 x s v i).
      simpl'. map_trivial.
      destruct H5 as [u H5]. subst.
    
      eapply CCIdefault.
  Qed.

End Refinement.

Module Type TranslationFacts ( T : Translation ).
  Import Refinement.

  Axiom T2 :
    forall p q n Ip Iq,
    forall WF: WellFormed p,
      T.translate p WF = q ->
      ValidInput p n Ip ->
      refining (TT p) Ip Iq ->
      ValidInput q n Iq.

  Axiom T1 :
    forall p q n Ip Iq Op Oq,
    forall WF: WellFormed p,
      T.translate p WF = q ->
      ValidInput p n Ip ->
      ProgramEval p n Ip Op ->
      ProgramEval q n Iq Oq ->
      refining (TT p) Ip Iq ->
      refining (TT p) Op Oq.

  Axiom T0 :
    forall (p: Program) (WF: WellFormed p) q n i x u Ip Iq,
      ValidInput p n Ip ->
      refining (TT p) Ip Iq ->
      T.translate p WF = q ->
      i < n ->
      evalX (EE p) Ip x i [u] ->
      evalX (EE q) Iq x i [u].
End TranslationFacts.
