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


Require Import Arith ZArith BinPos.
Require Import FMapPositive FMapFacts Structures.OrderedTypeEx.
Require Import Common.

(** A formal framework for the SL language *)


(** * Syntax *)
Definition ident := Pos.t.
Definition time := nat.
Definition clock := option ident.

Inductive kind :=
  | Kin
  | Kloc
  | Kout
  .

Inductive val :=
  | Vbool (vb:bool)
  | Vz (vz:Z)
  .

Inductive val' :=
  | V (vv:val)
  | Vbot
  .

Inductive type :=
  | Tbool
  | Tz
  .

Inductive operator :=
  | Oplus
  | Oopp
  | Ominus
  | Omul
  | Odiv
  | Omod

  | Ole
  | Olt
  | Oge
  | Ogt

  | Oeq
  | One

  | Onot
  | Oand
  | Oor

  | Oif
  .

Inductive expr :=
  | Evar (x:ident) (t:type) (c:clock)
  | Econst (u:val) (t:type) (c:clock)
  | Ewhen (e:expr) (x:ident) (t:type) (c:clock)
  | Ecurr (e:expr) (x:ident) (u:val) (t:type) (c:clock)
  | Efby (ea:expr) (eb:expr) (t:type) (c:clock)
  | Edata1 (o:operator) (ea:expr) (t:type) (c:clock)
  | Edata2 (o:operator) (ea eb:expr) (t:type) (c:clock)
  | Edata3 (o:operator) (ea eb ec:expr) (t:type) (c:clock)
  .

Definition typeof (e:expr) :=
  match e with
    | Evar _ t _ => t
    | Econst _ t _ => t
    | Ewhen _ _ t _ => t
    | Ecurr _ _ _ t _ => t
    | Efby _ _ t _ => t
    | Edata1 _ _ t _ => t
    | Edata2 _ _ _ t _ => t
    | Edata3 _ _ _ _ t _ => t
  end.

Definition clockof (e:expr) :=
  match e with
    | Evar _ _ c => c
    | Econst _ _ c => c
    | Ewhen _ _ _ c => c
    | Ecurr _ _ _ _ c => c
    | Efby _ _ _ c => c
    | Edata1 _ _ _ c => c
    | Edata2 _ _ _ _ c => c
    | Edata3 _ _ _ _ _ c => c
  end.

Lemma val_eq : forall (x y:val), V x = V y -> x = y.
Proof.
  congruence.
Qed.

Hint Resolve val_eq.

Notation "[ x ]" := (V x).

Ltac val_inj :=
  repeat match goal with
    | [ H: Vbool _ = Vbool _ |- _ ] => injection H; intro; subst; clear H
  end.



(** * Types for a program / environments *)
Definition Eknd := M.t kind.
Definition Etyp := M.t type.
Definition Eclk := M.t clock.
Definition Eeqs := M.t expr.
Definition Eio := M.t (list val').

Record Program := mkProgram {
  KK : Eknd;
  TT : Etyp;
  CC : Eclk;
  EE : Eeqs
}.

Definition emptyP :=
  {| KK := M.empty _;
     TT := M.empty _;
     CC := M.empty _;
     EE := M.empty _ |}.


(** * Dynamic semantics

    Note that [Z.div] conforms well to our setting that division by zero
    results in a zero.
*)
Inductive evalD1 : operator -> val -> val -> Prop :=
  | EDneg : forall z, evalD1 Oopp (Vz z) (Vz (Z.opp z))
  | EDnot : forall b, evalD1 Onot (Vbool b) (Vbool (negb b)).

Inductive evalD2 : operator -> val -> val -> val -> Prop :=
  | EDplus  : forall a b, evalD2 Oplus  (Vz a) (Vz b) (Vz (Z.add    a b))
  | EDminus : forall a b, evalD2 Ominus (Vz a) (Vz b) (Vz (Z.sub    a b))
  | EDmul   : forall a b, evalD2 Omul   (Vz a) (Vz b) (Vz (Z.mul    a b))
  | EDdiv   : forall a b, evalD2 Odiv   (Vz a) (Vz b) (Vz (Z.div    a b))
  | EDmod   : forall a b, evalD2 Omod   (Vz a) (Vz b) (Vz (Z.modulo a b))

  | EDle : forall a b, evalD2 Ole (Vz a) (Vz b) (Vbool (Z.leb a b))
  | EDlt : forall a b, evalD2 Olt (Vz a) (Vz b) (Vbool (Z.ltb a b))
  | EDge : forall a b, evalD2 Oge (Vz a) (Vz b) (Vbool (Z.geb a b))
  | EDgt : forall a b, evalD2 Ogt (Vz a) (Vz b) (Vbool (Z.gtb a b))

  | EDeqZ : forall a b, evalD2 Oeq (Vz a) (Vz b) (Vbool (Z.eqb a b))
  | EDneZ : forall a b, evalD2 One (Vz a) (Vz b) (Vbool (negb (Z.eqb a b)))
                     
  | EDeqB : forall a b, evalD2 Oeq (Vbool a) (Vbool b) (Vbool (eqb a b))
  | EDneB : forall a b, evalD2 One (Vbool a) (Vbool b) (Vbool (negb (eqb a b)))
                     
  | EDand : forall a b, evalD2 Oand (Vbool a) (Vbool b) (Vbool (andb a b))
  | EDor  : forall a b, evalD2 Oor  (Vbool a) (Vbool b) (Vbool (orb  a b)).

Inductive evalD3 : operator -> val -> val -> val -> val -> Prop :=
  | EDifT : forall ua ub, evalD3 Oif (Vbool true)  ua ub ua
  | EDifF : forall ua ub, evalD3 Oif (Vbool false) ua ub ub.



Section WithEnvs.
  Variables E : Eeqs.
  Variables I : Eio.

  Inductive eval : expr -> time -> val' -> Prop :=
    | Rvar : forall x t c i v,
               evalX x i v ->
               eval (Evar x t c) i v

    | Rconst : forall u t c i,
                 eval (Econst u t c) i [u]

    | RwhenT : forall e x t c i u,
                 eval e i [u] ->
                 evalX x i [Vbool true] ->
                 eval (Ewhen e x t c) i [u]

    | RwhenF : forall e x t c i u,
                 eval e i [u] ->
                 evalX x i [Vbool false] ->
                 eval (Ewhen e x t c) i Vbot

    | RwhenB : forall e x t c i,
                 eval e i Vbot ->
                 evalX x i Vbot ->
                 eval (Ewhen e x t c) i Vbot

    | RcurrT : forall e x ui t c i u,
                 eval e i [u] ->
                 evalX x i [Vbool true] ->
                 eval (Ecurr e x ui t c) i [u]

    | RcurrF : forall e x ui t c i u,
                 evalP e i ui u ->
                 evalX x i [Vbool false] ->
                 eval (Ecurr e x ui t c) i [u]

    | RcurrB : forall e x ui t c i,
                 eval e i Vbot ->
                 evalX x i Vbot ->
                 eval (Ecurr e x ui t c) i Vbot

    | Rfby : forall ea eb t c i ui u,
               eval ea i [ui] ->
               evalP eb i ui u ->
               eval (Efby ea eb t c) i [u]

    | RfbyB : forall ea eb t c i,
                eval ea i Vbot ->
                eval (Efby ea eb t c) i Vbot

    | Rdata1 : forall o e t c i ua u,
                 eval e i [ua] ->
                 evalD1 o ua u ->
                 eval (Edata1 o e t c) i [u]

    | Rdata1B : forall o e t c i,
                  eval e i Vbot ->
                  eval (Edata1 o e t c) i Vbot

    | Rdata2 : forall o ea eb t c i ua ub u,
                 eval ea i [ua] ->
                 eval eb i [ub] ->
                 evalD2 o ua ub u ->
                 eval (Edata2 o ea eb t c) i [u]

    | Rdata2B : forall o ea eb t c i,
                  eval ea i Vbot ->
                  eval eb i Vbot ->
                  eval (Edata2 o ea eb t c) i Vbot

    | Rdata3 : forall o ea eb ec t c i ua ub uc u,
                 eval ea i [ua] ->
                 eval eb i [ub] ->
                 eval ec i [uc] ->
                 evalD3 o ua ub uc u ->
                 eval (Edata3 o ea eb ec t c) i [u]

    | Rdata3B : forall o ea eb ec t c i,
                  eval ea i Vbot ->
                  eval eb i Vbot ->
                  eval ec i Vbot ->
                  eval (Edata3 o ea eb ec t c) i Vbot

  with evalX : ident -> time -> val' -> Prop :=
    | RVin : forall x i s v,
               M.MapsTo x s I ->
               nth_error s i = Some v ->
               evalX x i v
    
    | RVdef : forall x i e v,
                M.MapsTo x e E ->
                eval e i v ->
                evalX x i v

  with evalP : expr -> time -> val -> val -> Prop :=
    | RPinit : forall e ui,
                 evalP e O ui ui
    
    | RPval : forall e i ui u,
                eval e i [u] ->
                evalP e (S i) ui u
    
    | RPpull : forall e i ui u,
                 eval e i Vbot ->
                 evalP e i ui u ->
                 evalP e (S i) ui u
    .

  Scheme Ieval := Induction for eval Sort Prop
    with IevalX := Induction for evalX Sort Prop
    with IevalP := Induction for evalP Sort Prop.
  
  Combined Scheme CIevalX from Ieval, IevalX.
  Combined Scheme CIevalXP from IevalX, IevalP.
  Combined Scheme CIevalEXP from Ieval, IevalX, IevalP.

End WithEnvs.

Hint Constructors eval evalX evalP : constr.

Inductive ProgramEval : Program -> nat -> Eio -> Eio -> Prop :=
  | WPintro :
      forall p n I O,
        ( forall x, M.MapsTo x Kout (KK p) <-> M.In x O ) ->
        ( forall x s, M.MapsTo x s O -> length s = n ) ->
        ( forall x s i v,
            M.MapsTo x s O ->
            nth_error s i = Some v ->
            evalX (EE p) I x i v ) ->
        ProgramEval p n I O.

(** * Soundness and other properties of the defined semantics *)
Section Properties.
  Variable K : Eknd.
  Variable T : Etyp.
  Variable C : Eclk.
  Variable E : Eeqs.
  Variable I : Eio.
  Variable J : Eio. (* output; 'O' is used by nat, so we use 'J' *)
  
  (** ** Various inductive judgements to describe properties of a program *)
  Inductive well_type_val : val -> type -> Prop :=
    | WC_bool : forall u, well_type_val (Vbool u) Tbool
    | WC_z : forall u, well_type_val (Vz u) Tz
    .

  Inductive conform_clock : val' -> clock -> time -> Prop :=
    | CCdefault : forall u i,
                    conform_clock [u] None i
  
    | CCtrue : forall u x i,
                 evalX E I x i [Vbool true] ->
                 conform_clock [u] (Some x) i
  
    | CCfalse : forall x i,
                  evalX E I x i [Vbool false] ->
                  conform_clock Vbot (Some x) i
  
    | CCbot : forall x i,
                evalX E I x i Vbot ->
                conform_clock Vbot (Some x) i
    .
  
  Inductive conform_clock_io : val' -> clock -> time -> Prop :=
    | CCIdefault : forall u i,
                     conform_clock_io [u] None i
  
    | CCItrue : forall u x s i,
                  M.MapsTo x s I ->
                  nth_error s i = Some [Vbool true] ->
                  conform_clock_io [u] (Some x) i
  
    | CCIfalse : forall x s i,
                   M.MapsTo x s I ->
                   nth_error s i = Some [Vbool false] ->
                   conform_clock_io Vbot (Some x) i
  
    | CCIbot : forall x s i,
                 M.MapsTo x s I ->
                 nth_error s i = Some Vbot ->
                 conform_clock_io Vbot (Some x) i
    .
  
  Inductive well_type : expr -> Prop :=
    | Wvar : forall x t c,
               M.MapsTo x t T ->
               M.MapsTo x c C ->
               well_type (Evar x t c)
  
    | Wconst : forall u t c,
                 well_type_val u t ->
                 c = None ->
                 well_type (Econst u t c)
  
    | Wwhen : forall e x t c,
                well_type e ->
                M.MapsTo x Tbool T ->
                M.MapsTo x (clockof e) C ->
                typeof e = t ->
                Some x = c ->
                well_type (Ewhen e x t c)
  
    | Wcurr : forall e x c ui t,
                well_type e ->
                clockof e = Some x ->
                M.MapsTo x Tbool T ->
                M.MapsTo x c C ->
                well_type_val ui t ->
                typeof e = t ->
                well_type (Ecurr e x ui t c)
  
    | Wfby : forall ea eb t c,
               well_type ea ->
               well_type eb ->
               typeof ea = t ->
               typeof eb = t ->
               clockof ea = c ->
               clockof eb = c ->
               well_type (Efby ea eb t c)
  
    | WDnot : forall ea t c,
                well_type ea ->
                typeof ea = t ->
                clockof ea = c ->
                t = Tbool ->
                well_type (Edata1 Onot ea t c)
  
    | WDopp : forall ea t c,
                well_type ea ->
                typeof ea = t ->
                clockof ea = c ->
                t = Tz ->
                well_type (Edata1 Oopp ea t c)
  
    | WDbinZZ : forall ea eb t c o,
                  well_type ea ->
                  well_type eb ->
                  typeof ea = t ->
                  typeof eb = t ->
                  clockof ea = c ->
                  clockof eb = c ->
                  t = Tz ->
                  o = Oplus \/ o = Ominus \/ o = Omul \/ o = Odiv \/ o = Omod ->
                  well_type (Edata2 o ea eb t c)

    | WDbinZB : forall ea eb t c o,
                  well_type ea ->
                  well_type eb ->
                  typeof ea = Tz ->
                  typeof eb = Tz ->
                  clockof ea = c ->
                  clockof eb = c ->
                  t = Tbool ->
                  o = Ole \/ o = Olt \/ o = Oge \/ o = Ogt \/ o = Oeq \/ o = One ->
                  well_type (Edata2 o ea eb t c)

    | WDbinBB : forall ea eb t c o,
                  well_type ea ->
                  well_type eb ->
                  typeof ea = t ->
                  typeof eb = t ->
                  clockof ea = c ->
                  clockof eb = c ->
                  t = Tbool ->
                  o = Oand \/ o = Oor \/ o = Oeq \/ o = One ->
                  well_type (Edata2 o ea eb t c)
  
    | WDif : forall ea eb ec t c,
               well_type ea ->
               well_type eb ->
               well_type ec ->
               typeof ea = Tbool ->
               typeof eb = t ->
               typeof ec = t ->
               clockof ea = c ->
               clockof eb = c ->
               clockof ec = c ->
               well_type (Edata3 Oif ea eb ec t c)
               
               (* TODO: consider to pull this [Oif] out, and replace with an [o] *)
    .

  Inductive clk_nocyc : ident -> Prop :=
    | NIinit :
        forall x,
          M.MapsTo x None C ->
          clk_nocyc x
  
    | NIlevel :
        forall x x',
          M.MapsTo x (Some x') C ->
          clk_nocyc x' ->
          clk_nocyc x
    .
  
  Inductive nocyc_strong : expr -> Prop :=
    | NSvar : forall x t c,
                nocyc_strongX x ->
                nocyc_strongC c ->
                nocyc_strong (Evar x t c)
  
    | NSconst : forall u t c,
                  nocyc_strongC c ->
                  nocyc_strong (Econst u t c)
  
    | NSwhen : forall e x t c,
                 nocyc_strong e ->
                 nocyc_strongX x ->
                 nocyc_strongC c ->
                 nocyc_strong (Ewhen e x t c)
  
    | NScurr : forall e x ui t c,
                 nocyc_strong e ->
                 nocyc_strongX x ->
                 nocyc_strongC c ->
                 nocyc_strong (Ecurr e x ui t c)
  
    | NSfby : forall ea eb t c,
                nocyc_strong ea ->
                nocyc_strongC c ->
                nocyc_strong (Efby ea eb t c)
  
    | NSdata1 : forall o ea t c,
                  nocyc_strong ea ->
                  nocyc_strongC c ->
                  nocyc_strong (Edata1 o ea t c)
  
    | NSdata2 : forall o ea eb t c,
                  nocyc_strong ea ->
                  nocyc_strong eb ->
                  nocyc_strongC c ->
                  nocyc_strong (Edata2 o ea eb t c)
  
    | NSdata3 : forall o ea eb ec t c,
                  nocyc_strong ea ->
                  nocyc_strong eb ->
                  nocyc_strong ec ->
                  nocyc_strongC c ->
                  nocyc_strong (Edata3 o ea eb ec t c)
  
  with nocyc_strongX : ident -> Prop :=
    | NSVinit : forall x c,
                  M.MapsTo x Kin K ->
                  M.MapsTo x c C ->
                  nocyc_strongC c ->
                  nocyc_strongX x
  
    | NSVdef : forall x e c,
                 M.MapsTo x e E ->
                 M.MapsTo x c C ->
                 nocyc_strong e ->
                 nocyc_strongC c ->
                 nocyc_strongX x
  
  with nocyc_strongC : clock -> Prop :=
    | NSCdefault : nocyc_strongC None
  
    | NSCvar : forall x,
                 nocyc_strongX x ->
                 nocyc_strongC (Some x)
    .

  Scheme Inocyc_strong := Induction for nocyc_strong Sort Prop
    with Inocyc_strongX := Induction for nocyc_strongX Sort Prop
    with Inocyc_strongC := Induction for nocyc_strongC Sort Prop.
  
  Combined Scheme CInocyc_strongX from Inocyc_strong, Inocyc_strongX.
  Combined Scheme CInocyc_strong from Inocyc_strong, Inocyc_strongX, Inocyc_strongC.
  
  Inductive nocyc : expr -> Prop :=
    | NCvar : forall x t c,
                nocycX x ->
                nocyc (Evar x t c)
  
    | NCconst : forall u t c,
                  nocyc (Econst u t c)
  
    | NCwhen : forall e x t c,
                 nocyc e ->
                 nocycX x ->
                 nocyc (Ewhen e x t c)
  
    | NCcurr : forall e x ui t c,
                 nocyc e ->
                 nocycX x ->
                 nocyc (Ecurr e x ui t c)
  
    | NCfby : forall ea eb t c,
                nocyc ea ->
                nocyc (Efby ea eb t c)
  
    | NCdata1 : forall o ea t c,
                  nocyc ea ->
                  nocyc (Edata1 o ea t c)
  
    | NCdata2 : forall o ea eb t c,
                  nocyc ea ->
                  nocyc eb ->
                  nocyc (Edata2 o ea eb t c)
  
    | NCdata3 : forall o ea eb ec t c,
                  nocyc ea ->
                  nocyc eb ->
                  nocyc ec ->
                  nocyc (Edata3 o ea eb ec t c)
  
  with nocycX : ident -> Prop :=
    | NCVinit : forall x,
                  M.MapsTo x Kin K ->
                  nocycX x
  
    | NCVdef : forall x e,
                 M.MapsTo x e E ->
                 nocyc e ->
                 nocycX x
    .

  Scheme Inocyc := Induction for nocyc Sort Prop
    with InocycX := Induction for nocycX Sort Prop.
  
  Combined Scheme CInocycX from Inocyc, InocycX.
  

  

  (** ** Properties of a program *)
  Definition PconsistentC :=
    forall x, M.In x C <-> M.In x K.

  Definition PconsistentT :=
    forall x, M.In x T <-> M.In x K.

  Definition PconsistentE :=
    forall x, M.In x E <-> M.MapsTo x Kout K \/ M.MapsTo x Kloc K.

  Definition PconsistentI :=
    forall x, M.In x I <-> M.MapsTo x Kin K.

  Definition PconsistentO :=
    forall x, M.In x J <-> M.MapsTo x Kout K.



  Definition Pwell_type :=
    forall x e, M.MapsTo x e E -> well_type e.

  Definition Pwell_type_t :=
    forall x e t, M.MapsTo x e E -> M.MapsTo x t T -> typeof e = t.

  Definition Pwell_type_c :=
    forall x e c, M.MapsTo x e E -> M.MapsTo x c C -> clockof e = c.


  
  Definition Pnocyc :=
    forall x, M.In x K -> nocycX x.

  Definition PnocycE :=
    forall e, well_type e -> nocyc e.

  Definition Pnocyc_strong :=
    forall x, M.In x K -> nocyc_strongX x.

  Definition Pnocyc_strongE :=
    forall e, well_type e -> nocyc_strong e.

  Definition Pclk_nocyc :=
    forall x, M.In x K -> clk_nocyc x.

  Definition Pclk_nocyc_inp :=
    forall x, M.MapsTo x Kin K -> clk_nocyc x.

  
  
  Definition Pclk_bool :=
    forall x x', M.MapsTo x (Some x') C -> M.MapsTo x' Tbool T.

  Definition Pclk_boolE :=
    forall e x', well_type e -> clockof e = Some x' -> M.MapsTo x' Tbool T.

  Definition Pclk_bool_inp :=
    forall x x', M.MapsTo x Kin K -> M.MapsTo x (Some x') C -> M.MapsTo x' Tbool T.

  Definition Pclk_var :=
    forall x x', M.MapsTo x (Some x') C -> M.In x' K.

  Definition Pclk_varE :=
    forall e x', well_type e -> clockof e = Some x' -> M.In x' K.


  
  Definition Pexistence n :=
    forall x i, i < n -> M.In x K -> exists v, evalX E I x i v.

  Definition PexistenceE n :=
    forall e i, i < n -> well_type e -> exists v, eval E I e i v.

  Definition PexistenceP n :=
    forall e ui i, i < n -> well_type e -> exists u, evalP E I e i ui u.

  Definition Pdeterminism :=
    forall x i va vb, evalX E I x i va -> evalX E I x i vb -> va = vb.

  Definition PdeterminismE :=
    forall e i va vb, eval E I e i va -> eval E I e i vb -> va = vb.

  Definition PdeterminismP :=
    forall e i ui ua ub, evalP E I e i ui ua -> evalP E I e i ui ub -> ua = ub.
  
  Definition Pgood_val_t :=
    forall x i t u, M.MapsTo x t T -> evalX E I x i [u] -> well_type_val u t.
  
  Definition Pgood_val_tE :=
    forall e i u, well_type e -> eval E I e i [u] -> well_type_val u (typeof e).

  (* maybe add this: Definition Pgood_val_tP *)
  
  Definition Pgood_val_c :=
    forall x c i v, M.MapsTo x c C -> evalX E I x i v -> conform_clock v c i.
  
  Definition Pgood_val_cE :=
    forall e i v, well_type e -> eval E I e i v -> conform_clock v (clockof e) i.

  Definition Pgood_io_val_t (IO: Eio) :=
    forall x s t u i,
      M.MapsTo x s IO ->
      M.MapsTo x t T ->
      nth_error s i = Some [u] ->
      well_type_val u t.
  
  Definition Pgood_io_val_c (IO: Eio) :=
    forall x s c v i,
      M.MapsTo x s IO ->
      M.MapsTo x c C ->
      nth_error s i = Some v ->
      conform_clock_io v c i.



  Definition Pinp_long n :=
    forall x s, M.MapsTo x s I -> n <= length s.

  Definition Pinp_len n :=
    forall x s, M.MapsTo x s I -> n = length s.

  Definition Pout_len n :=
    forall x s, M.MapsTo x s J -> n = length s.
  


  Definition Pout_clk_in :=
    forall x x',
      M.MapsTo x Kout K ->
      M.MapsTo x (Some x') C ->
      M.MapsTo x' Kin K.

  Definition Pin_clk_in :=
    forall x x',
      M.MapsTo x Kin K ->
      M.MapsTo x (Some x') C ->
      M.MapsTo x' Kin K.
  


  Hint Constructors
    well_type_val
    conform_clock
    clk_nocyc
    nocyc_strong
    nocyc_strongX
    nocyc_strongC
    nocyc
    nocycX : constr.
  
  Hint Unfold
    PconsistentC
    PconsistentT
    PconsistentE
    PconsistentI
    Pwell_type
    Pwell_type_t
    Pwell_type_c
    Pnocyc
    PnocycE
    Pnocyc_strong
    Pnocyc_strongE
    Pclk_nocyc
    Pclk_nocyc_inp
    Pclk_bool
    Pclk_boolE
    Pclk_bool_inp
    Pclk_var
    Pclk_varE
    Pexistence
    PexistenceE
    PexistenceP
    Pdeterminism
    PdeterminismE
    PdeterminismP
    Pgood_val_t
    Pgood_val_tE
    Pgood_val_c
    Pgood_val_cE
    Pgood_io_val_t
    Pgood_io_val_c
    Pinp_long
    Pinp_len
    Pout_len
    Pout_clk_in
    Pin_clk_in : properties.
  
  Hypothesis HconsistentT : PconsistentT.
  Hypothesis HconsistentC : PconsistentC.
  Hypothesis HconsistentE : PconsistentE.
  Hypothesis HconsistentI : PconsistentI.

  Ltac inversion_WT :=
    ( iter_tac ( fun x => match type of x with
      | well_type _ => inversion x; clear x
      | _ => idtac
    end ) ); subst; simpl'.
  
  Ltac kind_consistent :=
    solve [ eapply HconsistentT; eauto |
            eapply HconsistentC; eauto |
            eapply HconsistentI; eauto |
            eapply HconsistentE; eauto |
            apply <- HconsistentT; eauto |
            apply <- HconsistentC; eauto |
            apply <- HconsistentI; eauto |
            apply <- HconsistentE; eauto ].
  
  Ltac kind_elaborate x :=
    match goal with
      | [ H : M.MapsTo x Kin K |- _ ] =>
        let HH := fresh "H_I" in
        let s := fresh "s" in
          assert (HH: M.In x I);
          [ kind_consistent | destruct HH as [s HH] ]
  
      | [ H : M.MapsTo x Kout K |- _ ] =>
        let HH := fresh "H_E" in
        let e := fresh "e" in
          assert (HH: M.In x E);
          [ kind_consistent | destruct HH as [e HH] ]
    end.
  
  Ltac kind_attach x :=
    match goal with
      | [ H: M.In x I |- _ ] =>
        assert (M.MapsTo x Kin K); [ kind_consistent; eauto | idtac ]
      | [ H: M.MapsTo x _ I |- _ ] =>
        assert (M.MapsTo x Kin K); [ kind_consistent; eauto | idtac ]
      | [ H: M.In x E |- _ ] =>
        assert (M.MapsTo x Kout K \/ M.MapsTo x Kloc K); [ kind_consistent; eauto | idtac ]
      | [ H: M.MapsTo x _ E |- _ ] =>
        assert (M.MapsTo x Kout K \/ M.MapsTo x Kloc K); [ kind_consistent; eauto | idtac ]
      | [ |- _ ] =>
        let Hk := fresh "Hk" in
        let knd := fresh "knd" in
          assert (Hk: M.In x K); [ kind_consistent; eauto | destruct Hk as [knd Hk] ]
    end.

  Ltac in_or_out k :=
    let Hio := fresh "Hio" in
    assert (Hio: k = Kin \/ k = Kout \/ k = Kloc);
      [ destruct k; auto | destruct Hio; [ subst k | ] ].

  (** These lemmas/theorems were proved when we had not decide what is
  a well-formed program. *)

  (** ** Any variable on which a clock is built is of type bool *)
  Theorem T9 :
    Pclk_bool_inp ->
    Pnocyc ->
    PnocycE ->
    Pwell_type ->
    Pwell_type_c ->
    Pclk_boolE /\ Pclk_bool.
  Proof.
    autounfold with properties.
    intros Hclk_bool_inp Hnocyc HnocycE Hwell_type Hwell_type_c.
  
    cut (( forall e, nocyc e ->
                     forall x',
                       well_type e ->
                       clockof e = Some x' ->
                       M.MapsTo x' Tbool T) /\
         ( forall x, nocycX x ->
                     forall x',
                       M.MapsTo x (Some x') C ->
                       M.MapsTo x' Tbool T)).
    { intros [ HH1 HH2 ]. split.
      + intros.
        assert (nocyc e).
          eapply HnocycE; eauto.
        eapply HH1; eauto.
      + intros.
        assert (nocycX x).
          eapply Hnocyc; eauto.
          kind_consistent.
        eapply HH2; eauto. }
  
    apply CInocycX with
      (P := fun e _ =>
              forall x', well_type e -> clockof e = Some x' -> M.MapsTo x' Tbool T )
      (P0 := fun x _ => forall x', M.MapsTo x (Some x') C -> M.MapsTo x' Tbool T );
  
    eauto; intros;
  
    try match goal with
      | [ H : well_type _ |- _ ] => inversion H; clear H; subst; simpl in *; subst;
                                    simpl'; subst
    end;
  
    eauto; try discriminate.
  Qed.
  
  (** ** Lemmas about Pinp_long *)
  Lemma L2 :
    forall i j x,
      Pinp_long i ->
      j < i ->
      M.MapsTo x Kin K ->
      exists u, evalX E I x j u.
  Proof.
    autounfold with properties.
    intros i j x Hinp_long' Hj Hk.
  
    kind_elaborate x.
    specialize (Hinp_long' _ _ H_I).
    assert (HH: j < length s) by omega.
    apply nth_error_ok in HH.
    apply option_exist in HH.
    destruct HH.
  
    eauto with constr.
  Qed.

  Lemma L2b :
    forall i j x,
      Pinp_len i ->
      j < i ->
      M.MapsTo x Kin K ->
      exists u, evalX E I x j u.
  Proof.
    autounfold with properties.
    intros i j x Hinp_len Hj Hk.
  
    kind_elaborate x.
    specialize (Hinp_len _ _ H_I). subst.
    apply nth_error_ok in Hj.
    apply option_exist in Hj.
    destruct Hj.
  
    eauto with constr.
  Qed.

  Lemma L5 : forall n m, n < m -> Pinp_long m -> Pinp_long n.
  Proof.
    unfold Pinp_long.
    intros.
    specialize (H0 _ _ H1).
    omega.
  Qed.


  (** ** Free of loops of clocks *)
  Theorem T0 :
    Pwell_type ->
    Pwell_type_c ->
    Pclk_nocyc_inp ->
    Pnocyc ->
    Pclk_nocyc.
  Proof.
    autounfold with properties.
    intros Hwell_type Hwell_type_c Hclk_nocyc_inp' Hnocyc x H.

    specialize (Hnocyc x H).
    clear H.

    induction Hnocyc using InocycX with
      (P := fun e _ => forall x,
                         well_type e ->
                         clockof e = Some x ->
                         clk_nocyc x)
      (P0 := fun x _ => clk_nocyc x);

    intros; simpl in *; inversion_WT; subst; eauto with constr;

    try discriminate.

    - inversion IHHnocyc; subst; try map_trivial; simpl'; subst; eauto.
    - inversion IHHnocyc0; subst; try map_trivial; simpl'; subst; eauto.
    
    - assert (M.MapsTo x Kout K \/ M.MapsTo x Kloc K) by kind_consistent.
      assert (M.In x K) by (destruct H; eauto).
      assert (HH: M.In x C) by kind_consistent.
      destruct HH as [ c HH ].

      destruct c as [x' | ]; eauto with constr.
  Qed.

  (** ** Free of causuality loop *)
  Lemma L1 :
    Pclk_nocyc_inp ->
    Pin_clk_in ->
    forall x,
      M.MapsTo x Kin K ->
      nocyc_strongX x.
  Proof.
    autounfold with properties.
    intros.

    specialize (H x H1).
    revert H1.
    move H after H0.

    induction H; intros; eauto with constr.
  Qed.
  
  Theorem T1 :
    Pwell_type ->
    Pwell_type_c ->
    Pin_clk_in ->
    Pclk_nocyc_inp ->
    Pnocyc ->
    Pnocyc_strong.
  Proof.
    autounfold with properties.
  
    intros Hwell_type Hwell_type_c Hin_clk_in Hclk_nocyc_inp Hnocyc x H.
    assert (HHH: nocycX x).
    auto.
    clear H Hnocyc.
  
    induction HHH using InocycX with
       (P := fun e _ => well_type e -> nocyc_strong e /\ nocyc_strongC (clockof e))
       (P0 := fun x _ => nocyc_strongX x);
  
    intros; inversion_WT; try split; simpl; try constructor;
  
    simpl';
  
    try match goal with
      | [ H : nocyc_strongX ?x |- _ ] => inversion H; subst
    end;
  
    map_trivial;
  
    eauto with constr.
  
    apply L1; try assumption.
  
    kind_attach x.
    assert (HH: M.In x C) by (destruct H1; kind_consistent).
    destruct HH as [c HH].
    apply NSVdef with (e:=e) (c:=c); try assumption.
    cutrewrite (c=clockof e); [ assumption | symmetry; eapply Hwell_type_c; eauto ].
  Qed.
  
  Lemma L13 :
    Pnocyc -> PnocycE.
  Proof.
    autounfold with properties.
    intro Hnocyc.
  
    intro e; induction e;
  
    intro Hwt; inversion Hwt; subst;
  
    try kind_attach x;
    try ( assert (Hx: nocycX x); [ destruct knd; eauto; fail | idtac ] );
  
    constructor; eauto.
  Qed.

  Lemma L11 :
    Pnocyc_strong -> Pnocyc_strongE.
  Proof.
    autounfold with properties.
    
    intros. induction H0; subst;

    try kind_attach x;
    try ( assert (Hx: nocyc_strongX x); [ eauto; fail | inversion Hx; subst ] );

    map_trivial; eauto with constr;

    try match reverse goal with
      | [ H: nocyc_strong _ |- _ ] => inversion H; subst; eauto with constr
    end.
  Qed.
  
  (** ** Good value properties *)
  Lemma LD1_1 :
    forall o ea t c ua u,
      evalD1 o ua u ->
      well_type (Edata1 o ea t c) ->
      well_type_val u t.
  Proof.
    intros o ea t c ua u HH Hwt.
    inversion Hwt; inversion HH; subst; try discriminate.
    + eauto with constr.
      rewrite H6. eauto with constr.
    + eauto with constr.
      rewrite H6. eauto with constr.
  Qed.

  Lemma LD1_2 :
    forall o ea eb t c ua ub u,
      evalD2 o ua ub u ->
      well_type (Edata2 o ea eb t c) ->
      well_type_val u t.
  Proof.
    intros.

    inversion H0; repeat destruct H13 as [ HH | H13 ]; subst;
    inversion H; subst; try discriminate;
    eauto with constr; rewrite H12; eauto with constr.
  Qed.
  
  Lemma LD1_3 :
    forall o ea eb ec t c ua ub uc u,
      evalD3 o ua ub uc u ->
      well_type (Edata3 o ea eb ec t c) ->
      well_type_val ub (typeof eb) ->
      well_type_val uc (typeof ec) ->
      well_type_val u t.
  Proof.
    intros o ea eb ec t c ua ub uc u HH Hwt HH1 HH2.
    inversion Hwt; inversion HH; subst; try discriminate;
    eauto with constr; congruence.
  Qed.
  
  Lemma L10 :
    forall v c i,
      conform_clock_io v c i ->
      conform_clock v c i.
  Proof.
    intros v c i HH.
    inversion HH;
    [ constructor 1 | constructor 2 | constructor 3 | constructor 4 ];
    eapply RVin; eauto.
  Qed.

  Theorem T2 :
    Pgood_io_val_t I ->
    Pwell_type ->
    Pwell_type_t ->
    Pgood_val_t /\ Pgood_val_tE.
  Proof.
    autounfold with properties.
  
    intros Hgood_inp_val_t Hwell_type Hwell_type_t.
    cut ((forall e i v,
            eval E I e i v ->
            well_type e -> forall u, [u]=v -> well_type_val u (typeof e)) /\
         (forall x i v,
            evalX E I x i v ->
            forall u t, [u]=v -> M.MapsTo x t T -> well_type_val u t)).
    intro.
    split; firstorder.
  
    clear - Hgood_inp_val_t Hwell_type Hwell_type_t.
  
    apply CIevalX with
      (P := fun e i v _ =>
              well_type e -> forall u, [u] = v -> well_type_val u (typeof e))
      (P0 := fun x i v _ =>
               forall u t, [u] = v -> M.MapsTo x t T -> well_type_val u t)
      (P1 := fun e i ui u _ =>
               well_type e -> well_type_val ui (typeof e) -> well_type_val u (typeof e));
  
    intros;
  
    try match goal with
      | [ H : well_type _ |- _ ] => inversion H
    end;
  
    try match goal with
      | [ H : evalP _ _ _ _ _ _ |- _ ] => inversion H
    end;
  
    repeat match goal with
      | [ H : [?x] = [?y] |- _ ] => injection H; intro; clear H
    end; auto; try discriminate;

    subst;
  
    try solve [ eapply LD1_1; eauto
              | eapply LD1_2; eauto
              | eapply LD1_3; eauto ]; eauto; simpl.

    + rewrite H10 in *.
      eauto.

    + rewrite H10 in *.
      eauto.

    + cutrewrite (t=typeof e).
      - apply H; eauto.
      - symmetry. apply Hwell_type_t with (x:=x); try assumption.
  Qed.
  
  Theorem T3 :
    Pgood_io_val_c I ->
    Pwell_type ->
    Pwell_type_c ->
    Pgood_val_c /\ Pgood_val_cE.
  Proof.
    autounfold with properties.

    intros Hgood_inp_val_c Hwell_type Hwell_type_c.
    cut ((forall e i v, eval E I e i v ->
                         well_type e -> conform_clock v (clockof e) i) /\
         (forall x i v, evalX E I x i v ->
                         forall c, M.MapsTo x c C -> conform_clock v c i)).
    intro.
    split; firstorder.
  
    clear - Hgood_inp_val_c Hwell_type Hwell_type_c.
  
    apply CIevalX with
      (P := fun e i v _ => well_type e -> conform_clock v (clockof e) i)
      (P0 := fun x i v _ => forall c, M.MapsTo x c C -> conform_clock v c i)
      (P1 := fun e i ui u _ => True);
  
    intros;
    
    try match goal with
      | [ H : well_type _ |- _ ] => inversion H
    end;
  
    repeat match goal with
      | [ H : [?x] = [?y] |- _ ] => injection H; intro; clear H
      | [ Hx : ?x, H : _ = ?x |- _ ] => rewrite <- H in *; clear H
      | [ H1 : M.MapsTo ?x _ C, H2 : forall c, M.MapsTo ?x c C -> _ |- _ ] =>
           specialize (H2 _ H1); inversion H2
    end; simpl; auto with constr ; try discriminate;
  
    try solve [ subst; simpl'; inversion H; eauto with constr ].
  
    + apply L10.
      apply Hgood_inp_val_c with (x:=x) (s:=s); try assumption.
  
    + assert (well_type e); firstorder.
      cutrewrite (c=clockof e). assumption.
      symmetry. apply Hwell_type_c with (x:=x); assumption.
  Qed.

  Theorem T10 :
    forall n,
      ProgramEval (mkProgram K T C E) n I J ->
      Pgood_val_t ->
      Pgood_io_val_t J.
  Proof.
    intros. inversion H; clear H; simpl in *; subst.

    autounfold with properties.
    autounfold with properties in H0.

    intros.
    specialize (H3 x s i [u]).
    specialize (H0 x i t u).
    simpl'.
    assumption.
  Qed.

  Theorem T11 :
    forall n,
      ProgramEval (mkProgram K T C E) n I J ->
      Pgood_val_c ->
      Pout_clk_in ->
      Pgood_io_val_c J.
  Proof.
    intros. inversion H; clear H; simpl in *; subst.

    autounfold with properties.
    autounfold with properties in H0, H1.

    intros.
    specialize (H4 x s i v).
    specialize (H0 x c i v).
    simpl'.

    destruct c as [ x' | ].
    + specialize (H1 x x').

      assert (M.In x J) by eauto.
      rewrite <- H2 in H7.

      simpl'.

      inversion H0; subst; clear H0;
      ( inversion H10; subst;
        [ | kind_attach x'; destruct H9; map_trivial ] ).
      - constructor 2 with (s:=s0); try assumption.
      - constructor 3 with (s:=s0); try assumption.
      - constructor 4 with (s:=s0); try assumption.

    + inversion H0; subst; clear H0.
      constructor 1.
  Qed.

  (** ** Lemmas about conform_clock *)
  Lemma L3 :
    Pdeterminism ->
    forall v1' v2' c i,
      conform_clock v1' c i ->
      conform_clock v2' c i ->
      v1' = Vbot ->
      v2' = Vbot.
  Proof.
    autounfold with properties.
  
    intros Hdeterminism v1' v2' c i Hc1 Hc2.
    inversion Hc1; inversion Hc2; subst; intro;
  
    repeat match goal with
      | [ H : Some _ = Some _ |- _ ] => injection H; clear H; intro; subst
      | [ Hc1 : evalX E I ?x ?i ?v1', Hc2 : evalX E I ?x ?i ?v2' |- _ ] =>
          assert (v1'=v2'); [ firstorder | clear Hc2 ]
    end;
  
    try discriminate; reflexivity.
  Qed.
  
  Lemma L6 :
    Pdeterminism ->
    forall v x i,
      conform_clock v (Some x) i ->
      evalX E I x i [Vbool true] ->
      v <> Vbot.
  Proof.
    intros Hdeterminism v x i Hcc He.
    inversion Hcc;
  
    match goal with
      | [ H1 : evalX E I ?x ?i ?v1', H2 : evalX E I ?x ?i ?v2' |- _ ] =>
        assert (v1' = v2'); [ firstorder | clear H2 ]
    end;
  
    try discriminate.
  Qed.
  
  Lemma L7 :
    Pdeterminism ->
    forall v x i,
      conform_clock v (Some x) i ->
      evalX E I x i Vbot ->
      v = Vbot.
  Proof.
    intros Hdeterminism v x i Hcc He.
  
    inversion Hcc;
  
    match goal with
      | [ H1 : evalX E I ?x ?i ?v1', H2 : evalX E I ?x ?i ?v2' |- _ ] =>
        assert (v1' = v2'); [ firstorder | clear H2 ]
    end;
  
    try discriminate;
    reflexivity.
  Qed.
  
  (** ** Existence of semantics *)
  Lemma L4 :
    forall e ui i,
      (forall i', i'<i -> exists v, eval E I e i' v) ->
      exists u, evalP E I e i ui u.
  Proof.
    induction i.
    intros.
    exists ui. constructor.
  
    intros.
    assert (Hv : exists v, eval E I e i v). auto with arith.
    assert (Hp : exists u, evalP E I e i ui u). auto with arith.
    destruct Hv as [v Hv].
    destruct Hp as [vp' Hp].
  
    destruct v as [ u | ].
    eexists u. constructor. assumption.
  
    eexists vp'. apply RPpull; assumption.
  Qed.
  
  Lemma LD2_1 :
    forall o ea t c ua,
      well_type (Edata1 o ea t c) ->
      well_type_val ua (typeof ea) ->
      exists u, evalD1 o ua u.
  Proof.
    intros.
    inversion H; inversion H0; subst; try congruence.
    + exists (Vbool (negb u)); constructor.
    + exists (Vz (Z.opp u)); constructor.
  Qed.
  
  Lemma LD2_2 :
    forall o ea eb t c ua ub,
      well_type (Edata2 o ea eb t c) ->
      well_type_val ua (typeof ea) ->
      well_type_val ub (typeof eb) ->
      exists u, evalD2 o ua ub u.
  Proof.
    intros.
    inversion H; repeat destruct H14 as [ HH | H14 ]; subst;
    inversion H0; inversion H1; subst; try congruence.

    + exists (Vz (Z.add u u0)); constructor.
    + exists (Vz (Z.sub u u0)); constructor.
    + exists (Vz (Z.mul u u0)); constructor.
    + exists (Vz (Z.div u u0)); constructor.
    + exists (Vz (Z.modulo u u0)); constructor.

    + exists (Vbool (Z.leb u u0)); constructor.
    + exists (Vbool (Z.ltb u u0)); constructor.
    + exists (Vbool (Z.geb u u0)); constructor.
    + exists (Vbool (Z.gtb u u0)); constructor.

    + exists (Vbool (Z.eqb u u0)); constructor.
    + exists (Vbool (negb (Z.eqb u u0))); constructor.

    + exists (Vbool (andb u u0)); constructor.
    + exists (Vbool (orb  u u0)); constructor.

    + exists (Vbool (eqb u u0)); constructor.
    + exists (Vbool (negb (eqb u u0))); constructor.
  Qed.
  
  Lemma LD2_3 :
    forall o ea eb ec t c ua ub uc,
      well_type (Edata3 o ea eb ec t c) ->
      well_type_val ua (typeof ea) ->
      well_type_val ub (typeof eb) ->
      well_type_val uc (typeof ec) ->
      exists u, evalD3 o ua ub uc u.
  Proof.
    intros o ea eb ec t c ua ub uc HH1 HH2 HH3 HH4;
    inversion HH1; inversion HH2; inversion HH3; inversion HH4; subst; try congruence;
    destruct u; eexists; econstructor; eauto.
  Qed.
  
  (* Previously another proof of existence of semantics (which is more
     complex) is also presented; but when I added more features to the
     small language, I kept only this simpler proof. *)
  Lemma L12 :
    Pdeterminism ->
    Pgood_val_t -> Pgood_val_tE ->
    Pgood_val_c -> Pgood_val_cE ->
    Pwell_type ->
    Pnocyc_strong ->
    forall n,
      Pinp_long (S n) ->
      (forall i x, i < n -> M.In x K -> exists v, evalX E I x i v) ->
      (forall i e, i < n -> well_type e -> exists v, eval E I e i v) ->
      (forall x, M.In x K -> exists v, evalX E I x n v) /\
      (forall e, well_type e -> exists v, eval E I e n v).
  Proof.
    autounfold with properties.

    intros Hdeterminism Hgood_val_t Hgood_val_tE Hgood_val_c Hgood_val_cE.
    intros Hwell_type Hnocyc_strong.
    intros n Hinp_long HeX He.
  
    cut ((forall e, nocyc_strong e -> well_type e -> exists v, eval E I e n v) /\
         (forall x, nocyc_strongX x -> exists v, evalX E I x n v)).
    intros [Ha Hb].
    split; intros; [ eapply Hb | eapply Ha; eauto; eapply L11 ]; eauto.
  
    apply CInocyc_strongX with
      (P := fun e _ => well_type e -> exists v, eval E I e n v)
      (P0 := fun x _ => exists v, evalX E I x n v)
      (P1 := fun c _ => True);
  
    intros;
  
    try match goal with
      | [ H: well_type _ |- _ ] => inversion H
    end;
  
    repeat match goal with
      | [ H: well_type ?e -> _, H': well_type ?e |- _ ] => specialize (H H')
  
      | [ H : (@ex val' _) |- _ ] => let v := fresh v
                                    with u := fresh u
                                    with HHH := fresh HHH
                                    with vh := fresh vH in
                                       destruct H as [v HHH];
                                       case_eq v; [intros u vH | intro vH]; subst v
  
      | [ H : (@ex val _) |- _ ] => let u := fresh u
                                   with HHH := fresh HHH in
                                      destruct H as [u HHH]
  
      | [ Ht : M.MapsTo ?x Tbool T, He : evalX E I ?x _ [?u] |- _ ] =>
        let Hwt := fresh Hwt in
          assert (Hwt: well_type_val u Tbool); [ eauto | idtac ];
          clear Ht; inversion Hwt; subst; clear Hwt
  
      | [ Hvi: well_type_val ?ui (typeof ?e) |- context [ Ecurr ?e _ ?ui _ _ ] ] =>
        assert (exists u, evalP E I e n ui u);
        [ apply L4; intros; apply He; assumption | idtac ];
        clear Hvi
  
      | [ u : bool |- _ ] => destruct u
    end;
  
    try match goal with
      | [ He1: eval E I ?e1 ?i [?v] |- context [ Efby ?e1 ?e2 _ _ ] ] =>
        assert (well_type_val u (typeof e1)); [ eauto | idtac ];
        assert (exists v2, evalP E I e2 n u v2);
        [ apply L4; intros; apply He; assumption | idtac ]
    end;
  
    repeat match goal with
      | [ H : (@ex val' _) |- _ ] => let v := fresh v
                                    with u := fresh u
                                    with HHH := fresh HHH
                                    with vh := fresh vH in
                                       destruct H as [v HHH];
                                       case_eq v; [intros u vH | intro vH]; subst v
  
      | [ H : (@ex val _) |- _ ] => let u := fresh u
                                   with HHH := fresh HHH in
                                      destruct H as [u HHH]
    end;
  
    try solve
        [ assert (HH := LD2_1 o ea t c u);
            simpl'; destruct_ex; subst; eauto with constr
        | assert (HH := LD2_2 o ea eb t c u0 u);
            simpl'; destruct_ex; subst; eauto with constr
        | assert (HH := LD2_3 o ea eb ec t c u1 u0 u);
            simpl'; destruct_ex; subst; eauto with constr ];
  
    repeat match goal with
      | [ Hc : M.MapsTo ?x ?c C, He : evalX E I ?x ?i ?v |- _ ] =>
        let Hcc := fresh Hcc in
          assert (Hcc: conform_clock v c i); [ eauto | clear Hc ]
  
      | [ Hwt : well_type ?e, He : eval E I ?e ?i ?v |- _ ] =>
        let Hcc := fresh Hcc in
          assert (Hcc: conform_clock v (clockof e) i); [ eauto | clear Hwt ]
  
      | [ Hcc1 : conform_clock ?v1' ?c ?i, Hcc2 : conform_clock ?v2' ?c ?i |- _ ] =>
        let H := fresh H in
          solve [ absurd (v1'=Vbot); [ discriminate | idtac ];
                  assert (H: v2'=Vbot); [ auto | idtac ];
                  eapply (L3 Hdeterminism _ _ _ _ Hcc2 Hcc1 H); eauto ]
  
      | [ Hc : clockof _ = _ |- _ ] => rewrite Hc in *; clear Hc
  
      | [ Hcc : conform_clock ?v (Some ?x) ?i, He : evalX E I ?x ?i [Vbool true] |- _ ] =>
        let H := fresh H in
          solve [ assert (H: Vbot<>Vbot);
                  [ eapply (L6 Hdeterminism _ _ _ Hcc He); eauto | idtac ];
                  contradict H; reflexivity ]
  
      | [ Hcc : conform_clock ?v (Some ?x) ?i, He : evalX E I ?x ?i Vbot |- _ ] =>
        let H := fresh H in
          solve [ absurd (v=Vbot); [ discriminate | idtac ];
                  eapply (L7 Hdeterminism _ _ _ Hcc He); eauto ]
    end;
  
    eauto with constr;
  
    subst; try (rewrite H16 in *);
  
    try solve
      [ absurd ([u] = Vbot); [ discriminate | subst; eapply L3 with (v1':=Vbot); eauto ] ].
  
    apply L2 with (i:=S n); auto with arith.
  
    assert (HH: well_type e); [ eauto | destruct (H HH); eauto with constr ].
  Qed.
  
  Theorem T7 :
    forall n,
      Pdeterminism ->
      Pwell_type ->
      Pgood_val_t -> Pgood_val_tE ->
      Pgood_val_c -> Pgood_val_cE ->
      Pnocyc_strong ->
      Pinp_long n ->
      Pexistence n /\ PexistenceE n.
  Proof.
    autounfold with properties.

    intros n.
    intros Hdeterminism Hwell_type.
    intros Hgood_val_t Hgood_val_tE.
    intros Hgood_val_c Hgood_val_cE.
    intros Hnocyc_strong.
    intros Hinp_long.
  
    revert Hinp_long.
  
    induction n.
    intro; split; intros; omega.
  
    intros Hinp_long.
  
    assert (Pinp_long n).
    unfold Pinp_long.
    intros.
    apply Hinp_long in H. omega.
    specialize (IHn H).
    clear H.
  
    cut ((forall x, M.In x K -> exists v, evalX E I x n v) /\
         (forall e, well_type e -> exists v, eval E I e n v));
      [ intros [Ha Hb];
        split;
        intros x i Hi Hx;
        ( assert (Hi': i=n \/ i<n); [ omega | idtac ] );
        ( destruct Hi'; [ subst; clear Hi; eauto | apply IHn; eauto ] ) | idtac ].
  
    destruct IHn.
    apply L12; try assumption;
    intros; auto.
  Qed.
  
  Corollary T6 : forall n,
                   Pdeterminism ->
                   Pwell_type ->
                   Pgood_val_t -> Pgood_val_tE ->
                   Pgood_val_c -> Pgood_val_cE ->
                   Pnocyc_strong ->
                   Pinp_long n ->
                   Pexistence n.
  Proof.
    apply T7.
  Qed.
      
  (** ** Determinism of semantics *)
  
  Lemma LD0_1 :
    forall o ua u u', evalD1 o ua u -> evalD1 o ua u' -> u = u'.
  Proof.
    intros o ua u u' HH1 HH2.
    inversion HH1; inversion HH2; subst;
    congruence.
  Qed.
  
  Lemma LD0_2 :
    forall o ua ub u u', evalD2 o ua ub u -> evalD2 o ua ub u' -> u = u'.
  Proof.
    intros o ua ub u u' HH1 HH2.
    inversion HH1; inversion HH2; subst; try discriminate;
    val_inj;
    congruence.
  Qed.
  
  Lemma LD0_3 :
    forall o ua ub uc u u',
      evalD3 o ua ub uc u ->
      evalD3 o ua ub uc u' ->
      u = u'.
  Proof.
    intros o ua ub uc u u' HH1 HH2.
    inversion HH1; inversion HH2; subst; try discriminate;
    val_inj;
    congruence.
  Qed.

  Theorem T8 : PdeterminismE /\ Pdeterminism /\ PdeterminismP.
  Proof.
    autounfold with properties.
  
    cut ( ( forall e i va,
             eval E I e i va ->
             forall vb,
               eval E I e i vb ->
               va = vb ) /\
          ( forall x i va,
              evalX E I x i va ->
              forall vb,
                evalX E I x i vb ->
                va = vb ) /\
          ( forall e i ui ua,
              evalP E I e i ui ua ->
              forall ub,
                evalP E I e i ui ub ->
                ua = ub ) ).
      firstorder.
  
    apply CIevalEXP with
      (P0 := fun x i v _ => forall v', evalX E I x i v' -> v=v')
      (P1 := fun e i ui u _ => forall u', evalP E I e i ui u' -> u=u')
      (P := fun e i v _ => forall v', eval E I e i v' -> v=v');
  
    intros until v' || intros until u'; intro HH;
  
    inversion HH; try f_equal; auto;
  
    try solve [ absurd ([Vbool true] = [Vbool false]); [ discriminate | auto ] |
                absurd ([Vbool false] = [Vbool true]); [ discriminate | auto ] |
                absurd ([Vbool false] = Vbot);         [ discriminate | auto ] |
                absurd (Vbot = [Vbool false]);         [ discriminate | auto ] |
                absurd ([u] = Vbot);                   [ discriminate | auto ] |
                absurd (Vbot = [u]);                   [ discriminate | auto ] |
                absurd ([ua] = Vbot);                  [ discriminate | auto ] |
                absurd (Vbot = [ua]);                  [ discriminate | auto ] |
                absurd (Vbot = [u']);                  [ discriminate | auto ] |
                absurd ([ui] = Vbot);                  [ discriminate | auto ] |
                absurd (Vbot = [ui]);                  [ discriminate | auto ] ];
  
    try solve [ absurd (M.MapsTo x Kin K /\ ( M.MapsTo x Kout K \/ M.MapsTo x Kloc K) );
                [ let H := fresh in
                  intro H; destruct H as [ H [ | ] ]; map_trivial |
                  split; kind_consistent ] ]; subst;
  
    try (assert (ua = ua0); [ eauto | subst ]);
    try (assert (ub = ub0); [ eauto | subst ]);
    try (assert (uc = uc0); [ eauto | subst ]);
    try (assert (ui = ui0); [ eauto | subst ]);
  
    eauto;
  
    try solve [ eapply LD0_1; eauto
              | eapply LD0_2; eauto
              | eapply LD0_3; eauto ];

    map_trivial; simpl'; auto; congruence.
  Qed.
  
End Properties.

Hint Constructors
  well_type_val
  conform_clock
  conform_clock_io
  well_type
  clk_nocyc
  nocyc_strong
  nocyc_strongX
  nocyc_strongC
  nocyc
  nocycX
  evalD1
  evalD2
  evalD3 : constr.

Ltac inversion_WT :=
  ( iter_tac ( fun x => match type of x with
    | well_type _ _ _ => inversion x; clear x
    | _ => idtac
  end ) ); subst; simpl'.

Ltac kind_consistent' :=
  match goal with
    (* E <=> K *)
    | [ H: PconsistentE ?K ?E, He: M.In ?x ?E |-
        M.MapsTo ?x Kout ?K \/ M.MapsTo ?x Kloc ?K ] =>
      apply H; assumption

    | [ H: PconsistentE ?K ?E, He: M.In ?x ?E |- M.In ?x ?K ] =>
      let HH := fresh in
      assert (HH : M.MapsTo x Kout K \/ M.MapsTo x Kloc K) by kind_consistent';
      destruct HH; eauto

    | [ H: PconsistentE ?K ?E, He: M.MapsTo ?x _ ?E |- context [?x] ] =>
      assert (M.In x E) by eauto;
      solve [ clear He; kind_consistent' ]

    | [ H: PconsistentE ?K ?E, Hk: M.MapsTo ?x Kout ?K |- M.In ?x ?E ] =>
      apply H; left; assumption

    | [ H: PconsistentE ?K ?E, Hk: M.MapsTo ?x Kloc ?K |- M.In ?x ?E ] =>
      apply H; right; assumption

    | [ H: PconsistentE ?K ?E,
        Hk: M.MapsTo ?x Kout ?K \/ M.MapsTo ?x Kloc ?K |- M.In ?x ?E ] =>
      apply H; assumption

    (* I <=> K *)
    | [ H: PconsistentI ?K ?I, Hi: M.In ?x ?I |- M.MapsTo ?x Kin ?K ] =>
      apply H; assumption

    | [ H: PconsistentI ?K ?I, Hi: M.MapsTo ?x Kin ?K |- M.In ?x ?I ] =>
      apply H; assumption

    | [ H: PconsistentI ?K ?I, Hi: M.MapsTo ?x _ ?I |- M.MapsTo ?x Kin ?K ] =>
      assert (M.In x I) by eauto;
      kind_consistent'

    | [ H: PconsistentI ?K ?I, Hi: M.MapsTo ?x _ ?I |- M.In ?x ?K ] =>
      assert (M.MapsTo x Kin K) by kind_consistent';
      eauto

    (* T <=> K *)
    | [ H: PconsistentT ?K ?T, Ht: M.In ?x ?T |- M.In ?x ?K ] =>
      apply H; assumption

    | [ H: PconsistentT ?K ?T, Ht: M.MapsTo ?x _ ?T |- M.In ?x ?K ] =>
      assert (M.In x T) by eauto;
      kind_consistent'

    | [ H: PconsistentT ?K ?T, Ht: M.In ?x ?K |- M.In ?x ?T ] =>
      apply H; assumption

    | [ H: PconsistentT ?K ?T, Ht: M.MapsTo ?x _ ?K |- M.In ?x ?T ] =>
      assert (M.In x K) by eauto;
      kind_consistent'

    (* C <=> K *)
    | [ H: PconsistentC ?K ?C, Ht: M.In ?x ?C |- M.In ?x ?K ] =>
      apply H; assumption

    | [ H: PconsistentC ?K ?C, Ht: M.MapsTo ?x _ ?C |- M.In ?x ?K ] =>
      assert (M.In x C) by eauto;
      kind_consistent'

    | [ H: PconsistentC ?K ?C, Ht: M.In ?x ?K |- M.In ?x ?C ] =>
      apply H; assumption

    | [ H: PconsistentC ?K ?C, Ht: M.MapsTo ?x _ ?K |- M.In ?x ?C ] =>
      assert (M.In x K) by eauto;
      kind_consistent'
  end.

Ltac kind_case :=
  match goal with
  | [ H: M.MapsTo _ Kout _ \/ M.MapsTo _ Kloc _ |- _ ] =>
    destruct H
  end.

(** * Program well-formedness and properties of I/O *)

Section WithProgram.
  Variable p : Program.

  Let K := KK p.
  Let T := TT p.
  Let C := CC p.
  Let E := EE p.

  Record WellFormed := {
    (* Interface part *)
    WFconsistentT:   PconsistentT K T;
    WFconsistentC:   PconsistentC K C;
    WFclk_inp_nocyc: Pclk_nocyc_inp K C;
    WFclk_inp_bool:  Pclk_bool_inp K T C;
    WFout_clk_in:    Pout_clk_in K C;
    WFin_clk_in:     Pin_clk_in K C;
  
    (* Program part *)
    WFconsistentE:   PconsistentE K E;
    WFwell_type:     Pwell_type T C E;
    WFwell_type_t:   Pwell_type_t T E;
    WFwell_type_c:   Pwell_type_c C E;
    WFnocyc:         Pnocyc K E
  }.

  Record ValidInput n I := {
    VIconsistentI:    PconsistentI K I;
    VIinp_long:       Pinp_long I n;
    VIgood_io_val_t:  Pgood_io_val_t T I;
    VIgood_io_val_c:  Pgood_io_val_c C I I
  }.

  Record ValidOutput n I O := {
    VOconsistentO:   PconsistentO K O;
    VOout_len:       Pout_len O n;
    VOgood_io_val_t: Pgood_io_val_t T O;
    VOgood_io_val_c: Pgood_io_val_c C I O
  }.
End WithProgram.

Definition Extend (IO1 IO2: Eio) :=
  forall x s1 s2 i v,
    M.MapsTo x s1 IO1 ->
    M.MapsTo x s2 IO2 ->
    nth_error s1 i = Some v ->
    nth_error s2 i = Some v.

Hint Resolve LD0_1 LD0_2 LD0_3.

Lemma ValidInput_lt :
  forall p I n m,
    m < n ->
    ValidInput p n I ->
    ValidInput p m I.
Proof.
  intros until m. intros Hm HI.
  inversion HI.
  constructor; try assumption.
  apply L5 with (m:=n); assumption.
Qed.

Ltac destructP :=
  iter_tac ( fun H => match type of H with
      WellFormed _ => inversion H
    | ValidInput _ _ _ => inversion H
    | _ => idtac
  end ).

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

Lemma extend_0 :
  forall p n m I1 I2 x i v1 v2,
    WellFormed p ->
    ValidInput p n I1 ->
    ValidInput p m I2 ->
    Extend I1 I2 ->
    evalX (EE p) I1 x i v1 ->
    evalX (EE p) I2 x i v2 ->
    v1 = v2.
Proof.
  intros.
  revert dependent v2.

  induction H3 using IevalX with
    ( P := fun e i va _ =>
             forall vb,
               eval (EE p) I2 e i vb ->
               va = vb )
    ( P0 := fun x i va _ =>
              forall vb,
                evalX (EE p) I2 x i vb ->
                va = vb )
    ( P1 := fun e i ui ua _ =>
              forall ub,
                evalP (EE p) I2 e i ui ub ->
                ua = ub );

  try
    ( match goal with
        | [ |- context [eval _ _ _ _ _ ] ] => idtac
      end;

      intros;

      match goal with
        [ H : eval _ _ _ _ _ |- _ ] => inversion H
      end;

      try f_equal; eauto;

      repeat
        match goal with
          | [ H1: evalX ?E I1 ?x ?i ?va,
              H2: evalX ?E I2 ?x ?i ?vb |- _ ] =>
              assert (va = vb) by eauto; discriminate
    
          | [ H1: evalX ?E I1 ?x ?i ?va,
              H2: evalX ?E I2 ?x ?i ?vb |- _ ] =>
              assert (va = vb) by eauto; subst
    
          | [ H1: eval ?E I1 ?e ?i ?va,
              H2: eval ?E I2 ?e ?i ?vb |- _ ] =>
              assert (va = vb) by eauto; discriminate
    
          | [ H1: eval ?E I1 ?e ?i [?ua],
              H2: eval ?E I2 ?e ?i [?ub] |- _ ] =>
              assert (ua = ub) by eauto; subst; simpl'
    
          | [ H1: eval ?E I1 ?e ?i ?va,
              H2: eval ?E I2 ?e ?i ?vb |- _ ] =>
              assert (va = vb) by eauto; subst; simpl'
          end;

      eauto
    ).

  + assert (ua = ua0) by eauto; subst; simpl'; eauto.
  + assert (ua = ua0) by eauto; subst; simpl'; eauto.
    assert (ub = ub0) by eauto; subst; simpl'; eauto.

  + intros. inversion H3; subst.
    - unfold Extend in H.
      assert (nth_error s0 i = Some v); eauto.
      congruence.
    - kind_attach x (KK p).
      kind_case; map_trivial.
  + intros. inversion H3; subst.
    - kind_attach x (KK p);
      kind_case; map_trivial.
    - map_trivial; auto.

  + intros.
    inversion H3. auto.
  + intros.
    inversion H3; subst.
    - eauto.
    - assert ([u] = Vbot) by eauto; discriminate.
  + intros.
    inversion H3; subst.
    - assert (Vbot = [ub]) by eauto; discriminate.
    - eauto.
Qed.

(** * Additional properties for well-formed programs when input is valid *)

(** ** First Category: syntax level properties *)

Lemma program_PnocycE :
  forall p,
    WellFormed p ->
    PnocycE (KK p) (TT p) (CC p) (EE p).
Proof.
  intros; destructP.
  eapply L13; eauto.
Qed.

Lemma program_Pnocyc_strong :
  forall p,
    WellFormed p ->
    Pnocyc_strong (KK p) (CC p) (EE p).
Proof.
  intros; destructP.
  eapply T1; eauto.
Qed.

Lemma program_Pnocyc_strongE :
  forall p,
    WellFormed p ->
    Pnocyc_strongE (KK p) (TT p) (CC p) (EE p).
Proof.
  intros; destructP.
  eapply L11; eauto.
  eapply T1; eauto.
Qed.

Lemma program_Pclk_nocyc :
  forall p,
    WellFormed p ->
    Pclk_nocyc (KK p) (CC p).
Proof.
  intros; destructP.
  eapply T0; eauto.
Qed.

Lemma program_Pclk_bool :
  forall p,
    WellFormed p ->
    Pclk_bool (TT p) (CC p).
Proof.
  intros; destructP.
  eapply T9; eauto.
  eapply L13; eauto.
Qed.

Lemma program_Pclk_boolE :
  forall p,
    WellFormed p ->
    Pclk_boolE (TT p) (CC p).
Proof.
  intros; destructP.
  eapply T9; eauto.
  eapply L13; eauto.
Qed.

Lemma program_Pclk_var :
  forall p,
    WellFormed p ->
    Pclk_var (KK p) (CC p).
Proof.
  intros.
  assert (HH := program_Pclk_bool p H).
  destructP.

  unfold Pclk_bool, Pclk_var in *.
  intros; specialize (HH x x'); simpl'.
  kind_consistent.
Qed.

Lemma program_Pclk_varE :
  forall p,
    WellFormed p ->
    Pclk_varE (KK p) (TT p) (CC p).
Proof.
  intros.
  assert (HH := program_Pclk_boolE p H).
  destructP.

  unfold Pclk_boolE, Pclk_varE in *.
  intros; specialize (HH e x'); simpl'.
  kind_consistent.
Qed.

(** ** Second Category: semantics level properties *)

Lemma program_PdeterminismE :
  forall p I n,
    WellFormed p ->
    ValidInput p n I ->
    PdeterminismE (EE p) I.
Proof.
  intros.
  destruct H; destruct H0.
  eapply T8; eauto.
Qed.

Lemma program_Pdeterminism :
  forall p I n,
    WellFormed p ->
    ValidInput p n I ->
    Pdeterminism (EE p) I.
Proof.
  intros.
  destruct H; destruct H0.
  eapply T8; eauto.
Qed.

Lemma program_PdeterminismP :
  forall p I n,
    WellFormed p ->
    ValidInput p n I ->
    PdeterminismP (EE p) I.
Proof.
  intros.
  destruct H; destruct H0.
  eapply T8; eauto.
Qed.

Lemma program_Pexistence :
  forall p I n,
    WellFormed p ->
    ValidInput p n I ->
    Pexistence (KK p) (EE p) I n.
Proof.
  intros.
  destruct H; destruct H0.
  eapply T6; eauto.
  - eapply T8; eauto.
  - eapply T2; eauto.
  - eapply T2; eauto.
  - eapply T3; eauto.
  - eapply T3; eauto.
  - eapply T1; eauto.
Qed.

Lemma program_PexistenceE :
  forall p I n,
    WellFormed p ->
    ValidInput p n I ->
    PexistenceE (TT p) (CC p) (EE p) I n.
Proof.
  intros. destruct H; destruct H0.

  eapply T7; eauto.
  - eapply T8; eauto.
  - eapply T2; eauto.
  - eapply T2; eauto.
  - eapply T3; eauto.
  - eapply T3; eauto.
  - eapply T1; eauto.
Qed.

Lemma program_Pgood_val_c :
  forall p I n,
    WellFormed p ->
    ValidInput p n I ->
    Pgood_val_c (CC p) (EE p) I.
Proof.
  intros.
  destruct H; destruct H0.

  eapply T3; eauto.
Qed.

Lemma program_Pgood_val_cE :
  forall p I n,
    WellFormed p ->
    ValidInput p n I ->
    Pgood_val_cE (TT p) (CC p) (EE p) I.
Proof.
  intros.
  destruct H; destruct H0.

  eapply T3; eauto.
Qed.

Lemma program_eval_in :
  forall p I n,
    WellFormed p ->
    ValidInput p n I ->
    forall x i v,
      evalX (EE p) I x i v ->
      M.In x (KK p).
Proof.
  intros. destruct H; destruct H0.

  inversion H1.
  + kind_consistent.
  + kind_consistent.
Qed.

Lemma program_out_nth :
  forall p n I O,
    WellFormed p ->
    ValidInput p n I ->
    ProgramEval p n I O ->
    forall x s i v,
      i < n ->
      evalX (EE p) I x i v ->
      M.MapsTo x s O ->
      List.nth_error s i = Some v.
Proof.
  intros.

  assert (length s = n).
    destruct H1. eauto.

  assert (HH: exists v', List.nth_error s i = Some v').
    apply list_nth_some. omega.
  destruct HH as [v' HH].

  assert (HH2: evalX (EE p) I x i v').
    destruct H1. eauto.

  assert (v = v').
    eapply program_Pdeterminism; eauto.

  congruence.
Qed.

(** ** Third Category: whole program properties *)

Theorem program_unique :
  forall p n I O1 O2,
    WellFormed p ->
    ValidInput p n I ->
    ProgramEval p n I O1 ->
    ProgramEval p n I O2 ->
    M.Equal O1 O2.
Proof.
  intros.
  inversion H1; inversion H2; subst; clear H1 H2.

  apply map_Equal_0.
  + intro.
    rewrite <- H3.
    rewrite <- H10.
    reflexivity.

  + intros x s1 s2 ? ?.

    specialize (H3 x).
    specialize (H4 x s1).
    specialize (H5 x s1).
    specialize (H10 x).
    specialize (H11 x s2).
    specialize (H12 x s2).

    simpl'.

    apply list_nth_eq. intros.

    assert (HH2: i < n \/ n <= i) by omega.
    destruct HH2.
    - assert (HH3: exists v1, nth_error s1 i = Some v1) by (apply list_nth_some; omega).
      assert (HH4: exists v2, nth_error s2 i = Some v2) by (apply list_nth_some; omega).
      destruct HH3 as [v1 HH3].
      destruct HH4 as [v2 HH4].

      specialize (H5 i v1).
      specialize (H12 i v2).
      simpl'.

      assert (v1 = v2).
        destruct H.
        destruct H0.
        eapply T8; eauto.

      congruence.

    - assert (nth_error s1 i = None) by (apply list_nth_none; omega).
      assert (nth_error s2 i = None) by (apply list_nth_none; omega).

      congruence.
Qed.

Theorem program_exist :
  forall p n I,
    WellFormed p ->
    ValidInput p n I ->
    exists O,
      ProgramEval p n I O.
Proof.
  intros.

  destruct map_exist with
    (P := fun x s =>
            length s = n /\
            ( forall i v,
                nth_error s i = Some v ->
                evalX (EE p) I x i v ) )
    (Q := fun k => k = Kout )
    (mm := KK p) as [ O [ HO1 HO2 ]].
  + decide equality.
  + intros. subst b.
    apply list_exist.
    intros. eapply program_Pexistence; eauto.
  + exists O.
    constructor.
    - intros. rewrite <- HO1.
      split; intros; destruct_ex; simpl'; [ eauto | congruence ].
    - apply HO2.
    - intros. revert i v H2. apply HO2.
      assumption.
Qed.

Theorem program_valid :
  forall p n I O,
    WellFormed p ->
    ValidInput p n I ->
    ProgramEval p n I O ->
    ValidOutput p n I O.
Proof.
  intros.
  constructor.
  + destruct H1. intro. symmetry. trivial.
  + destruct H1. intros ? ? ?. symmetry. eauto.
  + destruct p; eapply T10; eauto.
    destructP; eapply T2; eauto.
  + destructP; destruct p; simpl in *; eapply T11; eauto.
    eapply T3; eauto.
Qed.

Theorem program_causal :
  forall p n m I1 O1 I2 O2,
    WellFormed p ->
    ValidInput p n I1 ->
    ValidInput p m I2 ->
    ProgramEval p n I1 O1 ->
    ProgramEval p m I2 O2 ->
    n <= m ->
    Extend I1 I2 ->
    Extend O1 O2.
Proof.
  intros.
  unfold Extend. intros.

  assert (length s1 <= length s2).
    destruct H2. destruct H3.
    erewrite H9; eauto.
    erewrite H11; eauto.

  assert (HH: i < length s2).
    assert (i < length s1) by (eapply list_nth_some'; eauto).
    omega.

  assert (HH2:= list_nth_some _ s2 i HH).
  destruct HH2 as [ v' HH2 ].

  assert (evalX (EE p) I1 x i v).
    destruct H2. eauto.
  
  assert (evalX (EE p) I2 x i v').
    destruct H3. eauto.

  assert (v = v').
    eapply extend_0 with (I1:=I1) (I2:=I2); eauto.

  congruence.
Qed.
  

Hint Resolve
   ValidInput_lt
   program_PnocycE
   program_Pnocyc_strong
   program_Pnocyc_strongE
   program_Pclk_nocyc
   program_Pclk_bool
   program_Pclk_boolE
   program_Pclk_var
   program_Pclk_varE
   program_PdeterminismE
   program_Pdeterminism
   program_PdeterminismP
   program_Pexistence
   program_PexistenceE
   program_Pgood_val_c
   program_Pgood_val_cE
   program_eval_in
   program_unique
   program_exist : program.
  
Ltac program_trivial :=
  solve [ eapply ValidInput_lt; eauto
        | eapply program_PnocycE; eauto
        | eapply program_Pnocyc_strong; eauto
        | eapply program_Pnocyc_strongE; eauto
        | eapply program_Pclk_nocyc; eauto
        | eapply program_Pclk_bool; eauto
        | eapply program_Pclk_boolE; eauto
        | eapply program_Pclk_var; eauto
        | eapply program_Pclk_varE; eauto
        | eapply program_PdeterminismE; eauto
        | eapply program_Pdeterminism; eauto
        | eapply program_PdeterminismP; eauto
        | eapply program_Pexistence; eauto
        | eapply program_PexistenceE; eauto
        | eapply program_Pgood_val_c; eauto
        | eapply program_Pgood_val_cE; eauto
        | eapply program_eval_in; eauto
        | eapply program_unique; eauto
        | eapply program_exist; eauto ].

(** * Some Lemmas *)
(** Properties in the style of looking back in history *)
Lemma evalP_prev_0 :
  forall E I e i ui,
    ( forall j, j < i -> eval E I e j Vbot ) ->
    evalP E I e i ui ui.
Proof.
  intros.

  induction i.

  (* 0th instance *)
  constructor.

  (* (i+1)th instance *)
  simpl'.
  eapply RPpull; eauto.
Qed.

Lemma evalP_prev_1 :
  forall E I e i j ui u,
    j < i ->
    eval E I e j [u] ->
    ( forall k, j < k < i -> eval E I e k Vbot ) ->
    evalP E I e i ui u.
Proof.
  intros.

  induction i.

  (* 0th instance *)
  omega.

  (* (i+1)th instance *)
  assert (HH: j = i \/ j < i).
    omega.
  clear H. destruct HH.

    (* j = i *)
  subst.
  eapply RPval; eauto.

    (* j < i *)
  simpl'.
  eapply RPpull; eauto.
  apply IHi.
  intros. apply H1.
  omega.
Qed.

Lemma prev_0 :
  forall E I e i,
    ( forall j, j < i -> exists v, eval E I e j v ) ->
    ( forall j, j < i -> eval E I e j Vbot) \/
    ( exists j, exists u, ( j < i /\
                            eval E I e j [u] /\
                            ( forall k, j < k < i -> eval E I e k Vbot ) ) ).
Proof.
  intros.
  induction i.

  (* 0th instance *)
  left. intros. omega.

  (* (i+1)th instance *)
  assert (exists v, eval E I e i v).
    eauto.
  assert (forall j, j < i -> exists v, eval E I e j v).
    eauto.
  clear H. simpl'.

  destruct IHi;
  destruct H0 as [[u | ] H0].

    (* 1st case *)
  right. exists i. exists u.
  split; [ omega | ].
  split; [ eauto | ].
  intros; omega.

    (* 2nd case *)
  left.
  intros.
  assert (HH: j < i \/ j = i).
    omega.
  destruct HH; subst; eauto.

    (* 3rd case *)
  right. exists i. exists u.
  split; [ omega | ].
  split; [ eauto | ].
  intros; omega.
  
    (* 4th case *)
  destruct H as [j [u [ HH1 [ HH2 HH3 ] ] ] ].
  right. exists j. exists u.
  split; [ omega | ].
  split; [ eauto | ].
  intros.
  assert (HH: j < k < i \/ k = i).
    omega.
  destruct HH; subst; eauto.
Qed.

(** The relation of clocks respecting to sampling is well-founded in
a well-formed program *)
Definition clk_dep (p : Program) (ca cb : clock) :=
  exists x,
    cb = Some x /\
    M.MapsTo x ca (CC p).

Lemma clk_dep_0 :
  forall p,
    WellFormed p ->
    well_founded (clk_dep p).
Proof.
  intros p HHp.
  unfold well_founded; intro cb.
  constructor.
  intros ca H.

  unfold clk_dep in H.
  destruct cb.

  + destruct H. simpl'. subst.

    destruct ca as [ x' | ].
    - assert (HH1 : Pclk_nocyc (KK p) (CC p)) by eauto with program.
      unfold Pclk_nocyc in HH1.

      assert (M.In x (KK p)) by kind_consistent.
      assert (Pclk_var (KK p) (CC p)) by eauto with program.
      specialize (H1 x x').
      specialize (HH1 x').
      simpl'.

      clear H H0 H1.
      induction HH1.
      * constructor. intros.
        constructor. intros.
        destruct H0. destruct H1.
        simpl'. subst.
        map_trivial.
      * constructor. intros.
        destruct H0. simpl'. subst.
        map_trivial.

    - constructor. intros.
      destruct H; simpl'; discriminate.

  + constructor. intros.
    destruct H; simpl'; discriminate.
Qed.
