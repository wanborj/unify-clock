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


Require Import Common SingleNode ClockUnify ClockUnifyImpl ClockUnifyProof.
Require Import ZArith.

(** A few examples to test with the transformation and the static checker *)

Module Example1.
  (*
     input : x1

     x2 = (1 when x1) fby (x2 + (1 when x1))
     x3 = curr x2 0
  *)

  Definition E := M.add 2 (Efby ( Ewhen (Econst (Vz (1%Z)) Tz None)
                                        1
                                        Tz (Some 1) )
                                ( Edata2 Oplus (Evar 2 Tz (Some 1))
                                         ( Ewhen (Econst (Vz (1%Z)) Tz None)
                                                 1
                                                 Tz (Some 1) )
                                         Tz (Some 1) )
                                Tz (Some 1) ) (
                  M.add 3 (Ecurr (Evar 2 Tz (Some 1)) 1 (Vz (0%Z)) Tz None) (
                  M.empty _ )).

  Definition K := M.add 1 Kin (
                  M.add 2 Kloc (
                  M.add 3 Kout (
                  M.empty _ ))).

  Definition T := M.add 1 Tbool (
                  M.add 2 Tz (
                  M.add 3 Tz (
                  M.empty _ ))).

  Definition C := M.add 1 None (
                  M.add 2 (Some 1) (
                  M.add 3 None (
                  M.empty _ ))).

  Definition p := mkProgram K T C E.

  Require Import List.
  Import ListNotations.
  Definition I := M.add 1 [ V ( Vbool false );
                            V ( Vbool true  );
                            V ( Vbool false );
                            V ( Vbool false );
                            V ( Vbool true  );
                            V ( Vbool false ) ] (M.empty _ ).

  Lemma nth_error_1 :
    forall A i,
      nth_error nil i = @None A.
  Proof.
    intros.
    destruct i; reflexivity.
  Qed.

  Lemma VI : ValidInput p 6 I.
  Proof.
    constructor.
    + unfold PconsistentI, p. intros; simpl.
      unfold I, K; split; intros;
      repeat map_trivial.

    + unfold Pinp_long.
      intros.
      unfold I in H. repeat map_trivial.

    + unfold Pgood_io_val_t, p. intros; simpl in *.
      unfold I in H;
      repeat map_trivial.

      assert (M.MapsTo 1 Tbool T) by (unfold T; repeat map_trivial).
      repeat map_trivial.

      repeat ( destruct i;
               [ simpl in H1; injection H1; intro; subst; auto with constr | ]).

      simpl in H1.
      rewrite nth_error_1 in H1.
      discriminate.

    + unfold Pgood_io_val_c, p. intros; simpl in *.
      unfold I in H;
      repeat map_trivial.

      assert (M.MapsTo 1 None C) by (unfold C; repeat map_trivial).
      repeat map_trivial.

      repeat ( destruct i;
               [ simpl in H1; injection H1; intro; subst; auto with constr | ]).

      simpl in H1.
      rewrite nth_error_1 in H1.
      discriminate.
  Qed.

  Definition Iq := I.

  Import Refinement.

  Lemma RF : Refinement.refining T I Iq.
  Proof.
    constructor.
    + unfold PM_keys.
      intros; split;
      unfold Iq, I; intro; repeat map_trivial.

    + unfold PM_lens.
      intros.
      unfold Iq in H0.

      repeat map_trivial.

    + unfold PM_on.
      intros.
      unfold Iq in H0.

      map_trivial.

    + unfold Pgood_io_val_t, p. intros; simpl in *.
      unfold Iq, I in H;
      repeat map_trivial.

      assert (M.MapsTo 1 Tbool T) by (unfold T; repeat map_trivial).
      repeat map_trivial.

      repeat ( destruct i;
               [ simpl in H1; injection H1; intro; subst; auto with constr | ]).

      simpl in H1.
      rewrite nth_error_1 in H1.
      discriminate.

    + unfold Pgood_io_val_c', p. intros; simpl in *.
      unfold Iq, I in H;
      repeat map_trivial.

      repeat ( destruct i; [ subst; injection H0; eauto | ] ).

      simpl in H0.
      rewrite nth_error_1 in H0.
      discriminate.
  Qed.
End Example1.

Definition eTrue := Econst (Vbool true) Tbool None.
Definition eZero := Econst (Vz (0%Z)) Tz None.
Definition eNot e := Edata1 Onot e Tbool (clockof e).
Definition eFby ea eb := Efby ea eb (typeof ea) (clockof ea).
Definition eWhen e x := Ewhen e x (typeof e) (Some x).
Definition eCurr e x u c := Ecurr e x u (typeof e) c.
Definition ePlus ea eb := Edata2 Oplus ea eb (typeof ea) (clockof ea).
Definition uZero := Vz (0%Z).
Definition uFour := Vz (4%Z).
Definition eOne := Econst (Vz (1%Z)) Tz None.
Definition eTwo := Econst (Vz (2%Z)) Tz None.
Definition eThree := Econst (Vz (3%Z)) Tz None.

Module Example2.
  (*
     The example from Section 1 of the paper, translated into the
     small language as follows (by node expansion, and replace the
     temporal operators with our primitives):

input: x1

(c2)   x2 = fby (true, not x2)
(c4)   x3 = fby (when(true, x2), not x3)
(a2)   x4 = when(x1, x2)
(a4)   x5 = when(x4, x3)
(b2)   x6 = fby (when(0, x2), x6) + x4
(b4)   x7 = fby (when(when(0,x2),x3), x7) + x5
(s2)   x8 = curr(x6, x2, 0)
(s4)   x9 = curr(curr(x7,x3,0),x2,0)

  *)

  Definition x1 := Evar 1 Tz None.
  Definition x2 := Evar 2 Tbool None.
  Definition x3 := Evar 3 Tbool (Some 2).
  Definition x4 := Evar 4 Tz (Some 2).
  Definition x5 := Evar 5 Tz (Some 3).
  Definition x6 := Evar 6 Tz (Some 2).
  Definition x7 := Evar 7 Tz (Some 3).
  Definition x8 := Evar 8 Tz None.
  Definition x9 := Evar 9 Tz None.

  Definition E := M.add 2 (eFby eTrue (eNot x2)) (
                  M.add 3 (eFby (eWhen eTrue 2) (eNot x3)) (
                  M.add 4 (eWhen x1 2) (
                  M.add 5 (eWhen x4 3) (
                  M.add 6 (ePlus (eFby (eWhen eZero 2) x6) x4) (
                  M.add 7 (ePlus (eFby (eWhen (eWhen eZero 2) 3) x7) x5) (
                  M.add 8 (eCurr x6 2 uZero None) (
                  M.add 9 (eCurr (eCurr x7 3 uZero (Some 2)) 2 uZero None) (
                  M.empty _ )))))))).

  Definition K := M.add 1 Kin (
                  M.add 2 Kloc (
                  M.add 3 Kloc (
                  M.add 4 Kloc (
                  M.add 5 Kloc (
                  M.add 6 Kloc (
                  M.add 7 Kloc (
                  M.add 8 Kout (
                  M.add 9 Kout (
                  M.empty _ ))))))))).

  Definition T := M.add 1 Tz (
                  M.add 2 Tbool (
                  M.add 3 Tbool (
                  M.add 4 Tz (
                  M.add 5 Tz (
                  M.add 6 Tz (
                  M.add 7 Tz (
                  M.add 8 Tz (
                  M.add 9 Tz (
                  M.empty _ ))))))))).

  Definition C := M.add 1 None (
                  M.add 2 None (
                  M.add 3 (Some 2) (
                  M.add 4 (Some 2) (
                  M.add 5 (Some 3) (
                  M.add 6 (Some 2) (
                  M.add 7 (Some 3) (
                  M.add 8 None (
                  M.add 9 None (
                  M.empty _ ))))))))).

  Definition p := mkProgram K T C E.

End Example2.

Module Example3.
  Definition x1 := Evar 1 Tz None.
  Definition x2 := Evar 2 Tbool None.
  Definition x3 := Evar 3 Tz (Some 2).
  Definition x4 := Evar 4 Tz None.

  Definition E := M.add 2 (Edata2 Ogt x1 eZero Tbool None) (
                  M.add 3 (eFby (eWhen eThree 2)
                                (eFby (eWhen eTwo 2)
                                      (eFby (eWhen eOne 2)
                                            (eWhen eZero 2)))) (
                  M.add 4 (eCurr x3 2 uFour None) (
                  M.empty _ ))).

  Definition K := M.add 1 Kin (
                  M.add 2 Kloc (
                  M.add 3 Kloc (
                  M.add 4 Kout (
                  M.empty _ )))).

  Definition T := M.add 1 Tz (
                  M.add 2 Tbool (
                  M.add 3 Tz (
                  M.add 4 Tz (
                  M.empty _ )))).

  Definition C := M.add 1 None (
                  M.add 2 None (
                  M.add 3 (Some 2) (
                  M.add 4 None (
                  M.empty _ )))).

  Definition p := mkProgram K T C E.
End Example3.

Module Example4.
  Definition x1 := Evar 1 Tz None.
  Definition x2 := Evar 2 Tbool None.
  Definition x3 := Evar 3 Tz (Some 2).
  Definition x4 := Evar 4 Tz None.
  Definition x5 := Evar 5 Tz (Some 2).

  Definition E := M.add 2 (Edata2 Ogt x1 eZero Tbool None) (
                  M.add 3 (ePlus x5 (ePlus x5 (ePlus x5 (ePlus x5 x5)))) (
                  M.add 4 (eCurr x3 2 uFour None) (
                  M.add 5 (eWhen x1 2) (
                  M.empty _ )))).

  Definition K := M.add 1 Kin (
                  M.add 2 Kloc (
                  M.add 3 Kloc (
                  M.add 4 Kout (
                  M.add 5 Kloc (
                  M.empty _ ))))).

  Definition T := M.add 1 Tz (
                  M.add 2 Tbool (
                  M.add 3 Tz (
                  M.add 4 Tz (
                  M.add 5 Tz (
                  M.empty _ ))))).

  Definition C := M.add 1 None (
                  M.add 2 None (
                  M.add 3 (Some 2) (
                  M.add 4 None (
                  M.add 5 (Some 2) (
                  M.empty _ ))))).

  Definition p := mkProgram K T C E.
End Example4.

(** Cyclic definition *)
Module Example5.
  Definition x1 := Evar 1 Tz None.
  Definition x2 := Evar 2 Tz None.
  Definition x3 := Evar 3 Tz None.

  Definition E := M.add 1 x2 (
                  M.add 2 x3 (
                  M.add 3 x1 (
                  M.empty _ ))).

  Definition K := M.add 1 Kloc (
                  M.add 2 Kloc (
                  M.add 3 Kloc (
                  M.empty _ ))).

  Definition T := M.add 1 Tz (
                  M.add 2 Tz (
                  M.add 3 Tz (
                  M.empty _ ))).

  Definition C := M.add 1 None (
                  M.add 2 None (
                  M.add 3 None (
                  M.empty _ ))) : Eclk.

  Definition p := mkProgram K T C E.
End Example5.

Require Import Decidable.

Require Import List.
Import ListNotations.

Definition to_list A (x: option A): list A :=
  match x with
    | None => []
    | Some x' => [x']
  end.

Arguments to_list [A] x.

(** The result program can be transformed again (for fun) *)
Definition example6 := translate_failable Example4.p.
Definition example7 :=
  match example6 with
    | None => None
    | Some p => translate_failable p
  end.

Require Import ExtrOcamlBasic.
(* We convert [positive] and [Z] to OCaml's [int], which is enough here *)
Require Import ExtrOcamlIntConv.

(** Add more examples here: *)
Definition AllExamples : list Program
  := [ Example1.p; Example2.p; Example3.p; Example4.p; Example5.p ]
     (* ++ to_list (example6) *) (* the result is long *)
     (* ++ to_list (example7) *) (* the result is long *)
  .

Definition AllExampleResults : list (Program * option Program) :=
  map (fun p => (p, translate_failable p)) AllExamples.

Extraction "Results.ml" AllExampleResults int_of_pos int_of_z.
