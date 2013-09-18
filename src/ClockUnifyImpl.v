(*
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
Require Import BinInt BinPos.
Require Import Program.

(** A implementation algorithm that conforms to the specification. Now the
program is ugly: we explicitly manipulate states. It is better to use a do
notation in the future. *)

(* The 19*7 Obligations for state invariant preservation are all manually
proved for now. It is better to automate them. *)

Module ArbitraryValue.
  Definition arb_value (t:type) : val :=
    match t with
      | Tbool => Vbool false
      | Tz    => Vz Z0
    end.

  Lemma arb_value_0 :
    forall t,
      well_type_val (arb_value t) t.
  Proof.
    destruct t; constructor.
  Qed.
End ArbitraryValue.

Open Scope positive_scope.

Module TranslationImpl <: Translation.
  Opaque Pos.add Pos.mul.

  Section Impl.
    Variables p : Program.
    Hypothesis WF : WellFormed p.

    Notation trans'  := (trans  p).
    Notation transC' := (transC p).
    Notation transR' := (transR p).
    Notation transF' := (transF p).

    Notation well_typeP := (well_type (TT p) (CC p)).

    Lemma transC_add_0 :
      forall c xc q x' k' e' t' c',
        transC' q c xc ->
        ~ M.In x' (EE q) ->
        transC' {| KK := M.add x' k' (KK q);
                   EE := M.add x' e' (EE q);
                   CC := M.add x' c' (CC q);
                   TT := M.add x' t' (TT q) |} c xc.
    Proof.
      intros until c'. intro H.
      induction H.
      + constructor. simpl.
        assert (M.In x (EE q)) by eauto.
        map_trivial.
      + constructor 2 with (xc:=xc) (c:=c).
        * assumption.
        * auto.
        * simpl.

          assert (M.In xc' (EE q)) by eauto.
          map_trivial.
    Qed.

    Lemma transC_add_1 :
      forall c xc q x' k' t' c',
        transC' q c xc ->
        transC' {| KK := M.add x' k' (KK q);
                   EE := EE q;
                   CC := M.add x' c' (CC q);
                   TT := M.add x' t' (TT q) |} c xc.
    Proof.
      intros until c'. intro H.
      induction H.
      + constructor. simpl.
        assumption.
      + constructor 2 with (xc:=xc) (c:=c).
        * assumption.
        * assumption.
        * simpl.
          assumption.
    Qed.

    Lemma transR_add_0 :
      forall eq xc ui xr q x' k' e' t' c',
        transR' q eq xc ui xr ->
        (~ M.In x' (EE q)) ->
        transR' {| KK := M.add x' k' (KK q);
                   EE := M.add x' e' (EE q);
                   CC := M.add x' c' (CC q);
                   TT := M.add x' t' (TT q) |} eq xc ui xr.
    Proof.
      intros.
      inversion H; clear H; subst.
      constructor. simpl.

      assert (M.In xr (EE q)) by eauto.
      map_trivial.
    Qed.

    Lemma transR_add_1 :
      forall eq xc ui xr q x' k' t' c',
        transR' q eq xc ui xr ->
        transR' {| KK := M.add x' k' (KK q);
                   EE := EE q;
                   CC := M.add x' c' (CC q);
                   TT := M.add x' t' (TT q) |} eq xc ui xr.
    Proof.
      intros.
      inversion H; clear H; subst.
      constructor. simpl.
      assumption.
    Qed.

    Lemma transF_add_0 :
      forall x xf q x' k' e' t' c',
        transF' q x xf ->
        (~ M.In x' (EE q)) ->
        transF' {| KK := M.add x' k' (KK q);
                   EE := M.add x' e' (EE q);
                   CC := M.add x' c' (CC q);
                   TT := M.add x' t' (TT q) |} x xf.
    Proof.
      intros.
      inversion H; clear H; subst.
      constructor. simpl.

      assert (M.In xf (EE q)) by eauto.
      map_trivial.
    Qed.

    Lemma transF_add_1 :
      forall x xf q x' k' t' c',
        transF' q x xf ->
        transF' {| KK := M.add x' k' (KK q);
                   EE := EE q;
                   CC := M.add x' c' (CC q);
                   TT := M.add x' t' (TT q) |} x xf.
    Proof.
      intros.
      inversion H; clear H; subst.
      constructor. simpl.
      assumption.
    Qed.

    Lemma trans_add_0 :
      forall ep eq q x' k' e' t' c',
        trans' q ep eq ->
        (~ M.In x' (EE q)) ->
        trans' {| KK := M.add x' k' (KK q);
                  EE := M.add x' e' (EE q);
                  CC := M.add x' c' (CC q);
                  TT := M.add x' t' (TT q) |} ep eq.
    Proof.
      intros.
      induction H; eauto with constr.

      + apply TRvar with (xc:=xc) (ui:=ui).
        * apply transR_add_0; assumption.
        * apply transC_add_0; assumption.

      + apply TRwhen with (eq:=eq) (xc:=xc) (ui:=ui).
        * assumption.
        * apply transR_add_0; assumption.
        * apply transC_add_0; assumption.

      + apply TRcurr with (eq:=eq) (xc:=xc).
        * assumption.
        * apply transR_add_0; assumption.
        * apply transC_add_0; assumption.

      + apply TRfby with (eaq:=eaq) (ebq:=ebq) (xc:=xc) (xf:=xf) (ui:=ui).
        * assumption.
        * assumption.
        * apply transR_add_0; assumption.
        * apply transC_add_0; assumption.
        * apply transF_add_0; assumption.
    Qed.

    Lemma trans_add_1 :
      forall ep eq q x' k' t' c',
        trans' q ep eq ->
        trans' {| KK := M.add x' k' (KK q);
                  EE := EE q;
                  CC := M.add x' c' (CC q);
                  TT := M.add x' t' (TT q) |} ep eq.
    Proof.
      intros.
      induction H; eauto with constr.

      + apply TRvar with (xc:=xc) (ui:=ui).
        * apply transR_add_1; assumption.
        * apply transC_add_1; assumption.

      + apply TRwhen with (eq:=eq) (xc:=xc) (ui:=ui).
        * assumption.
        * apply transR_add_1. assumption.
        * apply transC_add_1. assumption.

      + apply TRcurr with (eq:=eq) (xc:=xc).
        * assumption.
        * apply transR_add_1. assumption.
        * apply transC_add_1. assumption.

      + apply TRfby with (eaq:=eaq) (ebq:=ebq) (xc:=xc) (xf:=xf) (ui:=ui).
        * assumption.
        * assumption.
        * apply transR_add_1; assumption.
        * apply transC_add_1; assumption.
        * apply transF_add_1; assumption.
    Qed.

    Definition max_ident := M.fold (fun x _ p => Pos.max x p) (KK p) 1.

    Lemma max_ident_0 :
      forall x, M.In x (KK p) -> x <= max_ident.
    Proof.
      apply MP.fold_rec_bis with
        (P := fun k x' => forall x, M.In x k -> x <= x').

      intros.
      assert (M.In x m).
        destruct H1. exists x0. congruence.
      eauto.

      intros.
      map_trivial.

      intros.
      map_trivial.
      + apply Pos.max_le_iff. left. apply Pos.le_refl.
      + apply Pos.max_le_iff. right. auto.
    Qed.

    Definition is_orig      x := x <= max_ident.
    Definition is_xc        x := max_ident < x <= 2*max_ident.
    Definition is_xf        x := 2*max_ident < x <= 3*max_ident.
    Definition is_xcn       x := 3*max_ident + 1 = x.
    Definition is_xfn       x := 3*max_ident + 2 = x.
    Definition is_new       x := 3*max_ident + 2 < x.

    Hint Unfold is_orig is_xc is_xf is_xcn is_xfn is_new : ident.

    Definition ident_xc c :=
      match c with
        | Some x =>   max_ident + x
        | None   => 3*max_ident + 1
      end.

    Definition ident_xf c :=
      match c with
        | Some x => 2*max_ident + x
        | None   => 3*max_ident + 2
      end.

    Lemma le_gt :
      forall a x,
        x <= a \/ a < x.
    Proof.
      intros.
      assert (H := Pos.lt_total a x).
      destruct H; [ | destruct H ].

      + auto.
      + subst. left. apply Pos.le_refl.
      + left. unfold Pos.lt in H. unfold Pos.le. congruence.
    Qed.

    Lemma eq_gt :
      forall a x,
        a < x ->
        a + 1 = x \/
        a + 1 < x.
    Proof.
      intros.

      assert (HH := Pos.lt_total (a+1) x).
      destruct HH as [ HH | HH]; [ | destruct HH ]; auto.

      rewrite Pos.add_1_r in H0.
      apply Pos.lt_succ_r in H0.

      apply Pos.gt_lt_iff in H.
      congruence.
    Qed.

    Lemma disjoint_0 :
      forall x,
        is_orig x \/ is_xc x \/ is_xcn x \/
        is_xf x \/ is_xfn x \/ is_new x.
    Proof.
      intros.

      destruct (le_gt max_ident x);
      destruct (le_gt (2*max_ident) x);
      destruct (le_gt (3*max_ident) x);
      auto 10 with ident.

      destruct (eq_gt (3*max_ident) x); auto with ident.
      destruct (eq_gt (3*max_ident+1) x); auto with ident;

      rewrite <- Pos.add_assoc in H3; auto 30 with ident.
    Qed.

    Lemma is_orig_0 :
      forall x,
        M.In x (KK p) ->
        is_orig x.
    Proof.
      unfold is_orig. intros.
      apply max_ident_0. assumption.
    Qed.

    Lemma is_orig_1 :
      forall x x',
        M.MapsTo x (Some x') (CC p) ->
        is_orig x'.
    Proof.
      intros.
      apply is_orig_0.
      program_trivial.
    Qed.

    Lemma is_xc_0 :
      forall x,
        is_orig x ->
        is_xc (max_ident + x).
    Proof.
      intros; autounfold with ident in *; simpl'; split; pomega.
    Qed.

    Lemma is_xc_1 :
      forall x,
        is_xc x ->
        exists2 x', is_orig x' & x = max_ident+x'.
    Proof.
      intros.

      unfold is_xc in H.
      destruct H.

      apply Pos.lt_iff_add in H.
      destruct H as [x' H].
      exists x'.

      + autounfold with ident. pomega.

      + congruence.
    Qed.

    Lemma is_xf_0 :
      forall x,
        is_orig x ->
        is_xf (2*max_ident + x).
    Proof.
      intros; autounfold with ident in *; simpl'; split; pomega.
    Qed.

    Lemma is_xf_1 :
      forall x,
        is_xf x ->
        exists2 x', is_orig x' & x = 2*max_ident+x'.
    Proof.
      intros.

      unfold is_xf in H.
      destruct H.

      apply Pos.lt_iff_add in H.
      destruct H as [x' H].
      exists x'.

      + autounfold with ident. pomega.

      + congruence.
    Qed.

    Hint Resolve is_orig_0 is_xc_0 is_xf_0 : ident.

    Definition well_typeF (prog : Program) (e : expr) :=
      forall pf,
        ( forall x t, M.MapsTo x t (TT p) -> M.MapsTo x t (TT pf) ) ->
        ( forall x t, M.MapsTo x t (TT prog) -> M.MapsTo x t (TT pf) ) ->
        ( forall x t, M.MapsTo x t (TT pf) -> M.MapsTo x None (CC pf) ) ->
        well_type (TT pf) (CC pf) e.

    Lemma well_type_add_0 :
      forall prog e x' k' t' c' e',
        ~ M.In x' (TT prog) ->
        well_typeF prog e ->
        well_typeF {| KK := M.add x' k' (KK prog);
                      TT := M.add x' t' (TT prog);
                      CC := M.add x' c' (CC prog);
                      EE := M.add x' e' (EE prog) |} e.
    Proof.
      unfold well_typeF; simpl.
      intros.
      apply H0; auto.
      intros.

      assert (M.In x (TT prog)) by eauto.
      apply H2; map_trivial.
    Qed.

    Lemma well_type_add_1 :
      forall prog e x' k' t' c',
        ~ M.In x' (TT prog) ->
        well_typeF prog e ->
        well_typeF {| KK := M.add x' k' (KK prog);
                      TT := M.add x' t' (TT prog);
                      CC := M.add x' c' (CC prog);
                      EE := EE prog |} e.
    Proof.
      unfold well_typeF; simpl.
      intros.
      apply H0; auto.
      intros.

      assert (M.In x (TT prog)) by eauto.
      apply H2; map_trivial.
    Qed.

    Record state :=
      mkState {
        prog : Program;
        nextID : ident;

        consistentT : PconsistentT (KK prog) (TT prog);
        consistentC : PconsistentC (KK prog) (CC prog);
        consistentE : PconsistentE (KK prog) (EE prog);

        well_type_t : Pwell_type_t (TT prog) (EE prog);
        well_type_c : Pwell_type_c (CC prog) (EE prog);

        nextID_a : is_new nextID;
        nextID_b : forall x, M.In x (KK prog) -> x < nextID;

        orig_k : forall x k,
                   is_orig x ->
                   M.MapsTo x k (KK prog) ->
                   M.MapsTo x k (KK p);

        orig_e : forall x ep e,
                   is_orig x ->
                   M.MapsTo x ep (EE p) ->
                   M.MapsTo x e (EE prog) ->
                   trans' prog ep e;

        orig_t : forall x t,
                   is_orig x ->
                   M.MapsTo x t (TT prog) ->
                   M.MapsTo x t (TT p);

        xc_e : forall x,
                 is_orig x ->
                 M.In (ident_xc (Some x)) (KK prog) ->
                 transC' prog (Some x) (ident_xc (Some x));

        xcn_e : M.In (ident_xc None) (KK prog) ->
                transC' prog None (ident_xc None);

        xf_e : forall x,
                 is_orig x ->
                 M.In (ident_xf (Some x)) (KK prog) ->
                 transF' prog (ident_xc (Some x)) (ident_xf (Some x));

        xfn_e : M.In (ident_xf None) (KK prog) ->
                transF' prog (ident_xc None) (ident_xf None);

        new_nocyc : forall x,
                      is_new x ->
                      M.In x (KK prog) ->
                      exists ep, exists eq,
                        well_typeP ep /\
                        trans' prog ep eq /\
                        ( forall K E, nocyc K E eq -> nocycX K E x);

        local_k : forall x k,
                    ~ is_orig x ->
                    M.MapsTo x k (KK prog) ->
                    k = Kloc;

        all_wt : forall x' e,
                   M.MapsTo x' e (EE prog) ->
                   well_typeF prog e;

        all_c : forall x c,
                  M.MapsTo x c (CC prog) ->
                  c = None;

        all_gc : forall x e,
                   M.MapsTo x e (EE prog) ->
                   global_clock_expr e
      }.

    Ltac kind_consistent :=
      try match goal with
        [ s : state |- _ ] =>
          destruct s; simpl in *; destructP; kind_consistent'
      end;
      destructP;
      kind_consistent'.

    Ltac kind_attach x K :=
      progress (
        try (assert (M.MapsTo x Kin K) by kind_consistent);
        try (assert (M.MapsTo x Kout K \/ M.MapsTo x Kloc K) by kind_consistent)
      ) || (
        try (assert (M.In x K) by kind_consistent)
      ).

    Ltac attach_is_orig :=
      iter_tac ( fun H => match type of H with
        | M.In ?x (KK p) => assert (is_orig x) by eauto with ident
        | M.MapsTo ?x ?k (KK p) => assert (is_orig x) by eauto with ident
        | M.MapsTo ?x ?t (TT p) =>
            assert (is_orig x);
            [ assert (M.In x (KK p)); [ kind_consistent | eauto with ident ] | ]
        | _ => idtac
      end ).

    Ltac attach_nextID_new :=
      try match goal with
        [ |- context [ nextID ?s ] ] =>
          assert (is_new (nextID s)); [ destruct s; eauto | ]
      end.

    Ltac attach_ident :=
      attach_is_orig;
      attach_nextID_new.

    Ltac destruct_and :=
      repeat match goal with
        [ H : _ /\ _ |- _ ] => destruct H
      end.

    Ltac auto_ident :=
      attach_ident;
      autounfold with ident in *;
      change ident with positive in *;
      destruct_and;
      pomega.

    Ltac destruct_new_nocyc H :=
      destruct H as [ ep [ eq [ Hwt [ Heq Hnocyc ]]]].

    Ltac state_trivial :=
      match goal with
        [ s : state |- _ ] =>
          destruct s; simpl in *; eauto
      end.

    Lemma state_in :
      forall s x,
        M.MapsTo x Kin (KK (prog s)) ->
        M.MapsTo x Kin (KK p).
    Proof.
      intros.
      assert (HH := disjoint_0 x).
      repeat destruct HH as [ HH0 | HH ];
      try solve [
        assert (~ is_orig x) by auto_ident;
        assert (Kin = Kloc) by state_trivial;
        discriminate ].

      eapply orig_k; eauto.
    Qed.

    Lemma state_out :
      forall s x,
        M.MapsTo x Kout (KK (prog s)) ->
        M.MapsTo x Kout (KK p).
    Proof.
      intros.
      assert (HH := disjoint_0 x).
      repeat destruct HH as [ HH0 | HH ];
      try solve [
        assert (~ is_orig x) by auto_ident;
        assert (Kout = Kloc) by state_trivial;
        discriminate ].

      eapply orig_k; eauto.
    Qed.

    Lemma state_xc_t :
      forall s c,
        ( forall x, c = Some x -> is_orig x ) ->
        M.In (ident_xc c) (KK (prog s)) ->
        M.MapsTo (ident_xc c) Tbool (TT (prog s)).
    Proof.
      intros.
      destruct c as [ x | ].
      + specialize (H x). simpl'.
        assert (HH: transC' (prog s) (Some x) (ident_xc (Some x))) by state_trivial.
        assert (HH2: M.In (ident_xc (Some x)) (TT (prog s))) by kind_consistent.
        destruct HH2 as [t HH2].
        assert (HH3: t = Tbool).
          inversion HH; clear HH; subst.
          destruct s; simpl in *. eapply well_type_t0 in H4.
          eapply H4 in HH2. simpl in HH2. congruence.
        subst. congruence.
      + clear H.
        assert (HH: transC' (prog s) None (ident_xc None)) by state_trivial.
        assert (HH2: M.In (ident_xc None) (TT (prog s))) by kind_consistent.
        destruct HH2 as [t HH2].
        assert (HH3: t = Tbool).
          inversion HH; clear HH; subst.
          destruct s; simpl in *. eapply well_type_t0 in H.
          eapply H in HH2. simpl in HH2. congruence.
        subst. congruence.
    Qed.

    Lemma state_xf_t :
      forall s c,
        ( forall x, c = Some x -> is_orig x ) ->
        M.In (ident_xf c) (KK (prog s)) ->
        M.MapsTo (ident_xf c) Tbool (TT (prog s)).
    Proof.
      intros.
      destruct c as [ x | ].
      + specialize (H x). simpl'.
        assert (HH: transF' (prog s) (ident_xc (Some x)) (ident_xf (Some x)))
          by state_trivial.
        assert (HH2: M.In (ident_xf (Some x)) (TT (prog s))) by kind_consistent.
        destruct HH2 as [t HH2].
        assert (HH3: t = Tbool).
          inversion HH; clear HH; subst.
          destruct s; simpl in *. eapply well_type_t0 in H1.
          eapply H1 in HH2. simpl in HH2. congruence.
        subst. congruence.
      + clear H.
        assert (HH: transF' (prog s) (ident_xc None) (ident_xf None)) by state_trivial.
        assert (HH2: M.In (ident_xf None) (TT (prog s))) by kind_consistent.
        destruct HH2 as [t HH2].
        assert (HH3: t = Tbool).
          inversion HH; clear HH; subst.
          destruct s; simpl in *. eapply well_type_t0 in H.
          eapply H in HH2. simpl in HH2. congruence.
        subst. congruence.
    Qed.

    Lemma state_next_0 :
      forall s,
        ~ M.In (nextID s) (KK (prog s)).
    Proof.
      intros.
      intro.

      assert (nextID s < nextID s).
        destruct s; eauto.

      pomega.
    Qed.

    Lemma state_next_1 :
      forall s,
        ~ M.In (nextID s) (EE (prog s)).
    Proof.
      intros.
      assert (H := state_next_0 s).
      contradict H.
      kind_consistent.
    Qed.

    Lemma state_next_2 :
      forall s,
        ~ M.In (nextID s) (TT (prog s)).
    Proof.
      intros.
      assert (H := state_next_0 s).
      contradict H.
      kind_consistent.
    Qed.
      

    Hint Resolve state_next_0 state_next_1 state_next_2 : ident.

    Program Definition init_state :=
      {| prog   := emptyP;
         nextID := 3*max_ident + 3 |}.
    Solve Obligations using
      program_simpl;
      unfold Pwell_type_t;
      unfold Pwell_type_c;
      repeat split; intros;
      try match goal with
        | [ H: _ \/ _ |- _ ] => destruct H
      end; map_trivial.
    Next Obligation. (* nextID_a *)
      auto_ident.
    Qed.

    Program Definition addvar_in
      ( s : state )
      ( x : ident )
      ( t : type )
      ( Hx : M.MapsTo x Kin (KK p) )
      ( Ht : M.MapsTo x t (TT p) )
      ( Hx_b : ~ M.In x (KK (prog s)) )
    : state :=
      {| prog   := let q := prog s in
                   {| KK := M.add x Kin (KK q);
                      EE := EE q;
                      TT := M.add x t (TT q);
                      CC := M.add x None (CC q) |};
         nextID := nextID s |}.
    Next Obligation. (* consistentT *)
      split; intro; do 2 map_trivial.
      + kind_attach x0 (KK (prog s)).
        map_trivial.
      + kind_consistent.
    Qed.
    Next Obligation. (* consistentC *)
      split; intro; do 2 map_trivial.
      + kind_attach x0 (KK (prog s)).
        map_trivial.
      + kind_consistent.
    Qed.
    Next Obligation. (* consistentE *)
      split; intro.

      + assert (x0 <> x).
          intro. subst x0.
          kind_attach x (KK (prog s)).
          kind_case; contradict Hx_b; eauto.

        kind_attach x0 (KK (prog s)).
        kind_case; [ left | right ];
        map_trivial.

      + kind_case; map_trivial; kind_consistent.
    Qed.
    Next Obligation. (* well_type_t *)
      unfold Pwell_type_t. intros.

      destruct (Pos.eq_dec x0 x).
      + subst x0.
        kind_attach x (KK (prog s)).
        contradict Hx_b.
        kind_case; kind_consistent.
      + map_trivial.
        state_trivial.
    Qed.
    Next Obligation. (* well_type_c *)
      unfold Pwell_type_c. intros.

      destruct (Pos.eq_dec x0 x).
      + subst x0.
        kind_attach x (KK (prog s)).
        contradict Hx_b.
        kind_case; kind_consistent.
      + map_trivial.
        state_trivial.
    Qed.
    Next Obligation. (* nextID_a *)
      state_trivial.
    Qed.
    Next Obligation. (* nextID_b *)
      map_trivial.
      + auto_ident.
      + state_trivial.
    Qed.
    Next Obligation. (* orig_k *)
      destruct (Pos.eq_dec x0 x).
      + subst x0.
        map_trivial.
      + map_trivial.
        state_trivial.
    Qed.
    Next Obligation. (* orig_e *)
      apply trans_add_1.
      state_trivial.
    Qed.
    Next Obligation. (* orig_t *)
      map_trivial.
      state_trivial.
    Qed.
    Next Obligation. (* xc_e *)
      map_trivial.
      + auto_ident.
      + apply transC_add_1.
        state_trivial.
    Qed.
    Next Obligation. (* xcn_e *)
      map_trivial.
      + auto_ident.
      + apply transC_add_1.
        state_trivial.
    Qed.
    Next Obligation. (* xf_e *)
      map_trivial.
      + auto_ident.
      + apply transF_add_1.
        state_trivial.
    Qed.
    Next Obligation. (* xfn_e *)
      map_trivial.
      + auto_ident.
      + apply transF_add_1.
        state_trivial.
    Qed.
    Next Obligation. (* new_nocyc *)
      map_trivial.
      + auto_ident.
      + destruct_new_nocyc (new_nocyc s x0 H H0).
        exists ep eq.
        repeat split; eauto.
        - apply trans_add_1. eauto.
    Qed.
    Next Obligation. (* local_k *)
      map_trivial.
      + contradict H; auto_ident.
      + eapply local_k in H; eauto.
    Qed.
    Next Obligation. (* all_wt *)
      eapply well_type_add_1; eauto.
      + contradict Hx_b.
        kind_consistent.
      + state_trivial.
    Qed.
    Next Obligation. (* all_c *)
      map_trivial.
      state_trivial.
    Qed.
    Next Obligation. (* all_gc *)
      state_trivial.
    Qed.

    Lemma addvar_in_0 :
      forall s x t Hx Ht Hx_b,
        M.In x (KK (prog (addvar_in s x t Hx Ht Hx_b))).
    Proof.
      intros.
      unfold addvar_in. simpl.
      map_trivial.
    Qed.

    Lemma addvar_in_1 :
      forall s x t Hx Ht Hx_b x',
        M.In x' (KK (prog s)) ->
        M.In x' (KK (prog (addvar_in s x t Hx Ht Hx_b))).
    Proof.
      intros.

      destruct (Pos.eq_dec x x').
      + subst.
        simpl. map_trivial.
      + simpl. map_trivial.
    Qed.

    Program Definition addvar_xc
      ( s : state )
      ( x : ident )
      ( c : clock )
      ( Ht : M.MapsTo x Tbool (TT p) )
      ( Hc : M.MapsTo x c (CC p) )
      ( Hc_b : M.In (ident_xc c) (KK (prog s)) )
      ( Hx_b : ~ M.In (ident_xc (Some x)) (KK (prog s)) )
    : state :=
      {| prog   := let q := prog s in
                   let x' := ident_xc (Some x) in
                   {| KK := M.add x' Kloc (KK q);
                      EE := M.add x' (Edata3 Oif
                                             (Evar (ident_xc c) Tbool None)
                                             (Evar x Tbool None)
                                             (Econst (Vbool false) Tbool None)
                                             Tbool
                                             None) (EE q);
                      TT := M.add x' Tbool (TT q);
                      CC := M.add x' None (CC q) |};
         nextID := nextID s |}.
    Next Obligation. (* consistentT *)
      split; intro; do 2 map_trivial.
      + kind_attach x0 (KK (prog s)).
        map_trivial.
      + kind_consistent.
    Qed.
    Next Obligation. (* consistentC *)
      split; intro; do 2 map_trivial.
      + kind_attach x0 (KK (prog s)).
        map_trivial.
      + kind_consistent.
    Qed.
    Next Obligation. (* consistentE *)
      split; intro; map_trivial.

      + right. map_trivial.
      + assert (x0 <> max_ident + x).
          intro; subst x0.
          assert (M.In (max_ident + x) (KK (prog s))) by kind_consistent.
          contradiction.
        kind_attach x0 (KK (prog s)); kind_case;
        [ left | right ]; map_trivial; assumption.

      + kind_case; map_trivial; eauto;
        map_trivial; kind_consistent.
    Qed.
    Next Obligation. (* well_type_t *)
      unfold Pwell_type_t. intros.

      destruct (Pos.eq_dec (max_ident + x) x0).
      + subst.
        map_trivial.
        map_trivial.
      + map_trivial.
        map_trivial.
        state_trivial.
    Qed.
    Next Obligation. (* well_type_c *)
      unfold Pwell_type_c. intros.

      destruct (Pos.eq_dec (max_ident + x) x0).
      + subst.
        map_trivial.
        map_trivial.
      + map_trivial.
        map_trivial.
        state_trivial.
    Qed.
    Next Obligation. (* nextID_a *)
      state_trivial.
    Qed.
    Next Obligation. (* nextID_b *)
      map_trivial.
      + auto_ident.
      + state_trivial.
    Qed.
    Next Obligation. (* orig_k *)
      map_trivial.
      + auto_ident.
      + map_trivial.
        state_trivial.
    Qed.
    Next Obligation. (* orig_e *)
      map_trivial.
      + auto_ident.
      + map_trivial.
        apply trans_add_0.
        * state_trivial.
        * contradict Hx_b.
          kind_consistent.
    Qed.
    Next Obligation. (* orig_t *)
      map_trivial.
      + auto_ident.
      + state_trivial.
    Qed.
    Next Obligation. (* xc_e *)
      map_trivial.
      + assert (x = x0).
          apply Pos.compare_eq_iff.
          rewrite <- Pos.add_compare_mono_l with (p:=max_ident).
          apply Pos.compare_eq_iff.
          assumption.
        subst x0. clear H0 H.

        constructor 2 with (xc:=ident_xc c) (c:=c).
        * assumption.
        * apply transC_add_0.
          - destruct s; simpl in *.
            destruct c as [ x' | ].
              assert (M.In x' (KK p)).
                program_trivial.
              assert (is_orig x').
                apply is_orig_0; assumption.
              eauto.

              auto.
          - contradict Hx_b.
            kind_consistent.
        * simpl. map_trivial.

      + apply transC_add_0.
        - state_trivial.
        - intro.
          assert (M.In (max_ident + x) (KK (prog s))).
            kind_consistent.
          contradiction.
    Qed.
    Next Obligation. (* xcn_e *)
      map_trivial.
      + auto_ident.
      + apply transC_add_0.
        - state_trivial.
        - intro.
          assert (M.In (max_ident + x) (KK (prog s))).
            kind_consistent.
          contradiction.
    Qed.
    Next Obligation. (* xf_e *)
      map_trivial.
      + auto_ident.
      + apply transF_add_0.
        - state_trivial.
        - intro.
          assert (M.In (max_ident + x) (KK (prog s))).
            kind_consistent.
          contradiction.
    Qed.
    Next Obligation. (* xfn_e *)
      map_trivial.
      + auto_ident.
      + apply transF_add_0.
        - state_trivial.
        - intro.
          assert (M.In (max_ident + x) (KK (prog s))).
            kind_consistent.
          contradiction.
    Qed.
    Next Obligation. (* new_nocyc *)
      map_trivial.
      + auto_ident.
      + destruct_new_nocyc (new_nocyc s x0 H H0).
        exists ep eq.
        repeat split; eauto.
        - apply trans_add_0. eauto.
          contradict Hx_b.
          kind_consistent.
    Qed.
    Next Obligation. (* local_k *)
      map_trivial.
      eapply local_k in H; eauto.
    Qed.
    Next Obligation. (* all_wt *)
      apply MF.add_mapsto_iff in H.
      destruct H.
      + simpl'. unfold well_typeF. simpl. subst. intros.

        assert (is_orig x).
          apply is_orig_0.
          kind_consistent.

        assert (M.MapsTo x Tbool (TT pf)).
          apply H.
          assumption.

        assert (M.MapsTo (ident_xc c) Tbool (TT (prog s))).
        { apply state_xc_t.
          - intros. subst.
            eapply is_orig_1; eauto.
          - assumption. }

        assert (M.MapsTo (ident_xc c) Tbool (TT pf)).
        { apply H0.
          map_trivial. }

        assert (M.MapsTo x None (CC pf)) by eauto.
        assert (M.MapsTo (ident_xc c) None (CC pf)) by eauto.

        eauto with constr.

      + simpl'. eapply well_type_add_0; eauto.
        - contradict Hx_b.
          kind_consistent.
        - state_trivial.
    Qed.
    Next Obligation. (* all_c *)
      map_trivial.
      state_trivial.
    Qed.
    Next Obligation. (* all_gc *)
      map_trivial.
      + subst; eauto with constr.
      + state_trivial.
    Qed.

    Lemma addvar_xc_0 :
      forall s x c Ht Hc Hc_b Hx_b,
        M.In (ident_xc (Some x)) (KK (prog (addvar_xc s x c Ht Hc Hc_b Hx_b))).
    Proof.
      intros.

      unfold addvar_xc. simpl.
      map_trivial.
    Qed.

    Lemma addvar_xc_1 :
      forall s x c Ht Hc Hc_b Hx_b x',
        M.In x' (KK (prog s)) ->
        M.In x' (KK (prog (addvar_xc s x c Ht Hc Hc_b Hx_b))).
    Proof.
      intros.
      unfold addvar_xc. simpl.

      destruct (Pos.eq_dec (max_ident + x) x').
      + subst. map_trivial.
      + map_trivial.
    Qed.

    Lemma addvar_xc_2 :
      forall s x c Ht Hc Hc_b Hx_b ep eq,
        trans' (prog s) ep eq ->
        trans' (prog (addvar_xc s x c Ht Hc Hc_b Hx_b)) ep eq.
    Proof.
      intros.
      unfold addvar_xc. simpl.

      apply trans_add_0.
      + assumption.
      + contradict Hx_b.
        kind_consistent.
    Qed.

    Lemma addvar_xc_3 :
      forall s x c Ht Hc Hc_b Hx_b e,
        well_typeF (prog s) e ->
        well_typeF (prog (addvar_xc s x c Ht Hc Hc_b Hx_b)) e.
    Proof.
      intros. apply well_type_add_0.
      * contradict Hx_b.
        kind_consistent.
      * auto.
    Qed.

    Program Definition addvar_xcn
      ( s : state )
      ( Hx : ~ M.In (ident_xc None) (KK (prog s)) )
    : state :=
      {| prog   := let q := prog s in
                   let x := ident_xc None in
                   {| KK := M.add x Kloc (KK q);
                      EE := M.add x (Econst (Vbool true) Tbool None) (EE q);
                      TT := M.add x Tbool (TT q);
                      CC := M.add x None (CC q) |};
         nextID := nextID s |}.
    Next Obligation. (* consistentT  *)
      split; intro; do 2 map_trivial.
      + kind_attach x0 (KK (prog s)).
        map_trivial.
      + kind_consistent.
    Qed.
    Next Obligation. (* consistentC *)
      split; intro; do 2 map_trivial.
      + kind_attach x0 (KK (prog s)).
        map_trivial.
      + kind_consistent.
    Qed.
    Next Obligation. (* consistentE *)
      split; intro; map_trivial.

      + right. map_trivial.
      + assert (x <> 3*max_ident + 1).
          intro; subst x.
          assert (M.In (3*max_ident + 1) (KK (prog s))) by kind_consistent.
          contradiction.
        kind_attach x (KK (prog s)); kind_case;
        [ left | right ]; map_trivial; assumption.

      + kind_case; map_trivial; eauto;
        map_trivial; kind_consistent.
    Qed.
    Next Obligation. (* well_type_t *)
      unfold Pwell_type_t. intros.

      destruct (Pos.eq_dec (3*max_ident + 1) x).
      + subst.
        map_trivial.
        map_trivial.
      + map_trivial.
        map_trivial.
        state_trivial.
    Qed.
    Next Obligation. (* well_type_c *)
      unfold Pwell_type_c. intros.

      destruct (Pos.eq_dec (3*max_ident + 1) x).
      + subst.
        map_trivial.
        map_trivial.
      + map_trivial.
        map_trivial.
        state_trivial.
    Qed.
    Next Obligation. (* nextID_a *)
      state_trivial.
    Qed.
    Next Obligation. (* nextID_b *)
      map_trivial.
      + auto_ident.
      + state_trivial.
    Qed.
    Next Obligation. (* orig_k *)
      map_trivial.
      + auto_ident.
      + map_trivial.
        state_trivial.
    Qed.
    Next Obligation. (* orig_e *)
      map_trivial.
      + auto_ident.
      + map_trivial.
        apply trans_add_0.
        * state_trivial.
        * contradict Hx.
          kind_consistent.
    Qed.
    Next Obligation. (* orig_t *)
      map_trivial.
      + auto_ident.
      + state_trivial.
    Qed.
    Next Obligation. (* xc_e *)
      map_trivial.
      + auto_ident.
      + apply transC_add_0.
        - state_trivial.
        - intro.
          assert (M.In (3*max_ident + 1) (KK (prog s))).
            kind_consistent.
          contradiction.
    Qed.
    Next Obligation. (* xcn_e *)
      map_trivial.
      constructor 1.
      simpl.
      map_trivial.
    Qed.
    Next Obligation. (* xf_e *)
      map_trivial.
      + auto_ident.
      + apply transF_add_0.
        - state_trivial.
        - intro.
          assert (M.In (3*max_ident + 1) (KK (prog s))).
            kind_consistent.
          contradiction.
    Qed.
    Next Obligation. (* xfn_e *)
      map_trivial.
      + auto_ident.
      + apply transF_add_0.
        - state_trivial.
        - intro.
          assert (M.In (3*max_ident + 1) (KK (prog s))).
            kind_consistent.
          contradiction.
    Qed.
    Next Obligation. (* new_nocyc *)
      map_trivial.
      + auto_ident.
      + destruct_new_nocyc (new_nocyc s x H H0).
        exists ep eq.
        repeat split; eauto.
        - apply trans_add_0. eauto.
          contradict Hx.
          kind_consistent.
    Qed.
    Next Obligation. (* local_k *)
      map_trivial.
      eapply local_k in H; eauto.
    Qed.
    Next Obligation. (* all_wt *)
      map_trivial.
      + simpl'. unfold well_typeF. simpl. subst. intros.

        eauto with constr.

      + simpl'. eapply well_type_add_0; eauto.
        - contradict Hx.
          kind_consistent.
        - state_trivial.
    Qed.
    Next Obligation. (* all_c *)
      map_trivial.
      state_trivial.
    Qed.
    Next Obligation. (* all_gc *)
      map_trivial.
      + subst; eauto with constr.
      + state_trivial.
    Qed.
 
    Lemma addvar_xcn_0 :
      forall s Hx,
        M.In (ident_xc None) (KK (prog (addvar_xcn s Hx))).
    Proof.
      intros.

      unfold addvar_xcn. simpl.
      map_trivial.
    Qed.

    Lemma addvar_xcn_1 :
      forall s Hx x,
        M.In x (KK (prog s)) ->
        M.In x (KK (prog (addvar_xcn s Hx))).
    Proof.
      intros.
      unfold addvar_xcn. simpl.

      destruct (Pos.eq_dec (3*max_ident + 1) x).
      + subst. simpl. map_trivial.
      + map_trivial.
    Qed.

    Lemma addvar_xcn_2 :
      forall s Hx ep eq,
        trans' (prog s) ep eq ->
        trans' (prog (addvar_xcn s Hx)) ep eq.
    Proof.
      intros.
      unfold addvar_xcn. simpl.

      apply trans_add_0.
      + assumption.
      + contradict Hx.
        kind_consistent.
    Qed.

    Program Definition addvar_xf
      ( s : state )
      ( x : ident )
      ( Hxc : M.In (ident_xc (Some x)) (KK (prog s)) )
      ( Hx : M.In x (KK p) )
      ( Hx_b : ~ M.In (ident_xf (Some x)) (KK (prog s)) )
    : state :=
      {| prog   := let q := prog s in
                   let x' := ident_xf (Some x) in
                   {| KK := M.add x' Kloc (KK q);
                      EE := M.add x' (Efby (Econst (Vbool true) Tbool None)
                                           (Edata3 Oif
                                                   (Evar (ident_xc (Some x)) Tbool None)
                                                   (Econst (Vbool false) Tbool None)
                                                   (Evar x' Tbool None)
                                                   Tbool
                                                   None)
                                           Tbool
                                           None) (EE q);
                      TT := M.add x' Tbool (TT q);
                      CC := M.add x' None (CC q) |};
         nextID := nextID s |}.
    Next Obligation. (* consistentT *)
      split; intro; do 2 map_trivial.
      + kind_attach x0 (KK (prog s)).
        map_trivial.
      + kind_consistent.
    Qed.
    Next Obligation. (* consistentC *)
      split; intro; do 2 map_trivial.
      + kind_attach x0 (KK (prog s)).
        map_trivial.
      + kind_consistent.
    Qed.
    Next Obligation. (* consistentE *)
      split; intro; map_trivial.

      + right. map_trivial.
      + assert (x0 <> 2*max_ident + x).
          intro; subst x0.
          assert (M.In (2*max_ident + x) (KK (prog s))) by kind_consistent.
          contradiction.
        kind_attach x0 (KK (prog s)); kind_case;
        [ left | right ]; map_trivial; assumption.

      + kind_case; map_trivial; eauto;
        map_trivial; kind_consistent.
    Qed.
    Next Obligation. (* well_type_t *)
      unfold Pwell_type_t. intros.

      destruct (Pos.eq_dec (2*max_ident + x) x0).
      + subst.
        map_trivial.
        map_trivial.
      + map_trivial.
        map_trivial.
        state_trivial.
    Qed.
    Next Obligation. (* well_type_c *)
      unfold Pwell_type_c. intros.

      destruct (Pos.eq_dec (2*max_ident + x) x0).
      + subst.
        map_trivial.
        map_trivial.
      + map_trivial.
        map_trivial.
        state_trivial.
    Qed.
    Next Obligation. (* nextID_a *)
      state_trivial.
    Qed.
    Next Obligation. (* nextID_b *)
      map_trivial.
      + auto_ident.
      + state_trivial.
    Qed.
    Next Obligation. (* orig_k *)
      map_trivial.
      + auto_ident.
      + map_trivial.
        state_trivial.
    Qed.
    Next Obligation. (* orig_e *)
      map_trivial.
      + auto_ident.
      + map_trivial.
        apply trans_add_0.
        * state_trivial.
        * contradict Hx_b.
          kind_consistent.
    Qed.
    Next Obligation. (* orig_t *)
      map_trivial.
      + auto_ident.
      + state_trivial.
    Qed.
    Next Obligation. (* xc_e *)
      map_trivial.
      + auto_ident.
      + apply transC_add_0.
        - state_trivial.
        - intro.
          assert (M.In (2*max_ident + x) (KK (prog s))).
            kind_consistent.
          contradiction.
    Qed.
    Next Obligation. (* xcn_e *)
      map_trivial.
      + auto_ident.
      + apply transC_add_0.
        - state_trivial.
        - intro.
          assert (M.In (2*max_ident + x) (KK (prog s))).
            kind_consistent.
          contradiction.
    Qed.
    Next Obligation. (* xf_e *)
      destruct (Pos.eq_dec (2*max_ident + x0) (2*max_ident+x)).
      + assert (x0 = x).
          eapply Pos.add_reg_l; eauto.
        subst x0.

        constructor.
        * subst. simpl. map_trivial.

      + map_trivial.
        apply transF_add_0.
        - state_trivial.
        - contradict Hx_b.
          kind_consistent.
    Qed.
    Next Obligation. (* xfn_e *)
      map_trivial.
      + auto_ident.
      + apply transF_add_0.
        - state_trivial.
        - contradict Hx_b.
          kind_consistent.
    Qed.
    Next Obligation. (* new_nocyc *)
      map_trivial.
      + auto_ident.
      + destruct_new_nocyc (new_nocyc s x0 H H0).
        exists ep eq.
        repeat split; eauto.
        - apply trans_add_0. eauto.
          contradict Hx_b.
          kind_consistent.
    Qed.
    Next Obligation. (* local_k *)
      map_trivial.
      eapply local_k in H; eauto.
    Qed.
    Next Obligation. (* all_wt *)
      map_trivial.
      + simpl'. unfold well_typeF. simpl. subst. intros.

        assert (M.MapsTo (2*max_ident+x) Tbool (TT pf)).
          apply H0. map_trivial.
        assert (M.MapsTo (max_ident+x) Tbool (TT pf)).
        { apply H0. map_trivial.
          assert (HH: transC' (prog s) (Some x) (max_ident + x)).
            assert (is_orig x).
              apply is_orig_0. assumption.
            destruct s; eauto.
          assert (HH2: M.In (max_ident + x) (TT (prog s))) by kind_consistent.
          destruct HH2 as [t Ht].
          assert (HH3: t = Tbool).
            inversion HH; clear HH; subst.
            destruct s; simpl in *. eapply well_type_t0 in H6.
            eapply H6 in Ht. simpl in Ht. congruence.
          subst. assumption. }

        assert (M.MapsTo (max_ident+x) None (CC pf)) by eauto.
        assert (M.MapsTo (2*max_ident+x) None (CC pf)) by eauto.

        eauto 30 with constr.

      + simpl'. eapply well_type_add_0; eauto.
        - contradict Hx_b.
          kind_consistent.
        - state_trivial.
    Qed.
    Next Obligation. (* all_c *)
      map_trivial.
      state_trivial.
    Qed.
    Next Obligation. (* all_gc *)
      map_trivial.
      + subst; eauto 30 with constr.
      + state_trivial.
    Qed.
 
    Lemma addvar_xf_0 :
      forall s x Hxc Hx Hx_b,
        M.In (ident_xf (Some x)) (KK (prog (addvar_xf s x Hxc Hx Hx_b))).
    Proof.
      intros.
      unfold addvar_xf; simpl.
      map_trivial.
    Qed.

    Lemma addvar_xf_1 :
      forall s x Hxc Hx Hx_b e,
        well_typeF (prog s) e ->
        well_typeF (prog (addvar_xf s x Hxc Hx Hx_b)) e.
    Proof.
      intros.
      unfold addvar_xf; simpl.
      apply well_type_add_0.
      * contradict Hx_b.
        kind_consistent.
      * assumption.
    Qed.

    Program Definition addvar_xfn
      ( s : state )
      ( Hxc : M.In (ident_xc None) (KK (prog s)) )
      ( Hx : ~ M.In (ident_xf None) (KK (prog s)) )
    : state :=
      {| prog   := let q := prog s in
                   let x := ident_xf None in
                   {| KK := M.add x Kloc (KK q);
                      EE := M.add x (Efby (Econst (Vbool true) Tbool None)
                                           (Edata3 Oif
                                                   (Evar (ident_xc None) Tbool None)
                                                   (Econst (Vbool false) Tbool None)
                                                   (Evar x Tbool None)
                                                   Tbool
                                                   None)
                                           Tbool
                                           None) (EE q);
                      TT := M.add x Tbool (TT q);
                      CC := M.add x None (CC q) |};
         nextID := nextID s |}.
    Next Obligation. (* consistentT  *)
      split; intro; do 2 map_trivial.
      + kind_attach x0 (KK (prog s)).
        map_trivial.
      + kind_consistent.
    Qed.
    Next Obligation. (* consistentC *)
      split; intro; do 2 map_trivial.
      + kind_attach x0 (KK (prog s)).
        map_trivial.
      + kind_consistent.
    Qed.
    Next Obligation. (* consistentE *)
      split; intro; map_trivial.

      + right. map_trivial.
      + assert (x <> 3*max_ident + 2).
          intro; subst x.
          assert (M.In (3*max_ident + 2) (KK (prog s))) by kind_consistent.
          contradiction.
        kind_attach x (KK (prog s)); kind_case;
        [ left | right ]; map_trivial; assumption.

      + kind_case; map_trivial; eauto;
        map_trivial; kind_consistent.
    Qed.
    Next Obligation. (* well_type_t *)
      unfold Pwell_type_t. intros.

      destruct (Pos.eq_dec (3*max_ident + 2) x).
      + subst.
        map_trivial.
        map_trivial.
      + map_trivial.
        map_trivial.
        state_trivial.
    Qed.
    Next Obligation. (* well_type_c *)
      unfold Pwell_type_c. intros.

      destruct (Pos.eq_dec (3*max_ident + 2) x).
      + subst.
        map_trivial.
        map_trivial.
      + map_trivial.
        map_trivial.
        state_trivial.
    Qed.
    Next Obligation. (* nextID_a *)
      state_trivial.
    Qed.
    Next Obligation. (* nextID_b *)
      map_trivial.
      + auto_ident.
      + state_trivial.
    Qed.
    Next Obligation. (* orig_k *)
      map_trivial.
      + auto_ident.
      + map_trivial.
        state_trivial.
    Qed.
    Next Obligation. (* orig_e *)
      map_trivial.
      + auto_ident.
      + map_trivial.
        apply trans_add_0.
        * state_trivial.
        * contradict Hx.
          kind_consistent.
    Qed.
    Next Obligation. (* orig_t *)
      map_trivial.
      + auto_ident.
      + state_trivial.
    Qed.
    Next Obligation. (* xc_e *)
      map_trivial.
      + auto_ident.
      + apply transC_add_0.
        - state_trivial.
        - intro.
          assert (M.In (3*max_ident + 2) (KK (prog s))).
            kind_consistent.
          contradiction.
    Qed.
    Next Obligation. (* xcn_e *)
      map_trivial.
      apply transC_add_0.
      - state_trivial.
      - intro.
        assert (M.In (3*max_ident + 2) (KK (prog s))).
          kind_consistent.
        contradiction.
    Qed.
    Next Obligation. (* xf_e *)
      map_trivial.
      + auto_ident.
      + apply transF_add_0.
        - state_trivial.
        - intro.
          assert (M.In (3*max_ident + 2) (KK (prog s))).
            kind_consistent.
          contradiction.
    Qed.
    Next Obligation. (* xfn_e *)
      map_trivial.
      constructor.
      simpl.
      map_trivial.
    Qed.
    Next Obligation. (* new_nocyc *)
      map_trivial.
      + auto_ident.
      + destruct_new_nocyc (new_nocyc s x H H0).
        exists ep eq.
        repeat split; eauto.
        - apply trans_add_0. eauto.
          contradict Hx.
          kind_consistent.
    Qed.
    Next Obligation. (* local_k *)
      map_trivial.
      eapply local_k in H; eauto.
    Qed.
    Next Obligation. (* all_wt *)
      map_trivial.
      + simpl'. unfold well_typeF. simpl. subst. intros.

        assert (M.MapsTo (3*max_ident+2) Tbool (TT pf)).
          apply H0. map_trivial.
        assert (M.MapsTo (3*max_ident+1) Tbool (TT pf)).
        { apply H0. apply MF.add_neq_mapsto_iff.
          - auto_ident.
          - assert (HH: transC' (prog s) None (3*max_ident + 1)).
              destruct s; eauto.
            assert (HH2: M.In (3*max_ident + 1) (TT (prog s))) by kind_consistent.
            destruct HH2 as [t Ht].
            assert (HH3: t = Tbool).
              inversion HH; clear HH; subst.
              destruct s; simpl in *. eapply well_type_t0 in H3.
              eapply H3 in Ht. simpl in Ht. congruence.
            subst. assumption. }

        assert (M.MapsTo (3*max_ident+2) None (CC pf)) by eauto.
        assert (M.MapsTo (3*max_ident+1) None (CC pf)) by eauto.

        eauto 30 with constr.

      + simpl'. eapply well_type_add_0; eauto.
        - contradict Hx.
          kind_consistent.
        - state_trivial.
    Qed.
    Next Obligation. (* all_c *)
      map_trivial.
      state_trivial.
    Qed.
    Next Obligation. (* all_gc *)
      map_trivial.
      + subst; eauto 30 with constr.
      + state_trivial.
    Qed.

    Lemma addvar_xfn_0 :
      forall s Hxc Hx,
        M.In (ident_xf None) (KK (prog (addvar_xfn s Hxc Hx))).
    Proof.
      intros.
      unfold addvar_xfn; simpl.
      map_trivial.
    Qed.

    Definition well_typeF' (prog : Program) (e : expr) (x':ident) (t':type) :=
      forall pf,
        ( forall x t, M.MapsTo x t (TT p) -> M.MapsTo x t (TT pf) ) ->
        ( forall x t, M.MapsTo x t (TT prog) -> M.MapsTo x t (TT pf) ) ->
        ( forall x t, M.MapsTo x t (TT pf) -> M.MapsTo x None (CC pf) ) ->
        M.MapsTo x' t' (TT pf) ->
        well_type (TT pf) (CC pf) e.

    Program Definition addvar_new
      ( s : state )
      ( ee : ident -> expr )
      ( Hc : forall x, clockof (ee x) = None )
      ( Hwt : forall x, well_typeF' (prog s) (ee x) x (typeof (ee x)) )
      ( Hnocyc :
          let q := prog s in
          let x := nextID s in
          let t := {| KK := M.add x Kloc (KK q);
                      EE := M.add x (ee x) (EE q);
                      TT := M.add x (typeof (ee x)) (TT q);
                      CC := M.add x None (CC q) |} in
          exists ep, exists ee',
            well_typeP ep /\
            trans' t ep (ee' x) /\
            ( forall K E, nocyc K E (ee' x) -> nocycX K E x) )
      ( Hgc : forall x, global_clock_expr (ee x) )
    : ident * state :=
      ( nextID s, {| prog   := let q := prog s in
                               let x := nextID s in
                               {| KK := M.add x Kloc (KK q);
                                  EE := M.add x (ee x) (EE q);
                                  TT := M.add x (typeof (ee x)) (TT q);
                                  CC := M.add x None (CC q) |};
                     nextID := Pos.succ (nextID s) |} ).
    Obligation Tactic := intros; simpl in *.
    Next Obligation. (* consistentT *)
      split; intro; do 2 map_trivial.
      + kind_attach x0 (KK (prog s)).
        assert (~ M.In (nextID s) (KK (prog s))) by auto with ident.
        map_trivial.
      + assert (~ M.In (nextID s) (KK (prog s))) by auto with ident.
        map_trivial.
        kind_consistent.
    Qed.
    Next Obligation. (* consistentC *)
      split; intro; do 2 map_trivial.
      + kind_attach x0 (KK (prog s)).
        assert (~ M.In (nextID s) (KK (prog s))) by auto with ident.
        map_trivial.
      + assert (~ M.In (nextID s) (KK (prog s))) by auto with ident.
        map_trivial.
        kind_consistent.
    Qed.
    Next Obligation. (* consistentE *)
      split; intro; map_trivial.

      + right. map_trivial.
      + assert (x <> nextID s).
          intro HH. rewrite HH in H.
          assert (M.In (nextID s) (KK (prog s))) by kind_consistent.
          assert (~ M.In (nextID s) (KK (prog s))) by auto with ident.
          contradiction.
        kind_attach x (KK (prog s)); kind_case;
        [ left | right ]; map_trivial; assumption.

      + kind_case; map_trivial; eauto;
        map_trivial; kind_consistent.
    Qed.
    Next Obligation. (* well_type_t *)
      unfold Pwell_type_t. intros.

      destruct (Pos.eq_dec (nextID s) x).
      + subst.
        map_trivial.
        map_trivial.
      + map_trivial.
        map_trivial.
        state_trivial.
    Qed.
    Next Obligation. (* well_type_c *)
      unfold Pwell_type_c. intros.

      destruct (Pos.eq_dec (nextID s) x).
      + subst.
        map_trivial.
        map_trivial.
      + map_trivial.
        map_trivial.
        state_trivial.
    Qed.
    Next Obligation. (* nextID_a *)
      destruct s; simpl.
      unfold is_new in *.
      apply Pos.lt_lt_succ.
      assumption.
    Qed.
    Next Obligation. (* nextID_b *)
      map_trivial.
      + subst.
        apply Pos.lt_succ_diag_r.

      + apply Pos.lt_trans with (m:=nextID s).
        * destruct s; simpl in *.
          auto.
        * apply Pos.lt_succ_diag_r.
    Qed.
    Next Obligation. (* orig_k *)
      map_trivial.
      + auto_ident.
      + map_trivial.
        state_trivial.
    Qed.
    Next Obligation. (* orig_e *)
      map_trivial.
      + auto_ident.
      + map_trivial.
        apply trans_add_0.
        * state_trivial.
        * eauto with ident.
    Qed.
    Next Obligation. (* orig_t *)
      map_trivial.
      + auto_ident.
      + state_trivial.
    Qed.

    Next Obligation. (* xc_e *)
      map_trivial.
      + auto_ident.
      + apply transC_add_0.
        - state_trivial.
        - auto with ident.
    Qed.
    Next Obligation. (* xcn_e *)
      map_trivial.
      + auto_ident.
      + apply transC_add_0.
        - state_trivial.
        - auto with ident.
    Qed.
    Next Obligation. (* xf_e *)
      map_trivial.
      + auto_ident.
      + apply transF_add_0.
        - state_trivial.
        - auto with ident.
    Qed.
    Next Obligation. (* xfn_e *)
      map_trivial.
      + auto_ident.
      + apply transF_add_0.
        - state_trivial.
        - auto with ident.
    Qed.
    Next Obligation. (* new_nocyc *)
      map_trivial.
      + destruct Hnocyc as [ep [ ee' Hnocyc ]].
        simpl'.
        set (eq := ee' (nextID s)) in *.
        exists ep eq.
        repeat split; assumption.
      + rename Hwt into Hwt'.
        rename Hnocyc into Hnocyc'.
        destruct_new_nocyc (new_nocyc s x H H0).
        exists ep eq.
        repeat split; eauto.
        - apply trans_add_0. eauto.
          auto with ident.
    Qed.
    Next Obligation. (* local_k *)
      map_trivial.
      eapply local_k in H; eauto.
    Qed.
    Next Obligation. (* all_wt *)
      map_trivial.
      + unfold well_typeF. simpl'. simpl. subst.
        specialize (Hwt (nextID s)). unfold well_typeF' in Hwt.

        intros.
        apply Hwt; try assumption.

        - intros. apply H0.
          assert (x <> nextID s).
            intro HH; rewrite HH in H2.
            assert (M.In (nextID s) (KK (prog s))) by kind_consistent.
            assert (~M.In (nextID s) (KK (prog s))) by auto with ident.
            contradiction.
          map_trivial.
        - apply H0. map_trivial.

      + simpl'. eapply well_type_add_0; eauto.
        - auto with ident.
        - state_trivial.
    Qed.
    Next Obligation. (* all_c *)
      map_trivial.
      state_trivial.
    Qed.
    Next Obligation. (* all_gc *)
      map_trivial.
      state_trivial.
    Qed.

    Lemma addvar_new_0 :
      forall s ee H Hwt Hnocyc Hgc,
        let (x, s') := addvar_new s ee H Hwt Hnocyc Hgc in
        M.MapsTo x (ee x) (EE (prog s')).
    Proof.
      intros.

      unfold addvar_new. simpl.
      map_trivial.
    Qed.

    Lemma addvar_new_1 :
      forall s ee H Hwt Hnocyc Hgc x,
        let (_, s') := addvar_new s ee H Hwt Hnocyc Hgc in
        M.In x (KK (prog s)) ->
        M.In x (KK (prog s')).
    Proof.
      intros.
      unfold addvar_new. simpl.
      intro.

      destruct (Pos.eq_dec (nextID s) x).
      + subst. map_trivial.
      + map_trivial.
    Qed.

    Lemma addvar_new_2 :
      forall s ee H Hwt Hnocyc Hgc ep eq,
        let (_, s') := addvar_new s ee H Hwt Hnocyc Hgc in
        trans' (prog s) ep eq ->
        trans' (prog s') ep eq.
    Proof.
      intros.
      unfold addvar_new. simpl.

      intro.
      apply trans_add_0.
      + assumption.
      + auto with ident.
    Qed.

    Program Definition addvar_orig
      ( s : state )
      ( x : ident )
      ( e : expr )
      ( k : kind )
      ( Hc : clockof e = None )
      ( Hx : M.MapsTo x k (KK p) )
      ( Ht : M.MapsTo x (typeof e) (TT p) )
      ( He : forall ep,
               M.MapsTo x ep (EE p) ->
               trans' (prog s) ep e )
      ( Hx_b : ~ M.In x (KK (prog s)) )
      ( Hwt : well_typeF (prog s) e )
      ( Hgc : global_clock_expr e )
      ( Hk : k = Kout \/ k = Kloc )
    : state :=
      {| prog   := let q := prog s in
                   {| KK := M.add x k (KK q);
                      EE := M.add x e (EE q);
                      TT := M.add x (typeof e) (TT q);
                      CC := M.add x None (CC q) |};
         nextID := nextID s |}.
    Obligation Tactic := program_simpl.
    Next Obligation. (* consistentT *)
      split; intro; do 2 map_trivial.
      + kind_attach x0 (KK (prog s)).
        map_trivial.
      + kind_consistent.
    Qed.
    Next Obligation. (* consistentC *)
      split; intro; do 2 map_trivial.
      + kind_attach x0 (KK (prog s)).
        map_trivial.
      + kind_consistent.
    Qed.
    Next Obligation. (* consistentE *)
      split; intro.

      + destruct (Pos.eq_dec x0 x).
        - subst x0;
          destruct Hk; [ left | right ]; subst k; map_trivial.

        - map_trivial.
          kind_attach x0 (KK (prog s)).
          destruct H; [ left | right ]; map_trivial; assumption.

      + kind_case; map_trivial; eauto;
        map_trivial; kind_consistent.
    Qed.
    Next Obligation. (* well_type_t *)
      unfold Pwell_type_t. intros.

      destruct (Pos.eq_dec x0 x).
      + subst x0.
        map_trivial.
        map_trivial.
      + map_trivial.
        map_trivial.
        state_trivial.
    Qed.
    Next Obligation. (* well_type_c *)
      unfold Pwell_type_c. intros.

      destruct (Pos.eq_dec x0 x).
      + subst x0.
        map_trivial.
        map_trivial.
      + map_trivial.
        map_trivial.
        state_trivial.
    Qed.
    Next Obligation. (* nextID_a *)
      state_trivial.
    Qed.
    Next Obligation. (* nextID_b *)
      map_trivial.
      + auto_ident.
      + state_trivial.
    Qed.
    Next Obligation. (* orig_k *)
      map_trivial.
      map_trivial.
      state_trivial.
    Qed.
    Next Obligation. (* orig_e *)
      map_trivial.
      + apply trans_add_0.
        * subst; auto.
        * contradict Hx_b.
          kind_consistent.

      + apply trans_add_0.
        * state_trivial.
        * contradict Hx_b.
          kind_consistent.
    Qed.
    Next Obligation. (* orig_t *)
      map_trivial.
      state_trivial.
    Qed.
    Next Obligation. (* xc_e *)
      map_trivial.
      + auto_ident.
      + apply transC_add_0.
        * state_trivial.
        * contradict Hx_b.
          kind_consistent.
    Qed.

    Obligation Tactic := idtac.    (* program_simpl eats a necessary premise *)
    Next Obligation. (* xcn_e *)
      intros; simpl in *.

      map_trivial.
      + auto_ident.
      + apply transC_add_0.
        * state_trivial.
        * contradict Hx_b.
          kind_consistent.
    Qed.
    Obligation Tactic := program_simpl.

    Next Obligation. (* xf_e *)
      map_trivial.
      + auto_ident.
      + apply transF_add_0.
        - state_trivial.
        - intro.
          assert (M.In x (KK (prog s))).
            kind_consistent.
          contradiction.
    Qed.
    Next Obligation. (* xfn_e *)
      map_trivial.
      + auto_ident.
      + apply transF_add_0.
        - state_trivial.
        - intro.
          assert (M.In x (KK (prog s))).
            kind_consistent.
          contradiction.
    Qed.
    Next Obligation. (* new_nocyc *)
      map_trivial.
      + auto_ident.
      + rename Hwt into Hwt'.
        destruct_new_nocyc (new_nocyc s x0 H H0).
        exists ep eq.
        repeat split; eauto.
        - apply trans_add_0. eauto.
          contradict Hx_b.
          kind_consistent.
    Qed.
    Next Obligation. (* local_k *)
      map_trivial.
      + contradict H. auto_ident.
      + eapply local_k in H; eauto.
    Qed.
    Next Obligation. (* all_wt *)
      map_trivial.
      + unfold well_typeF. simpl'. simpl. subst.
        unfold well_typeF in Hwt.

        intros.
        apply Hwt; try assumption.

        intros.
        assert (M.In x0 (KK (prog s))) by kind_consistent.
        apply H0; map_trivial.

      + simpl'. eapply well_type_add_0; eauto.
        - contradict Hx_b. kind_consistent.
        - state_trivial.
    Qed.
    Obligation Tactic := intros; simpl in *.

    Next Obligation. (* all_c *)
      map_trivial.
      state_trivial.
    Qed.

    Obligation Tactic := program_simpl.

    Next Obligation. (* all_gc *)
      map_trivial.
      state_trivial.
    Qed.
    

    Lemma addvar_orig_0 :
      forall s x e k Hc Hx Ht He Hx_b Hwt Hgc Hk,
        M.In x (KK (prog (addvar_orig s x e k Hc Hx Ht He Hx_b Hwt Hgc Hk))).
    Proof.
      intros.
      unfold addvar_orig. simpl.
      map_trivial.
    Qed.

    Lemma addvar_orig_1 :
      forall s x e k Hc Hx Ht He Hx_b Hwt Hgc Hk x',
        M.In x' (KK (prog s)) ->
        M.In x' (KK (prog (addvar_orig s x e k Hc Hx Ht He Hx_b Hwt Hgc Hk))).
    Proof.
      intros.

      destruct (Pos.eq_dec x x').
      + subst.
        simpl. map_trivial.
      + simpl. map_trivial.
    Qed.

    Program Fixpoint fill_xc
      (s : state)
      (c : clock)
      (Ht : forall x, c = Some x -> M.MapsTo x Tbool (TT p))
      { wf (clk_dep p) c }
    : { t : state | M.In (ident_xc c) (KK (prog t)) /\
                    ( forall x, M.In x (KK (prog s)) -> M.In x (KK (prog t)) ) /\
                    ( forall ep eq, trans' (prog s) ep eq -> trans' (prog t) ep eq ) /\
                    ( forall e, well_typeF (prog s) e -> well_typeF (prog t) e ) } :=
      match M.find (ident_xc c) (KK (prog s)) with
        | Some x => s
        | None => 
          match c with
            | None => addvar_xcn s _
            | Some x =>
                match M.find x (CC p) with
                  | None => !
                  | Some c' =>
                      let s' := fill_xc s c' _ in
                      match M.find (ident_xc c) (KK (prog s')) with
                        | Some x => s'    (* actually absurd *)
                        | None => addvar_xc s' x c' _ _ _ _
                      end
                end
          end
      end.
    Next Obligation.
      repeat split.
      + exists x.
        apply M.find_2.
        congruence.
      + trivial.
      + trivial.
      + trivial.
    Qed.
    Next Obligation.
      map_trivial.
    Qed.
    Next Obligation.
      repeat split.
      + map_trivial.
      + intros.
        assert (~ M.In (3*max_ident+1) (KK (prog s))) by map_trivial.
        map_trivial.
      + assert (Hx: ~ M.In (3*max_ident+1) (KK (prog s))) by map_trivial.
        apply addvar_xcn_2 with (Hx := Hx).
      + intros. apply well_type_add_0; eauto.
        assert (Hx : ~ M.In (3*max_ident+1) (KK (prog s))) by map_trivial.
        contradict Hx. kind_consistent.
    Qed.
    Next Obligation.
      specialize (Ht x). simpl'.

      assert (M.In x (KK p)) by kind_consistent.
      assert (HH1 : M.In x (CC p)) by kind_consistent.
      assert (HH2 : ~ M.In x (CC p)) by map_trivial.
  
      contradiction.
    Qed.
    Next Obligation.
      assert (HH1 : M.MapsTo x (Some x0) (CC p)) by map_trivial.
      program_trivial.
    Qed.
    Next Obligation.
      unfold clk_dep; intros; simpl'; subst.
      exists x. split.
      + reflexivity.
      + map_trivial.
    Qed.
    Next Obligation.
      repeat split.
      + exists x0.
        apply M.find_2.
        symmetry. auto.
      + set (res := fill_xc s c'
                            (fill_xc_func_obligation_5 s (Some x) Ht fill_xc Heq_anonymous
                                                       x eq_refl c' Heq_anonymous0)
                            (fill_xc_func_obligation_6 s (Some x) Ht fill_xc Heq_anonymous
                                                       x eq_refl c' Heq_anonymous0)).
        destruct res. simpl.
        intuition.
      + set (res := fill_xc s c'
                            (fill_xc_func_obligation_5 s (Some x) Ht fill_xc Heq_anonymous
                                                       x eq_refl c' Heq_anonymous0)
                            (fill_xc_func_obligation_6 s (Some x) Ht fill_xc Heq_anonymous
                                                       x eq_refl c' Heq_anonymous0)).
        destruct res. simpl.
        intuition.
      + set (res := fill_xc s c'
                            (fill_xc_func_obligation_5 s (Some x) Ht fill_xc Heq_anonymous
                                                       x eq_refl c' Heq_anonymous0)
                            (fill_xc_func_obligation_6 s (Some x) Ht fill_xc Heq_anonymous
                                                       x eq_refl c' Heq_anonymous0)).
        destruct res. simpl.
        intuition.
    Qed.
    Next Obligation.
      map_trivial.
    Qed.
    Next Obligation.
      set (res := fill_xc s c'
                          (fill_xc_func_obligation_5 s (Some x) Ht fill_xc Heq_anonymous
                                                     x eq_refl c' Heq_anonymous0)
                          (fill_xc_func_obligation_6 s (Some x) Ht fill_xc Heq_anonymous
                                                     x eq_refl c' Heq_anonymous0)).
      destruct res. simpl. destruct a. assumption.
    Qed.
    Next Obligation.
      map_trivial.
    Qed.
    Next Obligation.
      intros.
      repeat split.
      + map_trivial.
      + intros.
        apply MF.add_in_iff. right.
        set (res := fill_xc s c'
                            (fill_xc_func_obligation_5 s (Some x) Ht fill_xc Heq_anonymous
                                                       x eq_refl c' Heq_anonymous0)
                            (fill_xc_func_obligation_6 s (Some x) Ht fill_xc Heq_anonymous
                                                       x eq_refl c' Heq_anonymous0)).
        destruct res. simpl'.
        intuition.
      + intros.

        apply trans_add_0.
        * set (res := fill_xc s c'
                            (fill_xc_func_obligation_5 s (Some x) Ht fill_xc Heq_anonymous
                                                       x eq_refl c' Heq_anonymous0)
                            (fill_xc_func_obligation_6 s (Some x) Ht fill_xc Heq_anonymous
                                                       x eq_refl c' Heq_anonymous0)).
          destruct res. simpl'. intuition.
        * set (res := fill_xc s c'
                            (fill_xc_func_obligation_5 s (Some x) Ht fill_xc Heq_anonymous
                                                       x eq_refl c' Heq_anonymous0)
                            (fill_xc_func_obligation_6 s (Some x) Ht fill_xc Heq_anonymous
                                                       x eq_refl c' Heq_anonymous0)) in *.
          intro.
          assert (M.In (max_ident + x) (KK (prog (` res)))).
            destruct (` res).
            kind_consistent.
          assert (~ M.In (max_ident + x) (KK (prog (` res)))) by map_trivial.
          contradiction.
      + set (res := fill_xc s c'
                            (fill_xc_func_obligation_5 s (Some x) Ht fill_xc Heq_anonymous
                                                       x eq_refl c' Heq_anonymous0)
                            (fill_xc_func_obligation_6 s (Some x) Ht fill_xc Heq_anonymous
                                                       x eq_refl c' Heq_anonymous0)) in *.
        clearbody res. destruct res as [t Hres]. simpl in *.
        simpl'.

        intros. apply well_type_add_0.
        * intro.
          assert (M.In (max_ident + x) (KK (prog t))) by kind_consistent.
          assert (~ M.In (max_ident + x) (KK (prog t))) by map_trivial.
          contradiction.
        * auto.
    Qed.
    Next Obligation.
      apply measure_wf.
      apply clk_dep_0; assumption.
    Defined.

    Program Definition fill_xf
      (s : state)
      (c : clock)
      (Ht : forall x, c = Some x -> M.MapsTo x Tbool (TT p))
    : { t : state | M.In (ident_xf c) (KK (prog t)) /\
                    M.In (ident_xc c) (KK (prog t)) /\
                    ( forall x, M.In x (KK (prog s)) -> M.In x (KK (prog t)) ) /\
                    ( forall ep eq, trans' (prog s) ep eq -> trans' (prog t) ep eq ) /\
                    ( forall e, well_typeF (prog s) e -> well_typeF (prog t) e ) } :=
      let s' := fill_xc s c _ in
      match M.find (ident_xf c) (KK (prog s')) with
        | Some x => s'
        | None =>
          match c with
            | None => addvar_xfn s' _ _
            | Some x => addvar_xf s' x _ _ _
          end
      end.
    Next Obligation.
      repeat split.
      + exists x.
        map_trivial.
      + set (res := fill_xc s c (fill_xf_obligation_1 s c Ht)) in *.
        destruct res. simpl in *. simpl'. assumption.
      + set (res := fill_xc s c (fill_xf_obligation_1 s c Ht)) in *.
        destruct res. simpl in *. simpl'. assumption.
      + set (res := fill_xc s c (fill_xf_obligation_1 s c Ht)) in *.
        destruct res. simpl in *. simpl'. assumption.
      + set (res := fill_xc s c (fill_xf_obligation_1 s c Ht)) in *.
        destruct res. simpl in *. simpl'. assumption.
    Qed.
    Next Obligation.
      set (res := fill_xc s None (fill_xf_obligation_1 s None Ht)) in *.
      destruct res.
      simpl. simpl'. assumption.
    Qed.
    Next Obligation.
      map_trivial.
    Qed.
    Next Obligation.
      repeat split.
      + map_trivial.
      + set (res := fill_xc s None (fill_xf_obligation_1 s None Ht)) in *.
        destruct res. simpl in *. simpl'.
        intros. apply MF.add_in_iff. right. auto.
      + set (res := fill_xc s None (fill_xf_obligation_1 s None Ht)) in *.
        destruct res. simpl in *. simpl'.
        intros. apply MF.add_in_iff. right. auto.
      + set (res := fill_xc s None (fill_xf_obligation_1 s None Ht)) in *.
        destruct res. simpl in *. simpl'.

        intros.
        apply trans_add_0. auto.

        intro.
        assert (M.In (3*max_ident + 2) (KK (prog x))).
          destruct x.
          kind_consistent.
        assert (~ M.In (3*max_ident + 2) (KK (prog x))) by map_trivial.
        contradiction.
      + set (res := fill_xc s None (fill_xf_obligation_1 s None Ht)) in *.
        destruct res. simpl in *. simpl'.

        intros.
        apply well_type_add_0. auto.

        * intro.
          assert (M.In (3*max_ident + 2) (KK (prog x))).
            destruct x.
            kind_consistent.
          assert (~ M.In (3*max_ident + 2) (KK (prog x))) by map_trivial.
          contradiction.

        * auto.
    Qed.
    Next Obligation.
      set (res := fill_xc s (Some x) (fill_xf_obligation_1 s (Some x) Ht)) in *.
      destruct res.
      simpl. simpl'. assumption.
    Qed.
    Next Obligation.
      assert (M.MapsTo x Tbool (TT p)) by eauto.
      destruct WF; apply WFconsistentT; eauto.
    Qed.
    Next Obligation.
      map_trivial.
    Qed.
    Next Obligation.
      repeat split.
      + simpl. map_trivial.
      + set (res := fill_xc s (Some x) (fill_xf_obligation_1 s (Some x) Ht)) in *.
        destruct res. simpl in *. simpl'.
        intros. apply MF.add_in_iff. right. auto.
      + set (res := fill_xc s (Some x) (fill_xf_obligation_1 s (Some x) Ht)) in *.
        destruct res. simpl in *. simpl'.
        intros. apply MF.add_in_iff. right. auto.
      + set (res := fill_xc s (Some x) (fill_xf_obligation_1 s (Some x) Ht)) in *.
        destruct res. simpl in *. simpl'.

        intros.
        apply trans_add_0. auto.

        intro.
        assert (M.In (2*max_ident + x) (KK (prog x0))).
          destruct x0.
          kind_consistent.
        assert (~ M.In (2*max_ident + x) (KK (prog x0))) by map_trivial.
        contradiction.
      + set (res := fill_xc s (Some x) (fill_xf_obligation_1 s (Some x) Ht)) in *.
        destruct res. simpl in *. simpl'.

        intros.
        apply well_type_add_0. auto.
        * intro.
          assert (M.In (2*max_ident + x) (KK (prog x0))).
            destruct x0.
            kind_consistent.
          assert (~ M.In (2*max_ident + x) (KK (prog x0))) by map_trivial.
          contradiction.
        * auto.
    Qed.

    Program Definition trans_r
      ( s : state )
      ( eq : expr )
      ( xc : ident )
      ( ui : val )
      ( Hwt : well_typeF (prog s) eq )
      ( Hxc : M.MapsTo xc Tbool (TT (prog s)) )
      ( Hui : well_type_val ui (typeof eq) )
      ( Heq_c : clockof eq = None )
      ( Hnocyc :
          let q := prog s in
          let x := nextID s in
          let t := {| KK := M.add x Kloc (KK q);
                      EE := M.add x (Edata3 Oif
                                            (Evar xc Tbool None)
                                            eq
                                            (Efby
                                               (Econst ui (typeof eq) None)
                                               (Evar x (typeof eq) None)
                                               (typeof eq)
                                               None)
                                            (typeof eq)
                                            None ) (EE q);
                      TT := M.add x (typeof eq) (TT q);
                      CC := M.add x None (CC q) |} in
          exists ep,
            well_typeP ep /\
            ( transR' t eq xc ui x ->
              trans' t ep (Evar x (typeof ep) None ) ) )
      ( Hgc : global_clock_expr eq )
    : ident * state :=
    addvar_new s (fun xr => Edata3 Oif
                                   (Evar xc Tbool None)
                                   eq
                                   (Efby
                                      (Econst ui (typeof eq) None)
                                      (Evar xr (typeof eq) None)
                                      (typeof eq)
                                      None)
                                   (typeof eq)
                                   None ) _ _ _ _.
    Obligation Tactic := idtac.
    Next Obligation.
      unfold well_typeF'. intros.

      assert (M.MapsTo x None (CC pf)) by eauto.
      assert (M.MapsTo xc Tbool (TT pf)) by eauto.
      assert (M.MapsTo xc None (CC pf)) by eauto.

      eauto 30 with constr.
    Qed.
    Next Obligation.
      intros. simpl in *.
      destruct Hnocyc as [ep [ Hwt' Hnocyc ] ]. simpl'.

      exists ep (fun xr => (Evar xr (typeof ep) None)).
      intros. repeat split; try assumption.

      + apply Hnocyc.
        constructor. unfold t.
        simpl. map_trivial.
      
      + clear.
        intros.
        inversion H.
        assumption.
    Qed.
    Next Obligation.
      intros. simpl in *.

      eauto 30 with constr.
    Qed.
    Obligation Tactic := program_simpl.


    Ltac clean_trans_r :=
      match goal with
        | [ |- context [trans_r ?s ?eq ?xc ?ui ?H1 ?H2 ?H3 ?H4 ?H5 ?H6] ] =>
            generalize H1 as HG1;
            generalize H2 as HG2;
            generalize H3 as HG3;
            generalize H4 as HG4;
            generalize H5 as HG5;
            generalize H6 as HG6;
            intros;
            remember (trans_r s eq xc ui HG1 HG2 HG3 HG4 HG5 HG6) as res;
            destruct res as [xr res_s]; rewrite_tuple
      end.

    Ltac clean_trans_r' :=
      match goal with
        | [ H : ( _ , ?s_c ) = trans_r ?s ?eq ?xc ?ui ?H1 ?H2 ?H3 ?H4 ?H5 ?H6 |- _ ] =>
            set (HG1 := H1) in *;
            set (HG2 := H2) in *;
            set (HG3 := H3) in *;
            set (HG4 := H4) in *;
            set (HG5 := H5) in *;
            set (HG6 := H6) in *;
            clearbody HG1 HG2 HG3 HG4 HG5 HG6;
            let res_s := fresh "res_s" in
            let Heqres := fresh "Heqres" in
            rename s_c into res_s;
            rename H into Heqres
      end.

    Lemma trans_r_0 :
      forall s eq xc ui Hwt Hxc Hui Heq_c Hnocyc Hgc,
        let (xr, s') := trans_r s eq xc ui Hwt Hxc Hui Heq_c Hnocyc Hgc in
        transR' (prog s') eq xc ui xr.
    Proof.
      intros.
      remember (trans_r s eq xc ui Hwt Hxc Hui Heq_c Hnocyc Hgc). destruct p0 as [xr s'].
      unfold trans_r in Heqp0.

      match goal with
        | [ H : _ = addvar_new ?s ?ee ?H ?H2 ?H3 ?H4 |- _ ] =>
          set (HH1 := addvar_new_0 s ee H H2 H3 H4); clearbody HH1
      end.

      rewrite <- Heqp0 in HH1.

      constructor.
      assumption.
    Qed.

    Lemma trans_r_1 :
      forall s eq xc ui Hwt Hxc Hui Heq_c Hnocyc Hgc x',
        let (xr, s') := trans_r s eq xc ui Hwt Hxc Hui Heq_c Hnocyc Hgc in
        M.In x' (KK (prog s)) ->
        M.In x' (KK (prog s')).
    Proof.
      intros.
      unfold trans_r.
      apply addvar_new_1.
    Qed.

    Lemma trans_r_2 :
      forall s eq xc ui Hwt Hxc Hui Heq_c Hnocyc Hgc ep' eq',
        let (_, t) := trans_r s eq xc ui Hwt Hxc Hui Heq_c Hnocyc Hgc in
        trans' (prog s) ep' eq' ->
        trans' (prog t) ep' eq'.
    Proof.
      intros.
      unfold trans_r.
      apply addvar_new_2.
    Qed.

    Ltac apply_let H T :=
      match type of T with
        | (_, _) = trans_r ?s ?eq ?xc ?ui ?H1 ?H2 ?H3 ?H4 ?H5 ?H6 =>
          let HL := fresh "HL" in
          pose (HL := H s eq xc ui H1 H2 H3 H4 H5 H6); clearbody HL;
          rewrite <- T in HL; eauto
        | (_, _) = addvar_new ?s ?ee ?H1 ?H2 ?H3 ?H4 =>
          let HL := fresh "HL" in
          pose (HL := H s ee H1 H2 H3 H4); clearbody HL;
          rewrite <- T in HL; eauto
      end.

    Lemma trans_r_3 :
      forall s eq xc ui Hwt Hxc Hui Heq_c Hnocyc Hgc,
        let (xr, t) := trans_r s eq xc ui Hwt Hxc Hui Heq_c Hnocyc Hgc in
        well_typeF (prog t) (Evar xr (typeof eq) None).
    Proof.
      intros.
      remember (trans_r s eq xc ui Hwt Hxc Hui Heq_c Hnocyc Hgc) as res.
      destruct res as [xr t].

      unfold well_typeF; intros.

      assert (M.MapsTo xr (typeof eq) (TT (prog t))).
        unfold trans_r in *.

        apply_let addvar_new_0 Heqres.

        assert (M.In xr (KK (prog t))) by kind_consistent.

        assert (HH: M.In xr (TT (prog t))) by kind_consistent.
        destruct HH as [ xrt HH ].

        assert (typeof (Edata3 Oif (Evar xc Tbool None) eq
            (Efby (Econst ui (typeof eq) None) (Evar xr (typeof eq) None)
               (typeof eq) None) (typeof eq) None) = xrt).
          eapply (well_type_t t); eauto.

        subst. simpl in *. assumption.

      assert (M.MapsTo xr (typeof eq) (TT pf)) by auto.
      assert (M.MapsTo xr None (CC pf)) by eauto.
      
      constructor; eauto.
    Qed.

    Lemma addvar_new_4 :
      forall s ee H Hwt Hnocyc Hgc e,
        let (_, t) := addvar_new s ee H Hwt Hnocyc Hgc in
        well_typeF (prog s) e ->
        well_typeF (prog t) e.
    Proof.
      intros.
      unfold addvar_new. simpl.

      apply well_type_add_0.
      auto with ident.
    Qed.

    Lemma trans_r_4 :
      forall s eq xc ui Hwt Hxc Hui Heq_c Hnocyc Hgc e,
        let (xr, t) := trans_r s eq xc ui Hwt Hxc Hui Heq_c Hnocyc Hgc in
        well_typeF (prog s) e ->
        well_typeF (prog t) e.
    Proof.
      intros.
      remember (trans_r s eq xc ui Hwt Hxc Hui Heq_c Hnocyc Hgc) as res.
      destruct res as [xr t].
      intros.

      unfold trans_r in *.

      apply_let addvar_new_4 Heqres.
    Qed.

    Import ArbitraryValue.

    Hint Unfold well_typeF.

    Hint Resolve arb_value_0.

    Program Fixpoint trans_expr
      ( s : state )
      ( e : expr )
      ( Hwt : well_typeP e )
    : { ( t, e' ) : state * expr |
        trans' (prog t) e e' /\
        ( forall ep eq, trans' (prog s) ep eq -> trans' (prog t) ep eq) /\
        ( forall x, M.In x (KK (prog s)) -> M.In x (KK (prog t)) ) /\
        well_typeF (prog t) e' /\
        ( forall e, well_typeF (prog s) e -> well_typeF (prog t) e )
      } :=
    match e with
      | Evar x t c =>
        let ui := arb_value t in
        let (s_a, _) := fill_xc s c _ in
        let '(xr, s_b) := trans_r s_a (Evar x t None) (ident_xc c) ui _ _ _ _ _ _ in
        (s_b, (Evar xr t None) )
      | Econst u t c => (s, Econst u t None)
      | Ewhen ep x t c =>
        let ui := arb_value t in
        let (s_a, _) := fill_xc s c _ in
        let (res_b, _) := trans_expr s_a ep _ in let '(s_b, eq') := res_b in
        let '(xr, s_c) := trans_r s_b eq' (ident_xc c) ui _ _ _ _ _ _ in
        (s_c, (Evar xr t None) )
      | Ecurr ep x ui t c =>
        let (s_a, _) := fill_xc s (Some x) _ in
        let (res_b, _) := trans_expr s_a ep _ in let '(s_b, eq') := res_b in
        let '(xr, s_c) := trans_r s_b eq' (ident_xc (Some x)) ui _ _ _ _ _ _ in
        (s_c, (Evar xr t None) )
      | Efby eap ebp t c =>
        let ui := arb_value t in
        let (s_a, _) := fill_xf s c _ in
        let (res_b, _) := trans_expr s_a eap _ in let '(s_b, eaq) := res_b in
        let (res_c, _) := trans_expr s_b ebp _ in let '(s_c, ebq) := res_c in
        let '(xr, s_d) := trans_r s_c (Edata3 Oif
                                              (Evar (ident_xf c) Tbool None)
                                              eaq
                                              (Efby (Econst ui t None)
                                                    ebq
                                                    t
                                                    None)
                                              t
                                              None) (ident_xc c) ui _ _ _ _ _ _ in
        (s_d, (Evar xr t None) )
      | Edata1 o eap t c =>
        let '(s_a, eaq) := trans_expr s eap _ in
        (s_a, Edata1 o eaq t None)
      | Edata2 o eap ebp t c =>
        let '(s_a, eaq) := trans_expr s eap _ in
        let '(s_b, ebq) := trans_expr s_a ebp _ in
        (s_b, Edata2 o eaq ebq t None)
      | Edata3 o eap ebp ecp t c =>
        let '(s_a, eaq) := trans_expr s eap _ in
        let '(s_b, ebq) := trans_expr s_a ebp _ in
        let '(s_c, ecq) := trans_expr s_b ecp _ in
        (s_c, Edata3 o eaq ebq ecq t None)
    end.

    Solve Obligations using program_simpl; inversion_WT; repeat split; auto.

    Solve Obligations using program_simpl; eapply trans_clock; eauto.

    Next Obligation.
      program_trivial.
    Qed.

    Next Obligation. inversion_WT; repeat split; eauto 30 with constr. Qed.

    Next Obligation.
      apply state_xc_t; eauto.
      intros.
      apply is_orig_0.
      program_trivial.
    Qed.

    Next Obligation.
      exists (Evar x t c).
      split; [ assumption | ].
      intros. simpl.
      eapply TRvar; eauto.

      apply transC_add_0; [ | apply state_next_1 ].
      assert (M.In (ident_xc c) (KK (prog s_a))) by eauto.

      destruct c.
      - apply xc_e; try assumption.
        apply is_orig_0.
        program_trivial.
      - apply xcn_e; try assumption.
    Qed.

    Obligation Tactic := intros; simpl in *; subst; simpl'.

    Next Obligation.
      eauto with constr.
    Qed.

    Next Obligation. (* Evar *)
      clean_trans_r'. subst. simpl'.
      unfold ui in *. clear ui.
      repeat split.
      + apply TRvar with (xc:=ident_xc c) (ui:=arb_value t).
        - apply_let trans_r_0 Heqres.
        - apply_let trans_r_1 Heqres.

          assert (M.In (ident_xc c) (KK (prog s_a))).
            auto.

          assert (M.In (ident_xc c) (KK (prog res_s))).
            auto.

          inversion Hwt; clear Hwt; subst.
          attach_is_orig.

          destruct c.
          * assert (is_orig i1).
              apply is_orig_0.
              program_trivial.
            state_trivial.
          * state_trivial.
      + apply_let trans_r_2 Heqres.
      + apply_let trans_r_1 Heqres.
      + apply_let trans_r_3 Heqres.
      + apply_let trans_r_4 Heqres.
    Qed.
      
    Next Obligation. inversion_WT; repeat split; eauto 30 with constr. Qed.

    Next Obligation.
      program_trivial.
    Qed.

    Next Obligation.
      inversion Hwt; clear Hwt.
      apply state_xc_t; eauto.

      intros.
      apply is_orig_0.
      assert (x1 = x) by congruence.
      subst x1. clear H15. kind_consistent.
    Qed.

    Next Obligation.
      erewrite <- trans_type; eauto.
      inversion Hwt. rewrite H15.
      apply arb_value_0.
    Qed.

    Next Obligation.
      exists (Ewhen ep x t c).
      split; [ assumption | ].
      intros. simpl.
      eapply TRwhen; eauto.

      + apply trans_add_0; try assumption.
        apply state_next_1.
      + apply transC_add_0; [ | apply state_next_1 ].

        assert (M.In (ident_xc c) (KK (prog s_b))).
          eauto.

        destruct c.
        - apply xc_e; try assumption.
          apply is_orig_0.
          program_trivial.
        - apply xcn_e; try assumption.
    Qed.

    Next Obligation.
      eapply trans_gc_expr.
      eauto.
    Qed.

    Next Obligation. (* Ewhen *)
      clean_trans_r'. subst. simpl'.
      unfold ui in *. clear ui.
      repeat split.
      + apply TRwhen with (eq:=eq') (xc:=ident_xc c) (ui:=arb_value t).
        - apply_let trans_r_2 Heqres.
        - apply_let trans_r_0 Heqres.
        - apply_let trans_r_1 Heqres.

          assert (M.In (ident_xc c) (KK (prog s_b))).
            auto.

          assert (M.In (ident_xc c) (KK (prog res_s))).
            auto.

          inversion Hwt; clear Hwt; subst.
          attach_is_orig.
      iter_tac ( fun H => match type of H with
        | M.In ?x (KK p) => assert (is_orig x) by eauto with ident
        | M.MapsTo ?x ?k (KK p) => assert (is_orig x) by eauto with ident
        | M.MapsTo ?x ?t (TT p) =>
            assert (is_orig x);
            [ assert (M.In x (KK p)); [ kind_consistent | eauto with ident ] | ]
        | _ => idtac
      end ).
      destructP.
      assert (M.In x (KK p)) by kind_consistent.

          destruct res_s; simpl in *. eauto.
      + apply_let trans_r_2 Heqres.
      + apply_let trans_r_1 Heqres.
      + apply_let trans_r_3 Heqres.
        assert (HH: typeof ep = typeof eq').
          eapply trans_type; eauto.
        inversion_WT. rewrite HH; eauto.
      + apply_let trans_r_4 Heqres.
    Qed.

    Next Obligation.
      inversion Hwt; clear Hwt; subst.

      set (c' := Some x).
      change (M.MapsTo (ident_xc c') Tbool (TT (prog s_b))).
      apply state_xc_t.
      + intros; subst. simpl'; subst.
        apply is_orig_0; kind_consistent.
      + subst c'. simpl'. eauto.
    Qed.

    Next Obligation.
      assert (typeof ep = typeof eq').
        eapply trans_type; eauto.

      inversion Hwt; subst.
      rewrite <- H8; assumption.
    Qed.

    Next Obligation.
      exists (Ecurr ep x ui t c).
      split; [ assumption | ].
      intros. simpl.
      eapply TRcurr; eauto.

      + apply trans_add_0; try assumption.
        apply state_next_1.
      + apply transC_add_0; [ | apply state_next_1 ].

        assert (M.In (ident_xc (Some x)) (KK (prog s_b))).
          eauto.

        apply xc_e; try assumption.
        apply is_orig_0.
        inversion Hwt.
        kind_consistent.
    Qed.

    Next Obligation.
      eapply trans_gc_expr.
      eauto.
    Qed.

    Next Obligation. (* Ecurr *)
      clean_trans_r'.
      repeat split.
      + apply TRcurr with (eq:=eq') (xc:=ident_xc (Some x)).
        - apply_let trans_r_2 Heqres.
        - apply_let trans_r_0 Heqres.
        - apply_let trans_r_1 Heqres.

          assert (M.In (ident_xc (Some x)) (KK (prog res_s))).
            intuition.

          inversion Hwt; subst.
          attach_is_orig.

          destruct res_s; eauto.
      + apply_let trans_r_2 Heqres.
      + apply_let trans_r_1 Heqres.
      + apply_let trans_r_3 Heqres.
        assert (typeof ep = typeof eq').
          eapply trans_type; eauto.
        inversion_WT. rewrite H; assumption.
      + apply_let trans_r_4 Heqres.
    Qed.

    Next Obligation.
      program_trivial.
    Qed.

    Next Obligation.
      unfold ui in *; clear ui.
      
      assert (M.MapsTo (ident_xf c) Tbool (TT (prog s_c))).
        assert (M.In (ident_xf c) (KK (prog s_c))).
          eauto.
        assert (transF' (prog s_c) (ident_xc c) (ident_xf c)).
        { destruct c.
          + assert (is_orig i).
              apply is_orig_0.
              program_trivial.
            destruct s_c; simpl in *. eauto.
          + destruct s_c; eauto. }
        apply state_xf_t; eauto.
          intros. subst.
          apply is_orig_0.
          program_trivial.

      assert (typeof eap = typeof eaq).
        eapply trans_type; eauto.

      assert (typeof ebp = typeof ebq).
        eapply trans_type; eauto.

      assert (typeof eap = typeof ebp).
        inversion Hwt; congruence.

      assert (typeof ebq = t).
        inversion Hwt; congruence.
      subst t.

      assert (well_typeF (prog s_c) eaq).
        auto.

      assert (clockof eaq = None).
        eapply trans_clock; eauto.

      assert (clockof ebq = None).
        eapply trans_clock; eauto.

      change None with (clockof (Evar (ident_xf c) Tbool None)) at -1.

      constructor; eauto with constr.

      congruence.
    Qed.

    Next Obligation.
      apply state_xc_t; eauto.
      intros; subst.
      apply is_orig_0.
      program_trivial.
    Qed.

    Next Obligation.
      exists (Efby eap ebp t c).
      split; [ assumption | ].
      intros.

      simpl.
      eapply TRfby; eauto.
      + apply trans_add_0. eauto.
        apply state_next_1.
      + apply trans_add_0. eauto.
        apply state_next_1.
      + apply transC_add_0; [ | apply state_next_1 ].

        assert (M.In (ident_xc c) (KK (prog s_c))).
          eauto.

        destruct c.
        - apply xc_e; try assumption.
          apply is_orig_0.
          program_trivial.
        - apply xcn_e; try assumption.
      + apply transF_add_0; [ | apply state_next_1 ].

        assert (M.In (ident_xf c) (KK (prog s_c))).
          eauto.

        destruct c.
        - apply xf_e; try assumption.
          apply is_orig_0.
          program_trivial.
        - apply xfn_e; try assumption.
    Qed.

    Next Obligation.
      assert (global_clock_expr eaq).
        eapply trans_gc_expr; eauto.
      assert (global_clock_expr ebq).
        eapply trans_gc_expr; eauto.
      eauto 30 with constr.
    Qed.

    Next Obligation. (* Efby *)
      clean_trans_r'.
      unfold ui in *; clear ui.
      repeat split.
      + apply TRfby with (eaq:=eaq) (ebq:=ebq)
                         (xc:=ident_xc c) (xf:=ident_xf c) (ui:=arb_value t).
        - apply_let trans_r_2 Heqres.
        - apply_let trans_r_2 Heqres.
        - apply_let trans_r_0 Heqres.
        - apply_let trans_r_1 Heqres.
          assert (M.In (ident_xc c) (KK (prog res_s))).
            intuition.
          destruct c.
          * assert (is_orig i4).
              apply is_orig_0.
              program_trivial.
            destruct res_s; eauto.
          * destruct res_s; eauto.
        - apply_let trans_r_1 Heqres.
          assert (M.In (ident_xf c) (KK (prog res_s))).
            intuition.
          destruct c.
          * assert (is_orig i4).
              apply is_orig_0.
              program_trivial.
            destruct res_s; eauto.
          * destruct res_s; eauto.

      + apply_let trans_r_2 Heqres.
      + apply_let trans_r_1 Heqres.
      + apply_let trans_r_3 Heqres.
      + apply_let trans_r_4 Heqres.
    Qed.

    Hint Extern 5 (_ = _) => symmetry.

    Next Obligation. (* Edata1 *)
      remember (trans_expr s eap
                     (trans_expr_obligation_38 s (Edata1 o eap t c) Hwt o eap
                        t c eq_refl) ).
      clear Heqs0.
      destruct s0 as [ [ t' e' ] H ]. simpl'. simpl in *. rewrite_tuple.

      repeat split; eauto 30 with constr.
      inversion_WT; eauto 30 with constr.
    Defined.

    Obligation Tactic := program_simpl.
    Next Obligation. (* Edata2 *)
      repeat split; eauto 30.
      + constructor; eauto 30.
      + unfold well_typeF. intros.

        inversion_WT;
        [ eapply WDbinZZ | eapply WDbinZB | eapply WDbinBB ];
        subst; eauto with constr;

        try solve
            [ eapply w0; eauto
            | assert (typeof ebp = typeof e0);
                [ eapply trans_type; eauto | congruence ]
            | assert (typeof eap = typeof e1);
                [ eapply trans_type; eauto | congruence ] ].
    Defined.

    Next Obligation. (* Edata3 *)
      repeat split; eauto 30;
      inversion_WT;
      constructor; eauto 30.
      + eapply w0; eauto.
      + eapply w0; eauto.
      + assert (typeof eap = typeof e2).
          eapply trans_type; eauto.
        congruence.
      + assert (typeof ebp = typeof e1).
          eapply trans_type; eauto.
        assert (typeof ecp = typeof e0).
          eapply trans_type; eauto.
        congruence.
    Defined.

    Program Definition each_var
      s x k
      ( Hk : M.MapsTo x k (KK p) )
      ( Hx : ~ M.In x (KK (prog s)) )
    : { t:state | M.In x (KK (prog t)) /\
                  (forall x, M.In x (KK (prog s)) -> M.In x (KK (prog t))) } :=
      match k with
        | Kin =>
          match M.find x (TT p) with
            | None => !
            | Some t => addvar_in s x t _ _ _
          end
        | Kloc | Kout =>
          match M.find x (EE p) with
            | None => !
            | Some e =>
              let (res, _) := trans_expr s e _ in
              let '(s', e') := res in
              match M.find x (KK (prog s')) with
                | Some _ => s'
                | None => addvar_orig s' x e' k _ _ _ _ _ _ _ _
              end
          end
      end.
    Next Obligation.
      assert (~ M.In x (TT p)) by map_trivial.
      assert (M.In x (TT p)) by kind_consistent.
      contradiction.
    Qed.

    Next Obligation.
      map_trivial.
    Qed.

    Next Obligation.
      split.
      + map_trivial.
      + intros; map_trivial.
    Qed.

    Next Obligation.
      assert (~ M.In x (EE p)) by map_trivial.
      assert (M.In x (EE p)) by kind_consistent.
      contradiction.
    Qed.

    Next Obligation.
      assert (M.MapsTo x e (EE p)) by map_trivial.

      destructP; eauto.
    Qed.

    Next Obligation.
      split.
      + exists wildcard'. map_trivial.
      + intros.
        intuition.
    Qed.

    Obligation Tactic := intros; simpl in *; subst; simpl'.
    Next Obligation.
      eapply trans_clock; eauto.
    Qed.

    Next Obligation.
      assert (M.MapsTo x e (EE p)); map_trivial.

      assert (HH: M.In x (TT p)) by kind_consistent.
      destruct HH as [ t HH ].

      assert (t = typeof e).
        destructP; eauto.
      subst t.

      assert (typeof e = typeof e').
        eapply trans_type; eauto.

      congruence.
    Qed.

    Next Obligation.
      assert (M.MapsTo x e (EE p)) by map_trivial.
      map_trivial.
    Qed.

    Next Obligation.
      map_trivial.
    Qed.

    Next Obligation.
      eapply trans_gc_expr; eauto.
    Qed.

    Next Obligation.
      split.
      + map_trivial.
      + intuition.
        map_trivial.
        intuition.
    Qed.

    Next Obligation.
      assert (~ M.In x (EE p)) by map_trivial.
      assert (M.In x (EE p)) by kind_consistent.
      contradiction.
    Qed.

    Next Obligation.
      assert (M.MapsTo x e (EE p)) by map_trivial.

      destructP; eauto.
    Qed.

    Next Obligation.
      split.
      + exists wildcard'. map_trivial.
      + intros.
        intuition.
    Qed.

    Next Obligation.
      eapply trans_clock; eauto.
    Qed.

    Next Obligation.
      assert (M.MapsTo x e (EE p)) by map_trivial.

      assert (HH: M.In x (TT p)) by kind_consistent.
      destruct HH as [ t HH ].

      assert (t = typeof e).
        destructP; eauto.
      subst t.

      assert (typeof e = typeof e').
        eapply trans_type; eauto.

      congruence.
    Qed.

    Next Obligation.
      assert (M.MapsTo x e (EE p)) by map_trivial.
      map_trivial.
    Qed.

    Next Obligation.
      map_trivial.
    Qed.

    Next Obligation.
      eapply trans_gc_expr; eauto.
    Qed.

    Next Obligation.
      split.
      + map_trivial.
      + intuition.
        map_trivial.
        intuition.
    Qed.

    Program Definition trans_all := M.fold ( fun x _ s =>
                                       match M.find x (KK p) with
                                         | None => s
                                         | Some k =>
                                           match M.find x (KK (prog s)) with
                                             | Some k' => s
                                             | None =>
                                               let (t, _) := each_var s x k _ _ in t
                                           end
                                       end )
                                       (KK p) init_state.
    Next Obligation.
      map_trivial.
    Qed.
    Next Obligation.
      map_trivial.
    Qed.

    Lemma trans_all_0 :
      forall x,
        M.In x (KK p) ->
        M.In x (KK (prog trans_all)).
    Proof.
      unfold trans_all.
      apply MP.fold_rec_bis.

      + intros.
        apply H0.

        destruct H1 as [k H1].
        exists k.

        apply -> MF.Equal_mapsto_iff; eauto.

      + intros. map_trivial.

      + intros.

        rename x into x'.
        rename k into x.
        rename e into k.
        rename a into s.

        assert (M.find x (KK p) = Some k) by map_trivial.

        generalize (@eq_refl (option kind) (@M.find kind x (KK p))).
        pattern (M.find x (KK p)) at 1 3.
        rewrite H3.
        intros.

        generalize (@eq_refl (option kind) (@M.find kind x (KK (prog s)))).
        pattern (M.find x (KK (prog s))) at 1 3.
        destruct (M.find x (KK (prog s))).

        - intros.
          map_trivial.
          * exists k0. map_trivial.
          * intuition.

        - intros.
          remember (each_var s x k (trans_all_obligation_1 x k s k e e0)
                  (trans_all_obligation_2 x k s k e e0)). clear Heqs0.
          destruct s0 as [ t Ht ]. simpl'.

          map_trivial.
          intuition.
    Qed.

  End Impl.

  Section Nocyc.
    Variables p q : Program.
  
    Notation trans' := (trans p q).
    Notation transC' := (transC p q).
    Notation transR' := (transR p q).
    Notation nocyc_strong'  := (nocyc_strong  (KK p) (CC p) (EE p)).
    Notation nocyc_strongX' := (nocyc_strongX (KK p) (CC p) (EE p)).
    Notation nocyc_strongC' := (nocyc_strongC (KK p) (CC p) (EE p)).
    Notation nocyc'  := (nocyc  (KK q) (EE q)).
    Notation nocycX' := (nocycX (KK q) (EE q)).
    Notation well_type' := (well_type (TT p) (CC p)).
  
    Hypothesis He : forall x e, M.MapsTo x e (EE p) ->
                      exists2 e', M.MapsTo x e' (EE q) & trans p q e e'.
  
    Hypothesis Hin : forall x, M.MapsTo x Kin (KK p) -> M.MapsTo x Kin (KK q).
  
    Hypothesis Hwt : Pwell_type (TT p) (CC p) (EE p).

    Lemma nocyc_0 :
         ( forall e, nocyc_strong' e ->
                     well_type' e ->
                     forall e', trans' e e' -> nocyc' e' )
      /\ ( forall x, nocyc_strongX' x ->
                     nocycX' x /\
                     ( forall xc, transC' (Some x) xc -> nocycX' xc ) )
      /\ ( forall c, nocyc_strongC' c ->
                     forall xc, transC' c xc -> nocycX' xc ).
    Proof.
      apply CInocyc_strong; intros; simpl';
      
      try match goal with
        | [ H : trans _ _ _ _ |- _ ] => inversion H; clear H; subst
      end;

      try solve [ inversion_WT; eauto with constr ].

      + inversion_WT.
        inversion H8; clear H8; subst.
        eauto 50 with constr.
  
      + inversion_WT.
        inversion H11; clear H11; subst.
        eauto 50 with constr.
  
      + inversion_WT.
        inversion H12; clear H12; subst.
        eauto 50 with constr.
  
      + inversion_WT.
        inversion H10; clear H10; subst.
        inversion H12; clear H12; subst.
        eauto 100 with constr.
  
      + split.
        - eauto with constr.
        - intros.
          inversion H0; clear H0; subst; map_trivial.
          eauto 30 with constr.
  
      + split.
        - unfold Pwell_type in Hwt.
          specialize (He x e m). destruct He as [e' He1 He2].
          eauto with constr.
        - intros.
          inversion H1; clear H1; subst; map_trivial.
          eapply NCVdef; eauto; constructor.
          * eauto with constr.
          * eauto with constr.
            specialize (He x e m). destruct He as [e' He1 He2].
            eauto with constr.
          * eauto with constr.
  
      + inversion H; clear H; subst.
        eauto with constr.
    Qed.
  End Nocyc.

  Arguments prog [p] s.

  Definition translate p WF := prog (trans_all p WF).

  Theorem trans_k :
    forall p WF x k,
      M.MapsTo x k (KK p) ->
      M.MapsTo x k (KK (translate p WF)).
  Proof.
    intros.

    unfold translate in *.
    remember (trans_all p WF) as s.

    assert (M.In x (KK p)) by eauto.

    assert (M.In x (KK (prog s))).
      subst s. apply trans_all_0. assumption.
    destruct H1 as [k' H1].

    assert (is_orig p x).
      apply is_orig_0; auto.

    assert (M.MapsTo x k' (KK p)).
      destruct s; simpl in *. eauto.

    map_trivial.
  Qed.

  Theorem trans_i :
    forall p WF x,
      M.MapsTo x Kin (KK p) <->
      M.MapsTo x Kin (KK (translate p WF)).
  Proof.
    intros.
    split.
    + apply trans_k.
    + intros.
      unfold translate in *.
      eapply state_in; eauto.
  Qed.

  Theorem trans_o :
    forall p WF x,
      M.MapsTo x Kout (KK p) <->
      M.MapsTo x Kout (KK (translate p WF)).
  Proof.
    intros.
    split; intros.
    + apply trans_k.
      assumption.
    + eapply state_out; eauto.
  Qed.

  Theorem trans_t :
    forall p WF x tp tq,
      M.MapsTo x tp (TT p) ->
      M.MapsTo x tq (TT (translate p WF)) ->
      tp = tq.
  Proof.
    intros.

    unfold translate in *.
    destruct (trans_all p WF); simpl in *.

    assert (M.MapsTo x tq (TT p)).
      eapply orig_t0; eauto.
      apply is_orig_0.
      kind_consistent.

    map_trivial.
  Qed.

  Theorem trans_c :
    forall p WF x c,
      M.MapsTo x c (CC (translate p WF)) ->
      c = None.
  Proof.
    intros.

    unfold translate in *.
    destruct trans_all; simpl in *.

    eapply all_c0; eauto.
  Qed.

  Theorem trans_e :
    forall p WF x ep eq,
      M.MapsTo x ep (EE p) ->
      M.MapsTo x eq (EE (translate p WF)) ->
      trans p (translate p WF) ep eq.
  Proof.
    intros.
    unfold translate in *.
    destruct trans_all; simpl in *.

    eapply orig_e0; eauto.
    apply is_orig_0.
    kind_consistent.
  Qed.

  Theorem GoodProperties :
    forall p WF q,
      translate p WF = q ->
      WellFormed q.
  Proof.
    intros.

    constructor;
    unfold translate in *; remember (trans_all p WF); destruct s; simpl in *;
    subst prog0;

    try solve [ subst; assumption ].

    (* Pclk_nocyc_inp *)
    + unfold Pclk_nocyc_inp; intros.
      apply NIinit; try assumption.

      assert (HH: M.In x (CC q)).
        kind_consistent.
      destruct HH as [ c HH ].

      assert (c = None).
        eauto.

      subst. assumption.

    (* Pclk_bool_inp *)
    + unfold Pclk_bool_inp; intros.

      assert (Some x' = None).
        eauto.
      discriminate.

    (* Pout_clk_in *)
    + unfold Pout_clk_in. intros.

      assert (q = translate p WF).
        unfold translate. rewrite <- Heqs. reflexivity.

      assert (Some x' = None).
        subst q.
        eapply trans_c; eauto.

      discriminate.

    (* Pin_clk_in *)
    + unfold Pin_clk_in. intros.

      assert (Some x' = None).
        eauto.
      discriminate.

    (* Pwell_type *)
    + unfold Pwell_type; intros.
      unfold well_typeF in all_wt0.
      eapply all_wt0; eauto.
      - intros.

        assert (M.In x0 (KK p)).
          kind_consistent.

        assert (M.In x0 (KK q)).
        { cutrewrite ( q = prog (trans_all p WF) ).
          * apply trans_all_0. assumption.
          * rewrite <- Heqs. reflexivity. }

        assert (HH: M.In x0 (TT q)).
          kind_consistent.
        destruct HH as [ t' HH ].

        assert (M.MapsTo x0 t' (TT p)).
          eapply orig_t with (s := trans_all p WF); eauto.
          apply is_orig_0.
          assumption.
          rewrite <- Heqs. assumption.

        map_trivial.
      - intros.

        assert (M.In x0 (KK q)).
          kind_consistent.

        assert (HH: M.In x0 (CC q)).
          kind_consistent.
        destruct HH as [ c HH ].

        assert (c = None).
          eapply all_c0; eauto.

        subst c; assumption.

    (* Pnocyc *)
    + destruct nocyc_0 with (p:=p) (q:=q) as [ HHe [ HHx HHc ] ].
      - intros.

        assert (HH1: M.In x (KK p)).
          kind_consistent.

        assert (HH2: M.In x (KK q)).
          cutrewrite (q = prog (trans_all p WF)).
            apply trans_all_0; assumption.
          rewrite <- Heqs. reflexivity.
        destruct HH2 as [ kq HH2 ].

        assert (HH3 : M.MapsTo x Kout (KK p) \/ M.MapsTo x Kloc (KK p)).
          kind_consistent.

        assert (M.MapsTo x kq (KK p)).
          eapply orig_k0; eauto.
          apply is_orig_0.
          assumption.

        assert (M.MapsTo x Kout (KK q) \/ M.MapsTo x Kloc (KK q)).
          kind_case; [left | right]; map_trivial; assumption.

        assert (HH5: M.In x (EE q)).
          kind_consistent.
        destruct HH5 as [eq HH5].

        exists eq.
        * assumption.
        * eapply orig_e0; eauto.
          apply is_orig_0.
          assumption.

      - intros.
        cutrewrite (q = translate p WF).
          apply trans_k. assumption.
        unfold translate.
        rewrite <- Heqs. simpl. reflexivity.

      - destructP; assumption.

      - unfold Pnocyc. intros.

        destruct (disjoint_0 p x) as [ HH1 | [ HH2 | [ HH3 | [ HH4 | [ HH5 | HH6 ] ] ] ] ].
        
        * destruct (HHx x).
            destruct H as [kq H].
            assert (M.MapsTo x kq (KK p)).
              eapply orig_k0; assumption.

          program_trivial. assumption.

        * apply is_xc_1 in HH2.
          destruct HH2 as [x' HH2].
          rename H0 into HH3.
          subst x.

          apply HHc with (c := Some x').
          { constructor.
            eapply program_Pnocyc_strong; eauto.
            
            apply xc_e0 in H.
            * inversion H.
              kind_consistent.
            
            * assumption. }

          apply xc_e0; assumption.

        * { apply HHc with (c := None).
            - constructor.
            - unfold is_xcn in HH3.
              subst x.

              eapply xcn_e0; eauto. }

        * apply is_xf_1 in HH4.
          destruct HH4 as [x' HH4].
          rename H0 into HH5.
          subst x.

          apply xf_e0 in H; [ | assumption ].
          inversion H. subst.

          eauto with constr.

        * unfold is_xfn in HH5.
          subst x.

          apply xfn_e0 in H.
          inversion H.

          eauto with constr.

        * apply new_nocyc0 in HH6; [ | assumption ].

          destruct HH6 as [ ep [ eq HH6 ] ].
          simpl'.

          assert (nocyc (KK q) (EE q) eq).
            eapply HHe; eauto.

            program_trivial.

          apply H2; assumption.
  Qed.

  Theorem GlobalClockExpressions :
    forall p WF x e,
      M.MapsTo x e (EE (translate p WF)) ->
      global_clock_expr e.
  Proof.
    intros.

    unfold translate in *.
    destruct trans_all; simpl in *.

    eapply all_gc0; eauto.
  Qed.

End TranslationImpl.

(* Though some axioms are imported implicitly via the 'Program' module, we do
   not actually depend on them as shown by 'Print Assumptions' *)
Print Assumptions TranslationImpl.GoodProperties.
Print Assumptions TranslationImpl.GlobalClockExpressions.
Print Assumptions TranslationImpl.translate.
Print Assumptions TranslationImpl.trans_c.
Print Assumptions TranslationImpl.trans_t.
Print Assumptions TranslationImpl.trans_k.
Print Assumptions TranslationImpl.trans_i.
Print Assumptions TranslationImpl.trans_o.
Print Assumptions TranslationImpl.trans_e.


Require Import ClockUnifyProof.

Module TranslationCorrectness := TranslationProof TranslationImpl.
