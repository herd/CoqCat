(*********************************************************************)
(*             Stability in Weak Memory Models                       *)
(*                                                                   *)
(*   Jade Alglave INRIA Paris-Rocquencourt, France                   *)
(*                University of Oxford, UK                           *)
(*                                                                   *)
(*  Copyright 2010 Institut National de Recherche en Informatique et *)
(*  en Automatique. All rights reserved. This file is distributed    *)
(*  under the terms of the Lesser GNU General Public License.        *)
(*********************************************************************)

Require Import Ensembles.
Require Import Arith.
Require Import Bool.
From CoqCat Require Import util.
From CoqCat Require Import wmm.
From CoqCat Require Import basic.
From CoqCat Require Import hierarchy.
Require Import Classical_Prop.
From CoqCat Require Import racy.
From CoqCat Require Import valid.
From CoqCat Require Import covering.
Import OEEvt.
Set Implicit Arguments.

Module Rmw (A:Archi) (dp:Dp).

Module ABasic := Basic A dp.

Module ARes <: Archi.
Parameter ppo : Event_struct -> Rln Event.
Hypothesis ppo_valid : forall E, rel_incl (ppo E) (po_iico E).
Hypothesis ppo_fun :
  forall E s x y,
  ppo E x y /\ s x /\ s y <->
  ppo (mkes (Intersection Event (events E) s) (rrestrict (iico E) s)) x y.
Parameter inter : bool.
Parameter intra : bool.
Definition ppo_sub E :=
  fun e1 => fun e2 => A.ppo E e1 e2 /\ ~(ppo E e1 e2).

Inductive wAB_Wa (E:Event_struct) (fenced:Rln Event) : Event -> Event -> Prop :=
  | wBaseW : forall e1 e2, (*events E e1 -> events E e2 ->*)
      fenced e1 e2 (*/\ (writes E e1)*) -> wAB_Wa E fenced e1 e2.
Definition abc E (X:Execution_witness) := wAB_Wa E (po_iico E).
Lemma ab_evts : forall (E:Event_struct) (X:Execution_witness),
  forall x y, well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  abc E X x y -> In _ (events E) x /\ In _ (events E) y.
Proof.
intros E X x y Hwf Hrf Hxy.
inversion Hxy.
split; auto.
apply ABasic.po_iico_domain_in_events with y; auto.
apply ABasic.po_iico_range_in_events with x; auto.
Qed.
Lemma ab_incl :
  forall E X, rel_incl (abc E X) (tc (rel_union (hb E X) (po_iico E))).
Proof.
intros E X x y Hxy. inversion Hxy.
apply trc_step; right; auto.
Qed.
(*Lemma ab_fun :
  forall E X s x y,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  (abc E X x y /\ s x /\ s y <->
  abc (mkes
   (Intersection Event (events E) s) (rrestrict (iico E) s))
    (mkew (rrestrict (ws X) s) (rrestrict (rf X) s)) x y).
Proof.
unfold abc; intros E X s x y Hwf Hrfwf; split; intro Hxy.
  destruct Hxy as [Hxy ?]; destruct Hxy; destruct H; split.
    apply ABasic.po_rr; auto.

  split; inversion Hxy.
    apply wBaseW; apply ABasic.po_rr_bak with (fun w => (exists e, rf X w e /\ s e /\ ~ s w ) \/ init w) final s; auto.
    apply ABasic.po_rr_bak_s with E (fun w => (exists e, rf X w e /\ s e /\ ~ s w ) \/ init w) final; auto.
Qed.*)

Parameter stars : Event_struct -> set Event.
End ARes.

Import ARes.
Module AResBasic := Basic ARes dp.
Import AResBasic.
Module AResWmm := Wmm ARes dp.
Import AResWmm.
Module An <: Archi.
Definition ppo := A.ppo.
Lemma ppo_valid : forall E, rel_incl (ppo E) (po_iico E).
  apply A.ppo_valid.
Qed.
Lemma ppo_fun :
  forall E s x y,
  ppo E x y /\ s x /\ s y <->
  ppo (mkes (Intersection Event (events E) s) (rrestrict (iico E) s)) x y.
Proof.
  apply A.ppo_fun.
Qed.
Definition inter := A.inter.
Definition intra := A.intra.
Definition abc (E:Event_struct) (X:Execution_witness) : Rln Event :=
  fun e1 => fun e2 => False.
Lemma ab_evts : forall (E:Event_struct) (X:Execution_witness),
  forall x y, well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  abc E X x y -> In _ (events E) x /\ In _ (events E) y.
Proof.
intros E X x y Hwf Hrf Hxy. inversion Hxy.
Qed.
Lemma ab_incl :
  forall E X, rel_incl (abc E X) (tc (rel_union (hb E X) (po_iico E))).
Proof.
intros E X x y Hxy. inversion Hxy.
Qed.
Lemma ab_fun :
  forall E X s x y,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  (abc E X x y /\ s x /\ s y <->
  abc (mkes
   (Intersection Event (events E) s) (rrestrict (iico E) s))
    (mkew (rrestrict (ws X) s) (rrestrict (rf X) s)) x y).
Proof.
intros E X s x y Hwf Hrfwf; split; intro Hxy.
  destruct Hxy as [Hxy ?]; inversion Hxy.
  inversion Hxy.
Qed.

Parameter stars : Event_struct -> set Event.
End An.
Module AnWmm := Wmm An dp.
Module Wk := (*Hierarchy.*)Weaker An ARes dp.
Module VA := Valid An dp.
Import VA. Import VA.ScAx.
Module Covering := Covering ARes An dp.
Import Covering.

Axiom excluded_middle : forall (A:Prop), A \/ ~A.

Definition atom (E:Event_struct) (X:Execution_witness) (r w: Event) (l:Location): Prop :=
  reads E r /\ stars E r /\ loc r = l /\
  writes E w /\ stars E w /\ loc w = l /\ po_iico E r w /\
  ~(exists e, stars E e /\ po_iico E r e /\ po_iico E e w) /\
                  ~(exists w', proc_of w' <> proc_of r /\
                       writes E w' /\ loc w' = l /\ fr E X r w' /\ ws X w' w). (*w' pas sur le meme proc*)

Ltac destruct_atom H :=
  destruct H as [Hr [Hatr [Hlr [Hw [Haw [Hlw [Hporw [Hnoc Hno]]]]]]]].

Inductive rmw (E:Event_struct) (X:Execution_witness) (r w:Event) (l:Location) : Prop :=
  | Atom : atom E X r w l -> rmw E X r w l
  | Loop : (exists r', po_iico E r r' /\ loc r = loc r' /\ atom E X r' w l) -> rmw E X r w l.

Definition rrmw (E:Event_struct) (X:Execution_witness) : Prop :=
  forall r, (exists w, Wk.rf_sub X w r) ->
    (exists w, rmw E X r w (*l*) (loc r) /\ forall e, po_iico E r e -> po_iico E w e).

Module R := Racy ARes A dp.
Import R.
Import Wk.
Import ARes.
Import AResBasic.
Import AResWmm.
Module SN <: R.SafetyNet.
Definition fragile X r :=
  exists w, rf_sub X w r.
Definition competing E X :=
  rel_union (ppo_sub E) (fun e1 e2 => A.ppo E e1 e2 /\ fragile X e1).
(*Definition competing E X :=
  rel_union (ppo_sub E) (rel_seq (rf_sub X) (A.ppo E)). *)

Definition sx E X :=
  rel_union (ppo_sub E) (fun e1 e2 => A.ppo E e1 e2 /\ fragile X e1). (*(rel_seq (rf_sub X) (A.ppo E)).*)
Hypothesis s_ac : forall E X, AC X (sx E X).

Definition po_Wr E :=
  fun e1 => fun e2 => po_iico E e1 e2 /\ writes E e2.
Definition po_Wl E :=
  fun e1 => fun e2 => po_iico E e1 e2 /\ writes E e1.
Definition po_WW E :=
  fun e1 => fun e2 => po_iico E e1 e2 /\ (writes E e1 /\ writes E e2).

Definition pio_Wr E :=
  fun e1 => fun e2 => pio E e1 e2 /\ writes E e2.
Definition pio_Wl E :=
  fun e1 => fun e2 => pio E e1 e2 /\ writes E e1.
Definition pio_WW E :=
  fun e1 => fun e2 => pio E e1 e2 /\ (writes E e1 /\ writes E e2).

Lemma po_Wr_Wl_implies_po_WW :
  forall E x y z,
  well_formed_event_structure E ->
  (po_Wl E) x y /\ (po_Wr E) y z ->
  (po_WW E) x z.
Proof.
intros E x y z Hwf [[Hxy Hwx] [Hyz Hwz]].
split; [|split]; auto.
apply po_trans with y; auto.
Qed.

Lemma pio_Wr_Wl_implies_pio_WW :
  forall E x y z,
  well_formed_event_structure E ->
  (pio_Wl E) x y /\ (pio_Wr E) y z ->
  (pio_WW E) x z.
Proof.
intros E x y z Hwf [[Hxy Hwx] [Hyz Hwz]].
split; [|split]; auto.
split; destruct Hxy; destruct Hyz;
[|apply po_trans with y; auto].
  rewrite H; auto.
Qed.

Definition hbd (E:Event_struct) (X:Execution_witness) : Rln Event :=
  fun e1 => fun e2 => hb E X e1 e2 /\ proc_of e1 <> proc_of e2.

(*Definition ppo_Wl E :=
  fun e1 => fun e2 => A.ppo E e1 e2 /\ writes E e1.*)
Definition ghb_po_Wl E X :=
  fun e1 => fun e2 => AResWmm.ghb E X e1 e2 /\ po_iico E e1 e2 /\ writes E e1.

Lemma fno_rf_seq_po_implies_ws_seq_po :
  forall E X,
  well_formed_event_structure E ->
  valid_execution E X -> rrmw E X ->
  rel_incl (rel_seq (rf_sub X) (A.ppo E)) (rel_seq (ws X) (po_Wl E)).
Proof.
unfold rrmw;
intros E X Hwf Hv Hfno w e [r [Hrfs Hppo]].
generalize Hv; intro Hva.
destruct_valid Hv.
assert (rf X w r) as Hrf.
  destruct Hrfs; apply mrf2_in_rf; auto.
generalize (ran_rf_is_read E X w r Hrf_cands Hrf); intro Hrr.
assert (reads E r) as Hreads.
  split; auto.
  eapply (ran_rf_in_events); auto.
    split; auto. apply Hrf.
  destruct Hrr as [l [v Haction_r]].
  assert (loc r = l) as Hl.
    unfold loc; rewrite Haction_r; auto.
    assert (exists w, rf_sub X w r) as Hrrf.
    exists w; auto.
  generalize (Hfno r Hrrf); intros [wr [Hrmw Haf]].
  inversion Hrmw as [Himm | Hult].

  (*rmw r w*)
  destruct_atom Himm.
  exists wr.
assert (ws X w wr \/ ws X wr w) as Hor.
  destruct_lin (Hws_tot (loc r)).
  assert (w <> wr) as Hdiff.
    generalize (excluded_middle (w <> wr)); intro Hor.
    inversion Hor; auto.

      assert (w = wr) as Heq.
        apply NNPP; auto.
    assert (tc (rel_union (hb E X) (pio_llh E)) r r) as Hcy.
      rewrite <- Heq in Hporw.
      apply trc_ind with w; apply trc_step; [right; split; auto | left; left; left; auto].
      apply sym_eq; apply rf_implies_same_loc2 with E X; auto.
        split; split; auto.
        split; auto.
        rewrite Heq; intros [? [? [? [? Hrwr]]]];
        destruct Hw as [? [? [?  Hwwr]]];
        rewrite Hrwr in Hwwr; inversion Hwwr.
    unfold acyclic in Hsp; unfold not in Hsp; assert False as Ht.
      apply (Hsp r Hcy). inversion Ht.

  assert (In _ (writes_to_same_loc_l (events E) (loc r)) w) as Hew.
    split.
      eapply (dom_rf_in_events); auto.
        split; auto. apply Hrf.
        eapply rf_implies_same_loc;
          [apply Hva | apply Hrf | unfold read_from; exists v; auto].
    rewrite Hl; auto.
  assert (In _ (writes_to_same_loc_l (events E) (loc r)) wr) as Hewr.
    split; destruct Hw as [Hevw [lw [vw Hacw]]]; auto; exists vw; auto.
    rewrite <- Hlw; unfold loc; rewrite Hacw; auto.

  generalize (Htot w wr Hdiff Hew Hewr); intro Hor.
  inversion Hor as [Hwwr | Hwrw].
    left; destruct Hwwr; auto.
    right; destruct Hwrw; auto.
  inversion Hor as [Hy | Hn]; split; auto.
      split; [ | auto]. apply Haf; apply A.ppo_valid; auto.

      assert (fr E X r wr) as Hfr.
        split.
          apply po_iico_domain_in_events with e; auto.
        apply A.ppo_valid; auto.
          split.
            apply po_iico_range_in_events with r; auto.
            exists w; split; auto.
            assert (tc (rel_union (hb E X) (pio_llh E)) w w) as Hc.
              apply trc_ind with r.
                apply trc_step; left; left; left; auto.
                apply trc_ind with wr; apply trc_step.
                  right; split; auto.
                  split; auto.
                  intros [? [? [? [? Hrwr]]]];
                  destruct Hw as [? [? [? Hwwr]]];
                  rewrite Hrwr in Hwwr; inversion Hwwr.
                  left; right; auto.
            assert False as Htriv.
              apply (Hsp w Hc). inversion Htriv.

    destruct Hfr as [Her [Hewr [ew [Hrfr Hwsr]]]].
    generalize (Hrf_uni r w ew Hrf Hrfr); intro Heq.
      rewrite <- Heq in Hwsr.
    assert (ws X w w) as Hcy.
      apply ws_trans with E wr; auto; split; auto.
    generalize (ws_cy E X w Hws_tot Hws_cands); intro Hc.
    contradiction.

      assert (po_iico E r e) as Hpo.
        apply A.ppo_valid; auto.
      split; auto.

(*succes ultimately*)

destruct Hult as [r' [Hporr' [Heq_loc Hatom]]].
  destruct_atom Hatom.
  assert (po_iico E r' e \/ po_iico E e r') as Horpor'e.
    assert (po_iico E r e) as Hpore.
      apply A.ppo_valid; auto.
    assert (In _ (events E) r) as Her.
      apply po_iico_domain_in_events with e; auto.
    assert (In _ (events E) r') as Her'.
      apply po_iico_domain_in_events with wr; auto.
    assert (In _ (events E) e) as Hee.
      apply po_iico_range_in_events with r; auto.
    generalize (po_implies_same_proc Hwf Her Hee Hpore); intro Hpre.
    generalize (po_implies_same_proc Hwf Her Her' Hporr'); intro Hprr'.
    assert (proc_of e = proc_of r') as Hper'.
      rewrite <- Hpre; rewrite Hprr'; auto.
    apply (same_proc_implies_po); auto.
  inversion Horpor'e as [Haft | Hbef].

(*e after r' in po*)

 exists wr.
assert (ws X w wr \/ ws X wr w) as Hor.
  destruct_lin (Hws_tot l).
  assert (w <> wr) as Hdiff.
    generalize (excluded_middle (w <> wr)); intro Hor.
    inversion Hor; auto.

      assert (w = wr) as Heq.
        apply NNPP; auto.
    assert (tc (rel_union (hb E X) (pio_llh E)) r r) as Hcy.
      rewrite <- Heq in Hporw.
      apply trc_ind with w; apply trc_step; [right; split; auto | left; left; left; auto].
      apply sym_eq; apply rf_implies_same_loc2 with E X; auto.
        split; split; auto.
       split.
       apply po_trans with r'; auto.
       rewrite Heq; intros [? [? [? [? Hrwr]]]];
       destruct Hw as [? [? [? Hwwr]]]; rewrite Hrwr in Hwwr; inversion Hwwr.
    unfold acyclic in Hsp; unfold not in Hsp; assert False as Ht.
      apply (Hsp r Hcy). inversion Ht.

  assert (In _ (writes_to_same_loc_l (events E) l) w) as Hew.
    split.
      eapply (dom_rf_in_events); auto.
        split; auto. apply Hrf.
        eapply rf_implies_same_loc;
          [apply Hva | apply Hrf | unfold read_from; exists v; auto].
  assert (In _ (writes_to_same_loc_l (events E) l) wr) as Hewr.
    split; destruct Hw as [Hevw [lw [vw Hacw]]]; auto; exists vw; auto.
    rewrite <- Hl; rewrite <- Hlw; unfold loc; rewrite Hacw; auto.

  generalize (Htot w wr Hdiff Hew Hewr); intro Hor.
  inversion Hor as [Hwwr | Hwrw].
    left; destruct Hwwr; auto.
    right; destruct Hwrw; auto.
  inversion Hor as [Hy | Hn]; split; auto.
      assert (po_iico E r e) as Hpo.
        apply A.ppo_valid; auto.
      split; auto.

      assert (fr E X r wr) as Hfr.
        split.
      assert (po_iico E r e) as Hpo.
        apply A.ppo_valid; auto.
          apply po_iico_domain_in_events with e; destruct Hpo; auto.
            apply po_trans with r'; auto.
            apply po_trans with r'; auto.
          split.
            apply po_iico_range_in_events with r'; auto.
            exists w; split; auto.
            assert (tc (rel_union (hb E X) (pio_llh E)) w w) as Hc.
              apply trc_ind with r.
                apply trc_step; left; left; left; auto.
                apply trc_ind with wr; apply trc_step.
                  right; split; auto.
                 split; auto.
                  apply po_trans with r'; auto.
                  intros [? [? [? [? Hrwr]]]];
                  destruct Hw as [? [? [? Hwwr]]];
                  rewrite Hwwr in Hrwr; inversion Hrwr.
                  left; right; auto.
            assert False as Htriv.
              apply (Hsp w Hc). inversion Htriv.

    destruct Hfr as [Her [Hewr [ew [Hrfr Hwsr]]]].
    generalize (Hrf_uni r w ew Hrf Hrfr); intro Heq.
      rewrite <- Heq in Hwsr.
    assert (ws X w w) as Hcy.
      apply ws_trans with E wr; auto; split; auto.
    generalize (ws_cy E X w Hws_tot Hws_cands); intro Hc.
    contradiction.

      assert (po_iico E r e) as Hpo.
        apply A.ppo_valid; auto.
     split; auto.

   (*e before r' in po*)
   assert (po_iico E e wr) as Hpoc.
     apply po_trans with r'; auto.
     generalize (A.ppo_valid Hppo); intro Hpo.
     generalize (Haf e Hpo); intro Hc.
   assert (po_iico E e e) as Hcy.
     apply po_trans with wr; auto.
   generalize (po_ac Hwf Hcy); intro Ht; inversion Ht.
Qed.

Lemma fr_po :
  forall E X x y,
  well_formed_event_structure E ->
  valid_execution E X ->
  reads E x ->
  writes E y ->
  po_iico E x y ->
  loc x = loc y ->
  fr E X x y.
Proof.
intros E X x y Hwf Hv Hrx Hwy Hpo Hl.
generalize Hv; intro Hva.
destruct_valid Hv; generalize (Hrf_init x Hrx);
  intros [wx [Horx Hrfx]].
  split; [|split; [|exists wx; split]]; auto.
  apply ran_rf_in_events with X wx; auto.
    split; auto.
  apply po_iico_range_in_events with x; auto.
  generalize (Hws_tot (loc x)); intro Hlin;
  destruct_lin Hlin.
  generalize (excluded_middle (wx <> y)); intro Hord;
  inversion Hord as [Hdiff | Hnd].
    assert (In _ (writes_to_same_loc_l (events E) (loc x)) wx) as Hewx.
      split; auto.
  (*apply dom_rf_in_events with X x; auto.
    split; auto.*)

      apply rf_implies_same_loc with E X x; auto.
      destruct Hrx as [? [? [v Hrx]]]; exists v; auto.
      unfold loc; rewrite Hrx; auto.
    assert (In _ (writes_to_same_loc_l (events E) (loc x)) y) as Hey.
      destruct Hwy as [? [? [v Hwy]]]; split; auto.
      exists v; rewrite Hl; unfold loc; rewrite Hwy; auto.
    generalize (Htot wx y Hdiff Hewx Hey); intro Hor;
    inversion Hor as [Hwxy | Hywx].
    destruct Hwxy; auto.
    destruct Hywx as [Hywx ?].
    assert False as Htriv.
      assert (tc (rel_union (hb E X) (pio_llh E)) wx wx) as Hcy.
        apply trc_ind with x;
        [apply trc_step; left; left; left |
         apply trc_ind with y; apply trc_step;
           [right; split; [|split] | left; right]]; auto.
        intros [? [? [? [? Hry]]]]; destruct Hwy as [? [? [? Hwy]]];
        rewrite Hwy in Hry; inversion Hry.
      unfold acyclic in Hsp; apply (Hsp wx Hcy).
      inversion Htriv.

  assert (wx = y) as Heq.
    apply NNPP; auto.

    assert False as Htriv.
      assert (tc (rel_union (hb E X) (pio_llh E)) wx wx) as Hcy.
        apply trc_ind with x;
        [apply trc_step; left; left; left |
         subst; apply trc_step; right; split; [|split]]; auto.
        intros [? [? [? [? Hry]]]]; destruct Hwy as [? [? [? Hwy]]];
        rewrite Hwy in Hry; inversion Hry.
      unfold acyclic in Hsp; apply (Hsp wx Hcy).
      inversion Htriv.
Qed.

Lemma rmw_in_fr :
  forall E X x y l,
  well_formed_event_structure E ->
  valid_execution E X ->
  reads E x ->
  rmw E X x y l ->
  fr E X x y.
Proof.
intros E X x y l Hwf Hv Hrx Hrmw.
inversion Hrmw.
  destruct_atom H.
  apply fr_po; auto.
  subst; auto.

  destruct H as [r [Hpo_xr [Hl Hatom]]].
  destruct_atom Hatom.
  assert (po_iico E x y) as Hpo.
    apply po_trans with r; auto.
  apply fr_po; auto. subst; rewrite Hl; auto.
Qed.

Lemma sx_in_ghb :
  forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
  rrmw E X ->
  rel_incl (sx E X) (tc (AResWmm.ghb E X)).
Proof.
intros E X Hwf Hv Hrrmw x y Hxy.
  inversion Hxy as [Hppo | Hrf].
   apply trc_step; apply AResBasic.ab_in_ghb; unfold abc; apply wBaseW; auto.
   destruct Hppo; apply A.ppo_valid; auto.
  destruct Hrf as [Hppo ?].
   apply trc_step; apply AResBasic.ab_in_ghb; unfold abc; apply wBaseW; auto.
   apply A.ppo_valid; auto.
Qed.

(*generalize (excluded_middle (writes E x)); intro Hor;
inversion Hor as [Hwx | Hnwx].
  inversion Hxy; [apply trc_step|].
    apply AResBasic.ab_in_ghb;
    unfold abc; apply wBaseW;
    destruct H. apply A.ppo_valid; auto.
    generalize (fno_rf_seq_po_implies_ws_seq_po Hwf Hv Hrrmw);
    intro Hincl.
    destruct H as [Hppoxy [z Hzx]].
   apply trc_step; apply AResBasic.ab_in_ghb; unfold abc; apply wBaseW; auto.
   apply A.ppo_valid; auto.

    assert (rel_seq (ws X) (po_Wl E) x y) as Hin.
      apply Hincl; auto.
    destruct Hin as [z [Hws Hpo]].
      apply trc_ind with z; apply trc_step;
      [apply ws_in_ghb |
       apply AResBasic.ab_in_ghb; unfold abc; apply wBaseW; destruct Hpo]; auto.

  inversion Hxy as [Hppo | Hrf].
   apply trc_step; apply AResBasic.ab_in_ghb; unfold abc; apply wBaseW; auto.
   destruct Hppo; apply A.ppo_valid; auto.

    destruct Hrf as [z [[Hmrf2 ?] ?]].
    assert (rf X x z) as Hrf.
      apply mrf2_in_rf; auto.
    assert (writes E x) as Hc.
      split.
        apply dom_rf_in_events with X z; auto; destruct_valid Hv; split; auto.
        apply dom_rf_is_write with E X z; auto; destruct_valid Hv; auto.
    contradiction.
Qed.*)

Set Implicit Arguments.
Lemma tc_tc :
  forall A (r: Rln A),
  rel_incl (tc (tc r)) (tc r).
Proof.
intros A r x y Hxy.
induction Hxy; auto.
apply trc_ind with z; auto.
Qed.
Unset Implicit Arguments.

Hypothesis rmwt :
  forall E X, rrmw E X.

Lemma sx_ghb :
  forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
  acyclic (rel_union (sx E X) (AResWmm.ghb E X)).
Proof.
intros E X Hwf Hv.
apply incl_ac with (tc (AResWmm.ghb E X)).
  intros x y Hxy; inversion Hxy; auto.
    apply sx_in_ghb; auto.
      apply rmwt.
    apply trc_step; auto.
  destruct_valid Hv; auto.
  unfold acyclic; unfold acyclic in Hvalid; intros x Hx.
  assert (tc (ghb E X) x x) as Htc.
    apply tc_tc; auto.
  apply (Hvalid x Htc).
Qed.

Definition s E X := sx E X.
Definition cns E X :=
  fun e1 => fun e2 => competing E X e1 e2 /\ ~ (s E X e1 e2 \/ s E X e2 e1).

Lemma s_ghb :
  forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
  acyclic (rel_union (s E X) (AResWmm.ghb E X)).
Proof.
apply sx_ghb.
Qed.

Definition convoluted_wf :=
  forall E X Y x y,
  competing E X x y ->
  ~ (s E X x y \/ s E X y x) ->
  rf Y = so_rfm E
         (LE (tc (rel_union (rel_union (rel_inter (cns E X) (pair x y)) (A.ppo E)) (pio_llh E)))) ->
  ws Y = so_ws
         (LE (tc (rel_union (rel_union (rel_inter (cns E X) (pair x y)) (A.ppo E)) (pio_llh E)))) ->
  competing E Y x y /\ ~ (s E Y x y \/ s E Y y x).

Lemma convoluted_prop_stable :
  convoluted_wf.
(*  forall E X Y x y,
  competing E X x y ->
  ~ (s E X x y \/ s E X y x) ->
  rf Y = so_rfm E
         (LE (tc (rel_union (rel_union (rel_inter (cns E X) (pair x y)) (A.ppo E)) (pio_llh E)))) ->
  ws Y = so_ws
         (LE (tc (rel_union (rel_union (rel_inter (cns E X) (pair x y)) (A.ppo E)) (pio_llh E)))) ->
  competing E Y x y /\ ~ (s E Y x y \/ s E Y y x).*)
Proof.
intros E X Y x y Hxy Hnxy Hrf Hws.
unfold competing in Hxy; unfold SN.s in Hxy.
unfold SN.s in Hnxy; unfold SN.sx in Hnxy.
assert (rel_union (ppo_sub E)
          (fun e1 e2 : Event => A.ppo E e1 e2 /\ fragile X e1) x y \/
        rel_union (ppo_sub E)
          (fun e1 e2 : Event => A.ppo E e1 e2 /\ fragile X e1) y x) as Hc.
  left; auto.
contradiction.
Qed.

Lemma compete_in_events :
  forall E X x y,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  competing E X x y ->
  events E x /\ events E y.
Proof.
intros E X x y Hwf Hwfrf Hc; inversion Hc as [Hppo | Hrf].
  destruct Hppo; split;
    [change (events E x) with (In _ (events E) x);
     apply ABasic.po_iico_domain_in_events with y |
     change (events E y) with (In _ (events E) y);
     apply A2Basic.po_iico_range_in_events with x]; auto;
    apply A.ppo_valid; auto.
  destruct Hrf as [Hppo Hrf]; split;
  [change (events E x) with (In _ (events E) x);
    destruct Hrf as (*[? [[? ?] ?]]*) [z Hrf]|
   change (events E y) with (In _ (events E) y);
   apply A2Basic.po_iico_range_in_events with (*z*) x; auto; apply A.ppo_valid]; auto.
    destruct Hrf as [? ?];
   apply A2Basic.ran_rf_in_events with X z; auto.
   apply mrf2_in_rf; auto.
Qed.

Lemma udr_xy_ppo2_in_events :
  forall E X r x y,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  competing E X x y ->
  Included _   (Union _ (dom (tc (rel_union (rel_union (rel_inter r (pair x y)) (A.ppo E)) (pio_llh E))))
     (ran (tc (rel_union (rel_union (rel_inter r (pair x y)) (A.ppo E)) (pio_llh E))))) (events E).
Proof.
intros E X r x y Hwf Hwfrf Hc e1 Hudr.
generalize (compete_in_events E X x y Hwf Hwfrf Hc); intros [Hex Hey].
inversion Hudr as [e Hd |e Hr].
generalize (dom_tc_in_dom Hd); intros [e2 Hi];
  inversion Hi as [Hu | Hpio].
  inversion Hu as [Hp | Hppo].
  destruct Hp as [? [? ?]]; subst; auto.
apply ABasic.po_iico_domain_in_events with e2; auto.
apply A.ppo_valid; auto.
destruct Hpio as [? [Hpo ?]].
apply ABasic.po_iico_domain_in_events with e2; auto.
generalize (ran_tc_in_ran Hr); intros [e2 Hi];
  inversion Hi as [Hu | Hpio].
  inversion Hu as [Hp | Hppo].
  destruct Hp as [? [? ?]]; subst; auto.
apply ABasic.po_iico_range_in_events with e2; auto.
apply A.ppo_valid; auto.
destruct Hpio as [? [Hpo ?]].
apply ABasic.po_iico_range_in_events with e2; auto.
Qed.

Ltac destruct_valid H :=
  destruct H as [[Hws_tot Hws_cands] [[Hrf_init [Hrf_cands Hrf_uni]] [Hsp [Hth Hvalid]]]];
  unfold write_serialization_well_formed in Hws_tot(*; unfold uniproc in Hsp*).

Lemma u_in_pair_po :
  forall E X x y e1 e2,
  tc (rel_union (rel_union (rel_inter (cns E X) (pair x y)) (A.ppo E))
          (pio_llh E)) e1 e2 ->
  tc (rel_union (rel_inter (cns E X) (pair x y)) (po_iico E)) e1 e2.
Proof.
intros E X x y e1 e2 H12.
induction H12 as [e1 e2 Hu |]; [apply trc_step|].
  inversion Hu as [Hun | Hpio].
    inversion Hun as [Hp | Hppo].
      left; auto.
      right; apply A.ppo_valid; auto.
      right; destruct Hpio as [? [? ?]]; auto.
  apply trc_ind with z; auto.
Qed.

Lemma competing_irr : forall E X,
  well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  ~ (exists z, competing E X z z).
Proof.
intros E X Hwf Hv1 [z Hc].
  assert (  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ) as Hs.
    destruct_valid Hv1; split; split; auto.
  inversion Hc.
  destruct H as [Hz ?]; generalize (A.ppo_valid Hz); intro Hcy.
  apply (A2Basic.po_ac Hwf Hcy).
 (* destruct H as [z' [Hzz' Hz'z]].
  assert (po_iico E z' z) as Hpo.
    apply A2.ppo_valid; auto.
  generalize (rfs_seq_po_in_u Hs Hzz' Hpo); intro Hpio.
  assert (tc (rel_union (hb E X) (pio_llh E)) z z) as Hcy.
    apply trc_ind with z'; apply trc_step; [left | right]; auto.
    left; left; destruct Hzz'; apply mrf_in_rf; auto.
  destruct_valid Hv1; apply (Hsp z Hcy).  *)
 destruct H as [Hzz ?].
 generalize (A.ppo_valid Hzz).
 apply A2Basic.po_ac; auto.
Qed.

Lemma pair_irr :
  forall E X x y,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  ~ (exists z, (rel_inter (cns E X) (pair x y) z z)).
Proof.
intros E X x y Hwf Hv1 [z [[Hx Hy] [Hc ?]]].
destruct Hc as [? [? [? [Hdp ?]]]].
   assert (exists z, competing E X z z) as Hc.
     exists z; auto.
    apply (competing_irr E X Hwf Hv1 Hc).
Qed.
Lemma competing_not_po :
  forall E X x y,
  well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  competing E X x y -> ~ (po_iico E y x).
Proof.
intros E X x y Hwf Hv1 Hc Hyx.
  assert (  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ) as Hs.
    destruct_valid Hv1; split; split; auto.
  inversion Hc.
  destruct H as [Hz ?]; generalize (A.ppo_valid Hz); intro Hxy.
  assert (po_iico E x x) as Hcy.
    apply A2Basic.po_trans with y; auto.
  apply (A2Basic.po_ac Hwf Hcy).
(*    destruct H as [z' [Hzz' Hz'z]].
  assert (po_iico E z' x) as Hpo. *)

    destruct H as [Hxy ?].
    assert (po_iico E x y) as Hpo.
    (*apply A2nBasic.po_trans with y; auto.*)
    apply A.ppo_valid; auto.
    assert (po_iico E x x) as Hxx.
      apply A2nBasic.po_trans with y; auto.
    generalize Hxx; apply A2nBasic.po_ac; auto.
Qed.

Lemma tc_pair_po_in_pair_po :
  forall E X x y,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  rel_incl (tc (rel_seq (rel_inter (cns E X) (pair x y)) (po_iico E)))
    (rel_seq (rel_inter (cns E X) (pair x y)) (po_iico E)).
Proof.
intros E X x y Hwf Hv1 e1 e2 H12.
induction H12; auto.
  destruct IHtc1 as [z1 [H1 Hz1]];
  destruct IHtc2 as [z2 [H2 Hz2]].
  assert (po_iico E y x) as Hpo.
    destruct H1 as [? [? Hy]]; rewrite Hy in Hz1.
    destruct H2 as [? [Hx ?]]; rewrite Hx in Hz1.
  auto.
  destruct H1 as [Hc [Hx Hy]];
    rewrite Hx in Hc; rewrite Hy in Hc.
  destruct Hc as [Hc ?].
  generalize (competing_not_po E X x y Hwf Hv1 Hc); intro; contradiction.
Qed.

Lemma competing_ac_ppo2 :
  forall E X x y,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  competing E X x y ->
  (forall z, ~ tc (rel_union (rel_union (rel_inter (cns E X) (pair x y)) (A.ppo E)) (pio_llh E)) z z).
Proof.
intros E X x y Hwf Hv Hc z Hz.
generalize (u_in_pair_po E X x y z z Hz); intro Hu.
rewrite union_triv in Hu.
assert (~ (exists x, po_iico E x x)) as Hi1.
  intros [e He]; apply (A2Basic.po_ac Hwf He).
assert (~ (exists z, (rel_inter (cns E X) (pair x y)) z z)) as Hi2.
  apply pair_irr; auto.
assert (~ (exists z, (rel_union (po_iico E) (rel_inter (cns E X) (pair x y)) z z))) as Hiu.
  intros [e He]; inversion He.
    apply (A2Basic.po_ac Hwf H).
    assert (exists z, rel_inter (cns E X) (pair x y) z z) as Hco.
      exists e; auto.
    apply (pair_irr E X x y Hwf Hv Hco).
assert (trans (rel_inter (cns E X) (pair x y))) as Ht2.
  unfold trans; intros e1 e2 e3 H12 H23.
  destruct H12 as [? [? Hy]];
  destruct H23 as [[Hco ?] [Hx Hy2]].
  rewrite Hx in Hco; rewrite Hy2 in Hco.
  rewrite <- Hx in Hco; rewrite <- Hy in Hco.
  assert (exists z, competing E X z z) as Hcon.
    exists e2; auto.
  generalize (competing_irr E X Hwf Hv Hcon); intro Ht; inversion Ht.
assert (trans (po_iico E)) as Ht1.
  intros e1 e2 e3 H12 H23; apply A2Basic.po_trans with e2; auto.
generalize (union_cycle_implies_seq_cycle2 Hi1 Hi2 Hiu Ht2 Ht1 Hu);
  intros [e Htc].
generalize (tc_pair_po_in_pair_po E X x y Hwf Hv e e Htc); intro He.
destruct He as [e' [[[Hee' ?] ?] He'e]].
generalize (competing_not_po E X e e' Hwf Hv Hee'); intro; contradiction.
Qed.

Lemma convoluted_wf_implies_wf :
  convoluted_wf ->
  (forall E X x y,
  well_formed_event_structure E ->
  AResWmm.valid_execution E X ->
  competing E X x y ->
  ~ (s E X x y \/ s E X y x) ->
  (exists Y, AnWmm.valid_execution E Y /\
  competing E Y x y /\ ~ (s E Y x y \/ s E Y y x))).
Proof.
intros Hcwf E X x y Hwf Hv1 Hcxy Hns.
assert (exists so, vexec E so /\
               so_rfm E so = (so_rfm E
                 (LE (tc (rel_union (rel_union (rel_inter (cns E X) (pair x y))
                       (A.ppo E)) (pio_llh E))))) /\
               so_ws so = (so_ws
               (LE (tc (rel_union (rel_union (rel_inter (cns E X) (pair x y))
                       (A.ppo E)) (pio_llh E)))))) as Hvexec.
  exists (LE (tc (rel_union (rel_union (rel_inter (cns E X) (pair x y))
                       (A.ppo E)) (pio_llh E)))).
  split; [|split]; auto.

  assert (partial_order (tc (rel_union (rel_union (rel_inter (cns E X) (pair x y)) (A.ppo E)) (pio_llh E))) (events E)) as Hp.
    split.
      apply udr_xy_ppo2_in_events with X; auto.
      destruct_valid Hv1; split; auto.
      split.
        intros x1 x2 x3 [H12 H23]; apply trc_ind with x2; auto.
        intro e; apply competing_ac_ppo2; auto.
  assert (Included _ (events E) (events E)) as Htriv.
    unfold Included; trivial.
  generalize (OE Htriv Hp); intros [Hincl Hle].
  split; auto.
    apply lin_implies_part; auto.
    generalize (le_lso Hle); intro Heq; rewrite Heq.
    split.
      apply incl_ac with (LE
           (tc
              (rel_union (rel_union (rel_inter (cns E X) (pair x y)) (A.ppo E))
                 (pio_llh E)))).
        intros e1 e2 H12; inversion H12 as [Hppo|]; auto.
        apply Hincl; apply trc_step; left; right; auto.
    generalize (lso_is_tc Hle); intro Htc.
    intros e He; rewrite Htc in He; destruct_lin Hle;
    apply (Hac e He).

      apply incl_ac with (LE
           (tc
              (rel_union (rel_union (rel_inter (cns E X) (pair x y)) (A.ppo E))
                 (pio_llh E)))).
        intros e1 e2 H12; inversion H12 as [Hppo|]; auto.
        apply Hincl; apply trc_step; right; auto.
    generalize (lso_is_tc Hle); intro Htc.
    intros e He; rewrite Htc in He; destruct_lin Hle;
    apply (Hac e He).

generalize (ScModel.vexec_is_valid E
  (so_rfm E (LE (tc (rel_union (rel_union (rel_inter (cns E X) (pair x y))
                       (A.ppo E)) (pio_llh E)))))
  (so_ws
               (LE (tc (rel_union (rel_union (rel_inter (cns E X) (pair x y))
                       (A.ppo E)) (pio_llh E)))))
  Hwf Hvexec); intros [Y [Hv2Y [? ?]]].
  exists Y; split; auto.
    apply (Hcwf E X Y x y); auto.
Qed.

Lemma prop_stable :
  (forall E X x y,
  well_formed_event_structure E ->
  AResWmm.valid_execution E X ->
  competing E X x y ->
  ~ (s E X x y \/ s E X y x) ->
  (exists Y, AnWmm.valid_execution E Y /\
  competing E Y x y /\ ~ (s E Y x y \/ s E Y y x))).
Proof.
apply convoluted_wf_implies_wf.
apply convoluted_prop_stable.
Qed.

Lemma s_ppo_in_po :
  forall E X x y,
  well_formed_event_structure E ->
  tc (rel_union (s E X) (A2n.ppo E)) x y ->
  po_iico E x y.
Proof.
unfold s; unfold sx;
intros E X x y Hwf Hxy.
induction Hxy.
  inversion H.
    inversion H0;
      destruct H1; apply A.ppo_valid; auto.
      apply A2n.ppo_valid; auto.
    apply po_trans with z; auto.
Qed.

Lemma s_ppo2 :
  forall E X,
  well_formed_event_structure E ->
  acyclic (rel_union (s E X) (A2n.ppo E)).
Proof.
intros E X Hwf x Hx.
assert (po_iico E x x) as Hc.
  apply s_ppo_in_po with X; auto.
  apply (po_ac Hwf Hc).
Qed.

Definition covered E X r :=
  forall e1 e2, (competing E X e1 e2) -> (r E X e1 e2 \/ r E X e2 e1).
Definition covering s :=
  forall E X, well_formed_event_structure E ->
    A1Wmm.valid_execution E X ->
    covered E X s -> acyclic (A2nWmm.ghb E X).

End SN.

(*Import R.
Module BG := R.BarriersGuarantee SN.
Module AWmm := Wmm A dp.

Lemma rrmw_prop :
  (forall E X, rrmw E X) ->
  (forall E X, AnWmm.valid_execution E X -> BG.Bars.covered E X BG.Bars.s).
Proof.
intros Hrrmw E X Hv.
unfold BG.Bars.covered.
intros x y Hxy.
inversion Hxy; left; [left | right]; auto.
Qed.

Lemma rmw_guarantee :
  (forall E X, rrmw E X) ->
  (forall E X, well_formed_event_structure E ->
   (AResWmm.valid_execution E X <-> AnWmm.valid_execution E X)).
Proof.
intro Hrrmw.
apply BG.barriers_guarantee.
apply rrmw_prop; auto.
Qed.

Lemma rmw_equiv :
  (forall E X, rrmw E X) ->
  (forall E X, well_formed_event_structure E ->
   (AResWmm.valid_execution E X <-> AnWmm.valid_execution E X)).
Proof.
intros Hrrmw E X.
  apply rmw_guarantee; auto.
Qed.*)

End Rmw.
