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
Require Import Bool.
From CoqCat Require Import util.
From CoqCat Require Import wmm.
From CoqCat Require Import basic.
From CoqCat Require Import hierarchy.
From CoqCat Require Import valid.
From CoqCat Require Import covering.
From CoqCat Require Import crit_sc.
Require Import Classical_Prop.
Import OEEvt.
Set Implicit Arguments.

Module StableSC (A1 A2: Archi) (dp:Dp).
Module Wk := (* Hierarchy.*)Weaker A1 A2 dp.
Import Wk.
Module Covering := Covering A1b A2 dp.
Import Covering.
Module Crit := CritSC A1b A2 dp.
Import Crit.
Module VA1 := Valid A1b dp.
Import VA1.
Module A1Basic := Basic A1b dp.

Module Preservation := Preservation Cm.
Import Preservation.

(*A2n=SC*)
Hypothesis rfe2_glob : forall E X,
  rel_incl (rf_inter X) (A2nWmm.mhb E X).
Hypothesis ppo2_po : forall E, A2.ppo E = po_iico E.
Hypothesis rfi2_ppo2 : forall E X,
  rel_incl (rf_intra X) (A2.ppo E).

Lemma v1_and_no_cy_implies_covered :
  forall E X,
  well_formed_event_structure E ->
  A1bWmm.valid_execution E X ->
  ~ (exists cy : Rln Event, crit_cy E cy) ->
  Cm.covered E X Cm.s.
Proof.
intros E X Hwf Hv1 Hncy e1 e2 [Hc12 [sigma [Hsigma ?]]].
assert (exists cy : Rln Event, crit_cy E cy) as Hc.
  exists sigma; auto.
contradiction.
Qed.

Lemma write_or_read :
  forall E x,
  events E x ->
  writes E x \/ reads E x.
Proof.
intros E x Hex.
case_eq (action x); intros d l v Hax;
case_eq d; intro Hd; [right | left];
  split; auto; exists l; exists v; subst; auto.
Qed.

Lemma tc_dom_in_evts :
  forall E cy e1 e2,
  well_formed_event_structure E ->
  tc (rel_union (rel_inter cy (conflict E)) (rel_union (A1b.ppo E) (pio_llh E))) e1 e2 ->
  In _ (events E) e1.
Proof.
intros E cy e1 e2 Hwf Htc.
induction Htc as [e1 e2 Hu |]; auto.
  inversion Hu as [Hcy | Hpo].
    destruct Hcy as [? [? [? ?]]]; auto.
    apply A1Basic.po_iico_domain_in_events with e2; auto.
      inversion Hpo as [Hppo | Hpio].
      apply A1b.ppo_valid; auto.
      destruct Hpio as [? [? ?]]; auto.
Qed.

Lemma tc_ran_in_evts :
  forall E cy e1 e2,
  well_formed_event_structure E ->
  tc (rel_union (rel_inter cy (conflict E)) (rel_union (A1b.ppo E) (pio_llh E))) e1 e2 ->
  In _ (events E) e2.
Proof.
intros E cy e1 e2 Hwf Htc.
induction Htc as [e1 e2 Hu |]; auto.
  inversion Hu as [Hcy | Hpo].
    destruct Hcy as [? [? [? ?]]]; auto.
    apply A1Basic.po_iico_range_in_events with e1; auto.
      inversion Hpo as [Hppo | Hpio].
      apply A1b.ppo_valid; auto.
      destruct Hpio as [? [? ?]]; auto.
Qed.

Lemma cy_inter_conflict_ppo1_partial_order :
  forall E cy,
  well_formed_event_structure E ->
  acyclic (rel_union (rel_inter cy (conflict E)) (rel_union (A1b.ppo E) (pio_llh E))) ->
  partial_order (tc (rel_union (rel_inter cy (conflict E)) (rel_union (A1b.ppo E) (pio_llh E))))
  (events E).
Proof.
intros E cy Hwf Hac.
  split; [|split].

    intros e1 Hu; inversion Hu as [e Hd | e Hr].
    destruct Hd as [e2 H12].
      apply tc_dom_in_evts with cy e2; auto.

    destruct Hr as [e2 H12].
      apply tc_ran_in_evts with cy e2; auto.

    intros x1 x2 x3 [H12 H23]; apply trc_ind with x2; auto.

    intros e He; apply (Hac e He).
Qed.

Lemma ppo1_in_le :
  forall E cy,
  well_formed_event_structure E ->
  acyclic (rel_union (rel_inter cy (conflict E)) (rel_union (A1b.ppo E) (pio_llh E))) ->
  rel_incl (A1b.ppo E) (LE (tc (rel_union (rel_inter cy (conflict E)) (rel_union (A1b.ppo E) (pio_llh E))))).
Proof.
intros E cy Hwf Hacy;
generalize (cy_inter_conflict_ppo1_partial_order Hwf Hacy);
intro Hpart.
    assert (Included _ (events E) (events E)) as Htriv.
    intros e He; auto.
    generalize (OE Htriv Hpart); intros [Hinc Hle].
intros x y Hxy.
apply Hinc; apply trc_step; right; left; auto.
Qed.

Lemma pio_in_le :
  forall E cy,
  well_formed_event_structure E ->
  acyclic (rel_union (rel_inter cy (conflict E)) (rel_union (A1b.ppo E) (pio_llh E))) ->
  rel_incl (pio_llh E) (LE (tc (rel_union (rel_inter cy (conflict E)) (rel_union (A1b.ppo E) (pio_llh E))))).
Proof.
intros E cy Hwf Hacy;
generalize (cy_inter_conflict_ppo1_partial_order Hwf Hacy);
intro Hpart.
    assert (Included _ (events E) (events E)) as Htriv.
    intros e He; auto.
    generalize (OE Htriv Hpart); intros [Hinc Hle].
intros x y Hxy.
apply Hinc; apply trc_step; right; right; auto.
Qed.

Lemma le_ac :
  forall E cy,
  linear_strict_order
        (LE (tc (rel_union (rel_inter cy (conflict E)) (rel_union (A1b.ppo E) (pio_llh E)))))
        (events E) ->
  acyclic (LE (tc (rel_union (rel_inter cy (conflict E)) (rel_union (A1b.ppo E) (pio_llh E))))).
Proof.
intros E cy Hle x Hx; generalize Hle; intro Hlin;
destruct_lin Hle; apply (Hac x).
rewrite (lso_is_tc Hlin) in Hx; auto.
Qed.

Lemma cy_inter_conflict_ppo1_vexec :
  forall E cy,
  well_formed_event_structure E ->
  acyclic (rel_union (rel_inter cy (conflict E)) (rel_union (A1b.ppo E) (pio_llh E))) ->
  vexec E (tc (rel_union (rel_inter cy (conflict E)) (rel_union (A1b.ppo E) (pio_llh E)))).
Proof.
intros E cy Hwf Hacy;
generalize (cy_inter_conflict_ppo1_partial_order Hwf Hacy);
intro Hpart.
    assert (Included _ (events E) (events E)) as Htriv.
    intros e He; auto.
    generalize (OE Htriv Hpart); intros [Hinc Hle].
split; [|split]; auto.

  apply ac_incl with (LE (tc (rel_union (rel_inter cy (conflict E)) (rel_union (A1b.ppo E) (pio_llh E))))); auto.
    apply le_ac; auto.
    intros x y Hxy; inversion Hxy; auto.
    apply ppo1_in_le; auto.

  apply ac_incl with (LE (tc (rel_union (rel_inter cy (conflict E)) (rel_union (A1b.ppo E) (pio_llh E))))); auto.
    apply le_ac; auto.
    intros x y Hxy; inversion Hxy; auto.
    apply pio_in_le; auto.
Qed.

Lemma cy_is_or :
  forall E Y cy,
  well_formed_event_structure E ->
  A1bWmm.valid_execution E Y ->
  acyclic (rel_union (rel_inter cy (conflict E)) (rel_union (A1b.ppo E) (pio_llh E))) ->
  rel_incl cy (tc (rel_union (rel_inter cy (conflict E)) (A2n.ppo E))) ->
  (rf Y =
      so_rfm E (tc (rel_union (rel_inter cy (conflict E)) (rel_union (A1b.ppo E) (pio_llh E))))) ->
  (ws Y = so_ws (tc (rel_union (rel_inter cy (conflict E)) (rel_union (A1b.ppo E) (pio_llh E))))) ->
  rel_incl cy (tc (rel_union ((mhbd E Y)) (A2n.ppo E))).
Proof.
intros E Y cy Hwf Hv Hacy Hi Hrf Hws x y Hxy.
generalize (cy_inter_conflict_ppo1_partial_order Hwf Hacy);
intro Hpart.
    assert (Included _ (events E) (events E)) as Htriv.
    intros e He; auto.
    generalize (OE Htriv Hpart); intros [Hinc Hle].

generalize (Hi x y Hxy); intro Htc.
clear Hxy.
induction Htc as [x y Hu |]; auto.
  inversion Hu as [Hc | Hppo].
  destruct Hc as [Hxy Hc].
  generalize Hc; intros [Hex [Hey [? [? Hw]]]].
  inversion Hw as [Hwx | Hwy].

    generalize (write_or_read E y Hey); intro Hory.
    inversion Hory as [Hwy | Hry].

    (*Wx Wy*)
      apply trc_step; left;
      split; auto.
       (*split; auto.*)
       apply A2nBasic.ws_in_mhb.
        rewrite Hws; split.
          apply Hinc; apply trc_step; left; split; auto.
          exists (loc x); split; split.
            left; exists y.
              apply Hinc; apply trc_step; left; split; auto.
              destruct Hwx as [? [lx [vx Hax]]]; unfold write_to; rewrite Hax.
              exists vx; unfold loc; rewrite Hax; auto.
            right; exists x.
              apply Hinc; apply trc_step; left; split; auto.
              destruct Hwy as [? [ly [vy Hay]]]; unfold write_to; rewrite Hay.
              exists vy; rewrite H; unfold loc; rewrite Hay; auto.

     (*Wx Ry -> (ws)?;rf*)
     destruct_valid Hv.
     generalize (Hrf_init y Hry); intros [wy [Hwy ?]].
     generalize (eqEv_dec x wy); intros [Heq | Hneq].
     apply trc_step; left; split; auto.
     (*split; auto.*) apply rfe2_glob; split; auto.
       subst; auto.

       apply trc_ind with wy.
     assert (ws Y x wy \/ ws Y wy x) as Horxwy.
       generalize (Hws_tot (loc x)); intro Hl.
       destruct_lin Hl.
         assert (In Event (writes_to_same_loc_l (events E) (loc x)) x) as Hx.
           split; auto.
             destruct Hwx as [? [? [vx Hwx]]]; unfold write_to;
             rewrite Hwx; unfold loc; exists vx; rewrite Hwx; auto.
         assert (In Event (writes_to_same_loc_l (events E) (loc x)) wy) as Hwwy.
           split.
             apply A1Basic.dom_rf_in_events with Y y; auto.
               split; auto.
             rewrite H.
               rewrite <- A1Basic.rf_implies_same_loc2 with E Y wy y.
             generalize (A1Basic.dom_rf_is_write E Y wy y Hrf_cands H1);
             intros [? [vy Hwwy]]; unfold write_to;
             rewrite Hwwy; unfold loc; exists vy; rewrite Hwwy; auto.
       split; split; auto. auto.
       generalize (Htot x wy Hneq Hx Hwwy); intro Hor;
       inversion Hor as [Hxwy | Hwyx]; [left | right].
         destruct Hxwy; auto. destruct Hwyx; auto.

     inversion Horxwy as [Hxwy | Hwyx].
     destruct (eqProc_dec (proc_of x) (proc_of wy)) as [Heqp | Hneqp].
       apply trc_step; right; rewrite ppo2_po.
       assert (In _ (events E) wy) as Hewy.
         apply A2nBasic.ran_ws_in_events with Y x; auto.
         split; auto.
       generalize (A2nBasic.same_proc_implies_po x wy Hwf Heqp Hex Hewy);
       intro Hor; inversion Hor; auto.
       assert (tc (rel_union (hb E Y) (pio_llh E)) x x) as Hcuni.
         apply trc_ind with wy; apply trc_step.
           left; right; auto.
           right; split; [|split]; auto.
           apply sym_eq.
           apply A1bBasic.ws_implies_same_loc with E Y; auto.
             split; split; auto.
           intros [Hrwy [? [lx [vx Hax]]]].
           destruct Hwx as [? [? [? Hwx]]].
           rewrite Hax in Hwx; inversion Hwx.
           unfold acyclic in Hsp; generalize (Hsp x); intro; contradiction.

       apply trc_step; left; split; auto.
         apply A2nBasic.ws_in_mhb; auto.

       rewrite Hrf in H1; destruct H1 as [? [? Hmax]].
       assert (In Event
         (previous_writes E
            (LE (tc (rel_union (rel_inter cy (conflict E)) (rel_union (A1b.ppo E) (pio_llh E))))) y)
         x) as Hpwx.
         split; auto.
         split; auto.
         apply Hinc; apply trc_step; inversion Hu as [|Hppo2]; [left | right]; auto.
         generalize (A2.ppo_valid Hppo2); intro Hpo.
         generalize (A2nBasic.po_implies_same_proc Hwf Hex Hey Hpo); intro; contradiction.

       assert (LE (tc (rel_union (rel_inter cy (conflict E)) (rel_union (A1b.ppo E) (pio_llh E)))) wy x) as Hle_wyx.
         rewrite Hws in Hwyx.
         destruct Hwyx; auto.

       assert (In Event
         (previous_writes E
            (LE (tc (rel_union (rel_inter cy (conflict E)) (rel_union (A1b.ppo E) (pio_llh E))))) y)
         x /\
       LE (tc (rel_union (rel_inter cy (conflict E)) (rel_union (A1b.ppo E) (pio_llh E)))) wy x) as Hand.
         split; auto.

      generalize (Hmax x Hand); intro Heqwyx.
      assert (x = wy) as Heq'.
        auto.
      contradiction.

     destruct (eqProc_dec (proc_of wy) (proc_of y)) as [Heqp | Hneqp].
       apply trc_step; right.
       assert (rf_intra Y wy y) as Hrfi.
         split; auto.
       apply (rfi2_ppo2 E Hrfi).

       apply trc_step; left; split; auto.
       apply rfe2_glob; auto. split; auto.

    generalize (write_or_read E x Hex); intro Horx.
    inversion Horx as [Hwx | Hrx];
      apply trc_step; left; split; auto.

    (*Wx Wy*)
       (*split; auto.*)
       apply A2nBasic.ws_in_mhb.
        rewrite Hws; split.
          apply Hinc; apply trc_step; left; split; auto.
          exists (loc x); split; split.
            left; exists y.
              apply Hinc; apply trc_step; left; split; auto.
              destruct Hwx as [? [lx [vx Hax]]]; unfold write_to; rewrite Hax.
              unfold loc; exists vx; rewrite Hax; auto.
            right; exists x.
              apply Hinc; apply trc_step; left; split; auto.
              destruct Hwy as [? [ly [vy Hay]]]; unfold write_to; exists vy; rewrite Hay.
              rewrite H; unfold loc; rewrite Hay; auto.

   (*Rx Wy*)
      (*split; auto.*)
      apply A2nBasic.fr_in_mhb.
        generalize Hrx; intros [Heex Hrrx]; destruct Hwy as [Heey Hwy];
        split; [|split]; auto.
        destruct_valid Hv.
          generalize (Hrf_init x Hrx); intros [wx [Hewx Hwx]];
          exists wx; split; auto.
          rewrite Hws; split.
          destruct_lin Hle.
          apply Htrans with x; split.
            rewrite Hrf in Hwx; destruct Hwx as [? Hmax].
            destruct Hmax as [[? [? ?]] ?]; auto.
            apply Hinc; apply trc_step; left; split; auto.

            exists (loc x); split; split.
              left; exists x.
                rewrite Hrf in Hwx; destruct Hwx as [Hrfx Hmax].
                destruct Hmax as [Hpw ?].
                destruct Hpw as [? [? ?]]; auto.
                generalize (Hrf_cands wx x Hwx);
                intros [? [? [lx [Hwwx [[vx Hrrrx] ?]]]]].
                unfold loc; rewrite Hrrrx; auto.

              right; exists x.
                apply Hinc; apply trc_step; left; split; auto.
              destruct Hwy as [ly [vy Hay]]; unfold write_to; rewrite Hay.
              rewrite H; unfold loc; exists vy; rewrite Hay; auto.

  (*x ppo2 y*)
  apply trc_step; right; auto.

  apply trc_ind with z; auto.
Qed.

Lemma mv_implies_mvor :
  forall E X cy,
  well_formed_event_structure E ->
  A1bWmm.valid_execution E X ->
  crit_cy E cy ->
  (exists Y, A1bWmm.valid_execution E Y /\
     exists cy', crit_cy_or E Y cy').
Proof.
intros E X cy Hwf Hv1 Hcy.
destruct Hcy as [Hmcy [Hnac [Hi Hac1]]].

assert (exists so, vexec E so /\
    so_rfm E so = so_rfm E (tc (rel_union (rel_inter cy (conflict E)) (rel_union (A1b.ppo E) (pio_llh E))))  /\
    so_ws so = so_ws (tc (rel_union (rel_inter cy (conflict E)) (rel_union (A1b.ppo E) (pio_llh E))))) as Heex.
  exists (tc (rel_union (rel_inter cy (conflict E)) (rel_union (A1b.ppo E) (pio_llh E)))); split; [|split]; auto.
  apply cy_inter_conflict_ppo1_vexec; auto.

generalize (VA1.ScModel.vexec_is_valid E
  (so_rfm E (tc (rel_union (rel_inter cy (conflict E)) (rel_union (A1b.ppo E) (pio_llh E)))))
  (so_ws (tc ((rel_union (rel_inter cy (conflict E)) (rel_union (A1b.ppo E) (pio_llh E)))))) Hwf Heex);
intros [Y [HvY [Hrf Hws]]]; exists Y; split; auto.

exists cy; split; [|split]; auto.
  apply cy_is_or; auto.
  unfold sigma_wf in Hmcy; rewrite union_triv in Hmcy; auto.
Qed.

Lemma cy_or_in_ghb2 :
  forall E X cy,
  well_formed_event_structure E ->
  crit_cy_or E X cy ->
  rel_incl cy (tc (A2nWmm.ghb E X)).
Proof.
intros E X cy Hwf [Hmcy [? [? ?]]] x y Hxy.
rewrite ghb2_is_mhb_ppo2.
generalize (Hmcy x y Hxy); intro Htc.
generalize Htc; apply tc_incl.
intros e1 e2 Hor.
inversion Hor as [Hmhbd | Hppo2].
  destruct Hmhbd as [Hmhb ?].
    left; auto.
  right; auto.
Qed.

Set Implicit Arguments.
Lemma tc_tc :
  forall A (r: Rln A) x y,
  tc (tc r) x y ->
  tc r x y.
Proof.
intros A r x y Hxy.
induction Hxy; auto.
apply trc_ind with z; auto.
Qed.

Lemma ac_implies_tc_ac :
  forall A (r:Rln A),
  acyclic r ->
  acyclic (tc r).
Proof.
intros A r Hac x Hx.
generalize (tc_tc Hx); intro Htc.
apply (Hac x Htc); auto.
Qed.
Unset Implicit Arguments.

Lemma stability_to_SC :
  forall E, well_formed_event_structure E ->
               (exists X, A1bWmm.valid_execution E X) ->
  ((forall X, (A1bWmm.valid_execution E X -> A2nWmm.valid_execution E X)) <->
  (~(exists cy, crit_cy E cy))).
Proof.
intros E Hwf [X Hv1]; split.
  intros Hp [cy Hcy].
  generalize (mv_implies_mvor Hwf Hv1 Hcy);
    intros [Y [Hv1Y [cy' Hcy']]].
  generalize (Hp Y Hv1Y); intro Hv2.
  generalize (cy_or_in_ghb2 Hwf Hcy'); intro Hincl.
  destruct_valid Hv2.
  assert (acyclic (tc (A2nWmm.ghb E Y))) as Hac.
    apply ac_implies_tc_ac; auto.
  generalize (incl_ac Hincl Hac); intro Haccy.
  destruct Hcy' as [? [? [Hnac ?]]].
  contradiction.

  intros Hncy Y Hv1Y.
      generalize (v1_and_no_cy_implies_covered Hwf Hv1Y Hncy); intro Hc.
      apply prop_implies_v2; auto.
Qed.

End StableSC.
