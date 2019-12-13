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
Require Import Classical_Prop.
From CoqCat Require Import drf.
From CoqCat Require Import racy.
Import OEEvt.
Set Implicit Arguments.

Module CritSC (A1 A2: Archi) (dp:Dp).

Module Wk := (*Hierarchy.*)Weaker A1 A2 dp.
Import Wk.
Hypothesis wk : weaker.

Module VA2 := Valid A2n dp.
Import VA2. Import VA2.ScAx.
Module Covering := Covering A1 A2n dp.
Import Covering.

Set Implicit Arguments.

Definition rel_inter A (r1 r2 : Rln A) :=
  fun x => fun y => r1 x y /\ r2 x y.

Definition cycle_sym A (sigma : Rln A) :=
  forall x y, udr sigma x -> udr sigma y ->
  sigma x y -> sigma y x.
Definition cycle_trans_tot A (sigma : Rln A) :=
  forall x y, udr sigma x -> udr sigma y ->
    tc (sigma) x y.
Definition non_empty A (sigma : Rln A) :=
  (exists x, exists y, sigma x y).
Definition cycle A (sigma : Rln A) :=
  cycle_sym sigma /\
  cycle_trans_tot sigma /\ non_empty sigma.
Ltac destruct_cycle H :=
  destruct H as [Hsym [Htot Hnemp]].
Lemma cycle_implies_nac :
  forall A (sigma:Rln A),
  cycle sigma -> ~(acyclic sigma).
Proof.
unfold acyclic;
intros A sigma Hcy Hn.
destruct_cycle Hcy.
destruct Hnemp as [x [y Hxy]].
unfold cycle_sym in Hsym.
assert (udr sigma x) as Hudrx.
  left; exists y; auto.
assert (udr sigma y) as Hudry.
  right; exists x; auto.
generalize (Hsym x y Hudrx Hudry Hxy); intro Hyx.
assert (tc (sigma) x x) as Hc.
  apply trc_ind with y; apply trc_step; auto.
generalize (Hn x); intro; contradiction.
Qed.

Definition conflict E :=
  fun e1 => fun e2 => events E e1 /\ events E e2 /\
    loc e1 = loc e2 /\ proc_of e1 <> proc_of e2 /\ (writes E e1 \/ writes E e2).

Definition sigma_wf E sigma :=
  rel_incl sigma (tc (rel_union (A2n.ppo E) (rel_inter sigma (conflict E)))).

Definition crit_cy E sigma :=
  sigma_wf E sigma /\ ~ acyclic sigma /\
  acyclic (rel_union (rel_inter sigma (conflict E)) (rel_union (A1.ppo E) (pio_llh E))) /\
  (forall x y, sigma x y -> A2n.ppo E x y ->
  ~(exists z, (z <> y /\ sigma x z /\ A2n.ppo E x z /\ A2n.ppo E z y)) /\ loc x <> loc y) /\
  (forall x y, sigma x y -> conflict E x y ->
    (((reads E x /\ writes E y) \/
      (writes E x /\ reads E y) \/
      (writes E x /\ writes E y)) /\
      ~(exists z, conflict E z x /\ tc sigma x z /\ tc sigma z y)) \/
      (reads E x /\ reads E y /\ exists e, writes E e /\ tc sigma x e /\ tc sigma e y /\
       ~(exists z, conflict E z x /\ tc sigma x z /\ tc sigma z y))).

Definition mhbd E X :=
  fun x => fun y => (A2nWmm.mhb E X x y) /\ proc_of x <> proc_of y.

Ltac destruct_valid H :=
  destruct H as [[Hws_tot Hws_cands] [[Hrf_init [Hrf_cands Hrf_uni]] [Hsp [Hth Hvalid]]]];
  unfold write_serialization_well_formed in Hws_tot.

Definition sigma_wf_or E X sigma :=
  rel_incl sigma (tc (rel_union (mhbd E X) (A2.ppo E))).

Definition crit_cy_or E X sigma :=
  sigma_wf_or E X sigma /\
  crit_cy E sigma.
Axiom exists_crit_cy_or : forall E X x,
  tc (A2nWmm.ghb E X) x x ->
  exists sigma, crit_cy_or E X sigma.

Module C <: Compete.
Parameter competing : Event_struct -> Execution_witness -> Rln Event.
Hypothesis compete_in_events :
  forall E X x y,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  competing E X x y ->
  events E x /\ events E y.
Parameter s : Event_struct -> Execution_witness -> Rln Event.
Definition covered E X r :=
  forall e1 e2, (competing E X e1 e2) -> (r E X e1 e2 \/ r E X e2 e1).
Definition covering s :=
  forall E X, well_formed_event_structure E ->
    A1Wmm.valid_execution E X ->
    covered E X s -> acyclic (A2nWmm.ghb E X).

Definition cns E X :=
  fun e1 => fun e2 => competing E X e1 e2 /\ ~ (s E X e1 e2 \/ s E X e2 e1).
Hypothesis competing_irr : forall E X,
  well_formed_event_structure E ->
    A1Wmm.valid_execution E X ->
  ~ (exists z, competing E X z z).
Hypothesis competing_not_po :
  forall E X x y, well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  competing E X x y -> ~ (po_iico E y x).
Hypothesis covering_s : covering s.
Hypothesis wf :
  forall E X x y,
  well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  competing E X x y ->
  ~ (s E X x y \/ s E X y x) ->
  (exists Y, A2nWmm.valid_execution E Y /\
  competing E Y x y /\ ~ (s E Y x y \/ s E Y y x)).
End C.

Module Cm <: Compete.
Definition competing E X :=
  fun e1 e2 => C.competing E X e1 e2 /\
    (exists sigma, crit_cy E sigma /\ sigma e1 e2).
Lemma compete_in_events :
  forall E X x y,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  competing E X x y ->
  events E x /\ events E y.
Proof.
intros E X x y Hwf Hrfwf [Hc ?].
apply C.compete_in_events with X; auto.
Qed.

Definition s E X :=
  fun e1 e2 => C.s E X e1 e2.
Definition covered E X r :=
  forall e1 e2, (competing E X e1 e2) -> (r E X e1 e2 \/ r E X e2 e1).
Definition covering s :=
  forall E X, well_formed_event_structure E ->
    A1Wmm.valid_execution E X ->
    covered E X s -> acyclic (A2nWmm.ghb E X).

Definition cns E X :=
  fun e1 => fun e2 => competing E X e1 e2 /\ ~ (s E X e1 e2 \/ s E X e2 e1).
Lemma competing_irr : forall E X,
  well_formed_event_structure E ->
    A1Wmm.valid_execution E X ->
  ~ (exists z, competing E X z z).
Proof.
intros E X Hwf Hv1 [z [Hz ?]].
assert (exists z, C.competing E X z z) as Hc.
  exists z; auto.
apply (C.competing_irr Hwf Hv1 Hc).
Qed.
Lemma competing_not_po :
  forall E X x y, well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  competing E X x y -> ~ (po_iico E y x).
Proof.
intros E X x y Hwf Hv1 [Hc ?].
apply (C.competing_not_po Hwf Hv1 Hc).
Qed.

Lemma mhbd_in_conflict :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  rel_incl (mhbd E X) (conflict E).
Proof.
intros E X Hwf Hs x y [? ?].
generalize (A2nBasic.mhb_in_com E X x y H); intro Hhb.
split; [|split; [|split; [|split]]]; auto.
  change (events E x) with (In _ (events E) x); apply A2nBasic.hb_dom_in_evts with X y; auto.
  change (events E y) with (In _ (events E) y); apply A2nBasic.hb_ran_in_evts with X x; auto.
  apply A2nBasic.com_implies_same_loc with E X; auto.
  apply A2nBasic.com_implies_writes with X; auto.
Qed.

Set Implicit Arguments.
Lemma nac_incl :
  forall A (d s s' : Rln A),
  rel_incl s' s ->
  ~ acyclic (rel_union d s') ->
  ~ acyclic (rel_union d s).
Proof.
unfold not; unfold acyclic;
intros A d s1 s1' Hi Hnac Hc.
apply Hnac; intros x Hx.
assert (tc (rel_union d s1) x x) as Hin.
  generalize Hx; apply tc_incl; intros e1 e2 H12.
  inversion H12; [left | right; apply Hi]; auto.
  generalize (Hc x); intro; contradiction.
Qed.
Lemma nac_incl2 :
  forall A (s s' : Rln A),
  rel_incl s' s ->
  ~ acyclic s' ->
  ~ acyclic s.
Proof.
unfold not; unfold acyclic;
intros A s1 s1' Hi Hnac Hc.
apply Hnac; intros x Hx.
assert (tc s1 x x) as Hin.
  generalize Hx; apply tc_incl; intros e1 e2 H12.
  apply Hi; auto.
  generalize (Hc x); intro; contradiction.
Qed.
Lemma not_forall_exists_tc :
  forall A (s : Rln A), ~(forall x, ~ tc s x x) ->
  exists x, tc s x x.
Proof.
intros A s1 Hn.
generalize (excluded_middle (exists x, tc s1 x x)); intro Hor;
  inversion Hor; auto.
assert (forall x, ~ tc s1 x x) as Hc.
  intro x.
  generalize (excluded_middle (tc s1 x x)); intro Hor2;
  inversion Hor2; auto.
  assert (exists x, tc s1 x x) as Hc.
    exists x; auto.
  contradiction.
contradiction.
Qed.
Unset Implicit Arguments.

Hypothesis covering_s :
  forall E X, well_formed_event_structure E ->
    A1Wmm.valid_execution E X ->
    covered E X s -> acyclic (A2nWmm.ghb E X).

Lemma wf :
  forall E X x y,
  well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  competing E X x y ->
  ~ (s E X x y \/ s E X y x) ->
  (exists Y, A2nWmm.valid_execution E Y /\
  competing E Y x y /\ ~ (s E Y x y \/ s E Y y x)).
Proof.
intros E X x y Hwf Hv1 [Hc [cy [Hmcy Hcy]]] Hns.
unfold s in Hns.
generalize (C.wf Hwf Hv1 Hc Hns);
  intros [Y [Hv2 [HcY HnsY]]].
exists Y; split; [|split]; auto.
split; auto.
exists cy; split; auto.
Qed.

Module DrfG := DataRaceFree A1 A2 dp.

Module DrfMin (HB : DrfG.HappensBefore).

Module Drf := DrfG.Drf0 (HB).

Hypothesis s_com :
  forall E X x y,
  s E X x y -> ~(com E X y x).
Hypothesis s_po :
  forall E X,
  acyclic (rel_union (s E X) (po_iico E)).

Lemma tc_mhbd_ppo2_in_s_ppo2 :
  forall E X x y,
  well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  Drf.covered E X s ->
  tc (rel_union (mhbd E X) (A2.ppo E)) x y ->
  tc (rel_union (s E X) (A2.ppo E)) x y.
Proof.
intros E X e1 e2 Hwf Hv1 Hcov; apply tc_incl.
intros x y Hxy.
      assert ( write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X)) as Hs.
        split; split; destruct_valid Hv1; auto.

inversion Hxy as [Hc | Hppo2]; [left | right]; auto.

assert (Drf.competing E X x y) as Hcomp.

  destruct Hc as [Hmhbdxy ?]; split; [|split; [|split; [|split]]]; auto.

      assert (mhbd E X x y) as Hmhbd.
        split; auto.
      generalize (mhbd_in_conflict Hwf Hs Hmhbd); intro Hcxy.
      destruct Hcxy; auto.

      assert (mhbd E X x y) as Hmhbd.
        split; auto.
      generalize (mhbd_in_conflict Hwf Hs Hmhbd); intro Hcxy.
      destruct Hcxy as [? [? ?]]; auto.

      assert (mhbd E X x y) as Hmhbd.
        split; auto.
      generalize (mhbd_in_conflict Hwf Hs Hmhbd); intro Hcxy.
      destruct Hcxy as [? [? [? ?]]]; auto.

      assert (mhbd E X x y) as Hmhbd.
        split; auto.
      generalize (mhbd_in_conflict Hwf Hs Hmhbd); intro Hcxy.
      destruct Hcxy as [? [? [? [? ?]]]]; auto.

    destruct Hs as [? [? [? ?]]]; auto.

generalize (Hcov x y Hcomp); intro Hor; inversion Hor; auto.

inversion Hxy as [Hmhbd | Hppo].
  destruct Hmhbd as [Hmhbdxy ?].
  assert (com E X x y) as Hhb.
    apply A2nBasic.mhb_in_com; auto.
  generalize (s_com E X y x H3); intro; contradiction.

  assert (exists x, tc (rel_union (s E X) (po_iico E)) x x) as Hcy.
    exists x; apply trc_ind with y; apply trc_step;
      [right | left]; auto.
    apply A2.ppo_valid; auto.
  destruct Hcy as [e Hcy].
  generalize (s_po E X); intro Hac.
  generalize (Hac e Hcy); intro Ht; inversion Ht.
Qed.

Lemma tc_cy_in_tc :
  forall E X cy,
  rel_incl cy (tc (rel_union (s E X) (A2.ppo E))) ->
  rel_incl (tc cy) (tc (rel_union (s E X) (A2.ppo E))).
Proof.
intros E X cy Hi x y Hxy.
induction Hxy.
  apply Hi; auto.
  apply trc_ind with z; auto.
Qed.

Lemma min_covered_implies_no_min_cy :
  forall E X, well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  Drf.covered E X s ->
  ~(exists cy, crit_cy_or E X cy).
Proof.
intros E X Hwf Hv1 Hc [cy [Hicy [? [Hnac ?]]]].
assert (rel_incl cy (tc (rel_union (s E X) (A2.ppo E)))) as Hi.
  intros x y Hxy; generalize (Hicy x y Hxy); intro Htc.
    apply tc_mhbd_ppo2_in_s_ppo2; auto.
assert (~(acyclic (rel_union (s E X) (po_iico E)))) as Hco.
  apply nac_incl2 with (rel_union (s E X) (A2.ppo E)).
    intros e1 e2 H12; inversion H12; [left | right]; auto.
    apply A2.ppo_valid; auto.
  unfold acyclic; intros Hex.
  generalize (not_forall_exists_tc Hnac); intros [e He].
  assert (rel_incl (tc cy) (tc (rel_union (s E X) (A2.ppo E)))) as Hitc.
    apply tc_cy_in_tc; auto.
  generalize (Hitc e e He); intro Hxx.
  generalize (Hex e); intro; contradiction.
generalize (s_po E X); intro; contradiction.
Qed.

Lemma covering_s :
  forall E X, well_formed_event_structure E ->
    A1Wmm.valid_execution E X ->
    Drf.covered E X s -> acyclic (A2nWmm.ghb E X).
Proof.
intros E X Hwf Hv1 Hc z Hz.
generalize (exists_crit_cy_or E X Hz);
intros [cy Hcy].
assert (exists cy, crit_cy_or E X cy) as Hex.
  exists cy; auto.
generalize (min_covered_implies_no_min_cy E X Hwf Hv1 Hc); intro Hnex.
contradiction.
Qed.

End DrfMin.

Module Racy := Racy A1 A2 dp.
Module RacyMin (SN:Racy.SafetyNet).

Module R := Racy.Barriers (SN).

Definition AC X s :=
  forall (x z y:Event), rf_sub X x z /\ s z y -> s x y.
Hypothesis s_ghb :
  forall E X,
  well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  acyclic (rel_union (s E X) (A1bWmm.ghb E X)).
Hypothesis s_ppo2 :
  forall E X,
  well_formed_event_structure E ->
  acyclic (rel_union (s E X) (A2n.ppo E)).
Hypothesis s_ac : forall E X, AC X (s E X).

Lemma tc_cy_in_tc :
  forall E X cy,
  rel_incl cy (tc (rel_union (mhbd E X) (A2.ppo E))) ->
  rel_incl (tc cy) (tc (rel_union (mhbd E X) (A2.ppo E))).
Proof.
intros E X cy Hi x y Hxy.
induction Hxy; auto.
apply trc_ind with z; auto.
Qed.

Lemma tc_mhbd_ppo2_in_mhb_ppo2 :
  forall E X x y,
  tc (rel_union (mhbd E X) (A2.ppo E)) x y ->
  tc (rel_union (A2nBasic.AWmm.mhb E X) (A2n.ppo E)) x y.
Proof.
intros E X x y Hxy; induction Hxy as [x y Hu |].
  apply trc_step; inversion Hu as [Hmhbd | Hppo]; [left | right]; auto.
    destruct Hmhbd; auto.
  apply trc_ind with z; auto.
Qed.

Lemma ppo2_in_ghb1 :
  forall E X x y,
  well_formed_event_structure E ->
  R.covered E X s ->
  A2n.ppo E x y ->
  rel_union (A1bWmm.ghb E X) (s E X) x y.
Proof.
intros E X x y Hwf Hfb Hxy.
  generalize (excluded_middle (A1b.ppo E x y)); intro Hor.
  inversion Hor as [Hppo1 | Hnppo1].
   left; apply A1bBasic.ppo_in_ghb; auto.
   assert (ppo_sub E x y) as Hppos.
     split; auto.

   assert (R.competing E X x y) as Hc.
    left; auto.
   right; generalize (Hfb x y Hc); intro Hors; auto.
   inversion Hors as [|Hsyx]; auto.
     assert (tc (rel_union (s E X) (A2n.ppo E)) y y) as Hcy.
       apply trc_ind with x; apply trc_step; [left | right]; auto.
     generalize (s_ppo2 E X Hwf); unfold acyclic; intro Hac;
     generalize (Hac y Hcy); intro Ht; inversion Ht.
Qed.

Lemma rf_sub_seq_ppo2_in_ab1 :
  forall E X x z y,
  well_formed_event_structure E ->
  R.covered E X s ->
  rf_sub X x z ->
  A2n.ppo E z y ->
  s E X x y.
Proof.
intros E X x z y Hwf Hfb Hxz Hzy.
   assert (R.competing E X z y) as Hc.
     right; split; auto.
     exists x; auto.
generalize (Hfb z y Hc); intro Hor.
inversion Hor.
assert (rf_sub X x z /\ s E X z y) as Hand.
  split; auto.

apply (s_ac E X x z y Hand).
     assert (tc (rel_union (s E X) (A2n.ppo E)) y y) as Hcy.
       apply trc_ind with z; apply trc_step; [left | right]; auto.
     generalize (s_ppo2 E X Hwf); unfold acyclic; intro Hac;
     generalize (Hac y Hcy); intro Ht; inversion Ht.
Qed.

Lemma seq_implies_ghb1_int :
  forall E X x y,
  weaker ->
  well_formed_event_structure E ->
  R.covered E X s ->
  tc (rel_seq (rel_union (rel_union (A1bWmm.mhb' E X) (rf_sub X))
   (rel_union (rel_seq (ws X) (rf_sub X)) (rel_seq (fr E X) (rf_sub X)))) (tc (A2n.ppo E))) x y ->
  tc (rel_union (A1bWmm.ghb E X) (s E X)) x y.
Proof.
intros E X x y Hwk Hwf Hfb Hxy.

induction Hxy.
  destruct H as [z [Hxz Hzy]].
    inversion Hxz as [Hu | Hs].
    inversion Hu as [Hmhb'1 | Hrf_sub].
      apply trc_ind with z.
        rewrite (ghb1b_eq E X).
        apply tc_incl with (rel_union (rel_union (ws X) (fr E X))
        (rel_union (rel_union (mrf1 X) (A1.ppo E)) (A1b.abc E X))).
        intros e1 e2 H12; left; auto.
        apply (mhb'1_eq Hmhb'1).

        apply tc_incl with (A2n.ppo E); auto.
        intros e1 e2 H12; apply ppo2_in_ghb1; auto.

        generalize (tc_dec Hzy); intros [z' [Hzz' Hor]].
        inversion Hor as [Htc | Heq].
          apply trc_ind with z'.

        inversion Hu as [Hmhb | Hrfs].
          apply trc_ind with z.
        rewrite (ghb1b_eq E X).
        apply tc_incl with (rel_union (rel_union (ws X) (fr E X))
        (rel_union (rel_union (mrf1 X) (A1.ppo E)) (A1b.abc E X))).
        intros e1 e2 H12; left; auto.
        apply (mhb'1_eq Hmhb).
        apply tc_incl with (A2n.ppo E); auto.
        intros e1 e2 H12; apply ppo2_in_ghb1; auto.
          apply trc_step; auto.
       apply trc_step; right;
       apply (rf_sub_seq_ppo2_in_ab1 E X x z z' Hwf Hfb Hrf_sub Hzz').
        apply tc_incl with (A2n.ppo E); auto.
        intros e1 e2 H12; apply ppo2_in_ghb1; auto.
       rewrite <- Heq; apply trc_step; right;
       apply (rf_sub_seq_ppo2_in_ab1 E X x z z' Hwf Hfb Hrf_sub Hzz').

  inversion Hs as [Hsws | Hsfr].
    destruct Hsws as [e [Hxe Hez]].
        generalize (tc_dec Hzy); intros [z' [Hzz' Hor]].
        inversion Hor as [Htc | Heq].
          apply trc_ind with z'.
    apply trc_ind with e; apply trc_step.
        rewrite (ghb1b_eq E X).
      left; left; left; auto.

      right. apply rf_sub_seq_ppo2_in_ab1 with z; auto.
      apply tc_incl with (A2n.ppo E); auto.
      intros e1 e2 H12; apply ppo2_in_ghb1; auto.

    apply trc_ind with e; apply trc_step.
        rewrite (ghb1b_eq E X).
      left; left; left; auto.

      right. apply rf_sub_seq_ppo2_in_ab1 with z; auto.
      rewrite <- Heq; auto.

    destruct Hsfr as [e [Hxe Hez]].

        generalize (tc_dec Hzy); intros [z' [Hzz' Hor]].
        inversion Hor as [Htc | Heq].
          apply trc_ind with z'.
    apply trc_ind with e.
    apply trc_step.
        rewrite (ghb1b_eq E X).
      left; left; right; auto.

      apply trc_step; right; apply rf_sub_seq_ppo2_in_ab1 with z; auto.
      apply tc_incl with (A2n.ppo E); auto.
          intros e1 e2 H12; apply ppo2_in_ghb1; auto.

    rewrite <- Heq; apply trc_ind with e.
    apply trc_step.
        rewrite (ghb1b_eq E X).
      left; left; right; auto.

      apply trc_step; right; apply rf_sub_seq_ppo2_in_ab1 with z; auto.

apply trc_ind with z; auto.
Qed.

Lemma seq_implies_ghb1 :
  forall E X x y,
  weaker ->
  well_formed_event_structure E ->
  R.covered E X s ->
  tc (rel_seq (maybe (rel_union (rel_union (A1bWmm.mhb' E X) (rf_sub X))
   (rel_union (rel_seq (ws X) (rf_sub X)) (rel_seq (fr E X) (rf_sub X))))) (tc (A2n.ppo E))) x y ->
  tc (rel_union (A1bWmm.ghb E X) (s E X)) x y.
Proof.
intros E X x y Hwk Hwf Hfb Hxy.

induction Hxy.
  destruct H as [z [Hor Hzy]].
    inversion Hor as [Hxz | Heq].
      apply seq_implies_ghb1_int; auto.
        apply trc_step; exists z; auto.
   subst; generalize Hzy; apply tc_incl.
  intros e1 e2 H12; apply ppo2_in_ghb1; auto.

  apply trc_ind with z; auto.
Qed.

Lemma min_covered_implies_no_min_cy :
  forall E X, well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  R.covered E X s ->
  ~(exists cy, crit_cy_or E X cy).
Proof.
intros E X Hwf Hv1 Hc [cy [Hicy [? [Hnac ?]]]].
assert (  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X)) as Hs.
  destruct_valid Hv1; split; split; auto.
generalize (not_forall_exists_tc Hnac); intros [x Hx].
generalize (tc_cy_in_tc E X cy Hicy x x Hx); intros Hx'.
generalize (tc_mhbd_ppo2_in_mhb_ppo2 E X x x Hx'); intro Htc.
change (A2.ppo E) with (A2n.ppo E) in Htc.
change (A2nWmm.mhb E X) with (A2nBasic.AWmm.mhb E X) in Htc.
assert (exists y, tc (rel_seq (maybe (A2nWmm.mhb' E X)) (tc (A2.ppo E))) y y) as Hcyc.
eapply (A2nBasic.mhb_union_ppo_cycle_implies_mhb'_seq_ppo_cycle2
  X Hwf Hs Htc); auto; apply Htc.
destruct Hcyc as [y Hcyc].
generalize (mhb'_ppo2_is_u_seq wk Hwf Hcyc); intro Hcy'.
assert (rfmaps_well_formed E (events E) (rf X)) as Hrfwf.
  destruct Hs; auto.
generalize (seq_implies_ghb1 E X y y wk Hwf Hc Hcy');
rewrite union_triv; intro Hcycle.
generalize (s_ghb E X Hwf Hv1 y); intro. contradiction.
Qed.

Lemma covering_s :
  forall E X, well_formed_event_structure E ->
    A1Wmm.valid_execution E X ->
    R.covered E X s -> acyclic (A2nWmm.ghb E X).
Proof.
intros E X Hwf Hv1 Hc z Hz.
generalize (exists_crit_cy_or E X Hz);
intros [cy Hcy].
assert (exists cy, crit_cy_or E X cy) as Hex.
  exists cy; auto.
generalize (min_covered_implies_no_min_cy E X Hwf Hv1 Hc); intro Hnex.
contradiction.
Qed.

End RacyMin.

End Cm.

End CritSC.
