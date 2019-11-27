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
Import OEEvt.
Set Implicit Arguments.

Module Racy (A1 A2: Archi) (dp:Dp).
Module Wk := (*Hierarchy.*)Weaker A1 A2 dp.
Import Wk.
Module VA2 := Valid A2 dp.
Import VA2. Import VA2.ScAx.
Module Covering := Covering A1 A2 dp.
Import Covering.
Module A2Basic := Basic A2 dp.

Lemma mrf2_in_rf :
  forall X x y,
  mrf2 X x y ->
  rf X x y.
Proof.
intros X x y Hxy.
unfold mrf2 in Hxy; unfold mrfi2 in Hxy; unfold mrfe2 in Hxy.
case_eq A2.intra; case_eq A2.inter; intros Hinter Hintra;
  rewrite Hinter in Hxy; rewrite Hintra in Hxy; simpl in Hxy;
inversion Hxy as [Hrfintra | Hrfinter].
  destruct Hrfintra; auto.
  destruct Hrfinter; auto.
  destruct Hrfintra; auto.
  destruct Hrfinter; auto.
  destruct Hrfintra; auto.
  destruct Hrfinter; auto.
  destruct Hrfintra; auto.
  destruct Hrfinter; auto.
Qed.

Definition AC X s :=
  forall (x z y:Event), rf_sub X x z /\ s z y -> s x y.
Definition fragile X r :=
  exists w, rf_sub X w r.

Module Type SafetyNet.
Parameter s : Event_struct -> Execution_witness -> Rln Event.
Hypothesis s_ghb :
  forall E X,
  well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  acyclic (rel_union (s E X) (A1Wmm.ghb E X)).
Hypothesis s_ppo2 :
  forall E X,
  well_formed_event_structure E ->
  acyclic (rel_union (s E X) (A2n.ppo E)).
Hypothesis s_ac : forall E X, AC X (s E X).


Definition competing E X :=
  rel_union (ppo_sub E) (fun e1 e2 => A2.ppo E e1 e2 /\ fragile X e1)(*(rel_seq (rf_sub X) (A2.ppo E))*).
Definition cns E X :=
  fun e1 => fun e2 => competing E X e1 e2 /\ ~ (s E X e1 e2 \/ s E X e2 e1).
Hypothesis prop_stable :
  forall E X x y,
  well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  competing E X x y ->
  ~ (s E X x y \/ s E X y x) ->
  (exists Y, A2nWmm.valid_execution E Y /\
  competing E Y x y /\ ~ (s E Y x y \/ s E Y y x)).
(*  forall E X Y x y,
  competing E X x y ->
  ~ (s E X x y \/ s E X y x) ->
  rf Y = so_rfm E
         (LE (tc (rel_union (rel_union (rel_inter (cns E X) (pair x y)) (A2.ppo E)) (pio_llh E)))) ->
  ws Y = so_ws
         (LE (tc (rel_union (rel_union (rel_inter (cns E X) (pair x y)) (A2.ppo E)) (pio_llh E)))) ->
  competing E Y x y /\ ~ (s E Y x y \/ s E Y y x).*)
Definition covered E X r :=
  forall e1 e2, (competing E X e1 e2) -> (r E X e1 e2 \/ r E X e2 e1).
Definition covering s :=
  forall E X, well_formed_event_structure E ->
    A1Wmm.valid_execution E X ->
    covered E X s -> acyclic (A2nWmm.ghb E X).
(*Hypothesis s_fun :
   forall E X r x y,
    well_formed_event_structure E ->
    (s E X x y /\ r x /\ r y <->
    s (mkes (Intersection Event (events E) r) (rrestrict (iico E) r))
    ((mkew (rrestrict (ws X) r) (rrestrict (rf X) r))) x y).*)
End SafetyNet.

Definition srfs E :=
  fun e1 => fun e2 => loc e1 = loc e2 /\
    writes E e1 /\ reads E e2 /\
  (exists X, rf_sub X e1 e2).

Module Barriers (SN:SafetyNet) <: Compete.
Definition fragile X r :=
  exists w, rf_sub X w r.
Definition competing E X :=
  rel_union (ppo_sub E) (fun e1 e2 => A2.ppo E e1 e2 /\ fragile X e1)(*(rel_seq (rf_sub X) (A2.ppo E))*).

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
     apply A2Basic.po_iico_domain_in_events with y |
     change (events E y) with (In _ (events E) y);
     apply A2Basic.po_iico_range_in_events with x]; auto;
    apply A2.ppo_valid; auto.
  destruct Hrf as [Hppo Hrf]; split;
  [change (events E x) with (In _ (events E) x);
    destruct Hrf as (*[? [[? ?] ?]]*) [z Hrf]|
   change (events E y) with (In _ (events E) y);
   apply A2Basic.po_iico_range_in_events with (*z*) x; auto; apply A2.ppo_valid]; auto.
    destruct Hrf as [? ?];
   apply A2Basic.ran_rf_in_events with X z; auto.
   apply mrf2_in_rf; auto.
Qed.

Definition cns E X :=
  fun e1 => fun e2 => competing E X e1 e2 /\ ~ (SN.s E X e1 e2 \/ SN.s E X e2 e1).

Lemma cns_ppo_in_cns_po :
  forall E X x y e1 e2,
  competing E X x y ->
  tc (rel_union (rel_union (rel_inter (cns E X) (pair x y)) (A2.ppo E)) (pio_llh E)) e1 e2 ->
  tc (rel_union (rel_inter (cns E X) (pair x y)) (po_iico E)) e1 e2.
Proof.
intros E X x y e1 e2 Hc H12.
induction H12 as [e1 e2 Huu |].
  inversion Huu as [Hu | Hpio].
    inversion Hu as [Hxy | Hppo];
      apply trc_step; [left | right]; auto.
      apply A2.ppo_valid; auto.
      apply trc_step; right; destruct Hpio as [? [? ?]]; auto.
  apply trc_ind with z; auto.
Qed.

Ltac destruct_valid H :=
  destruct H as [[Hws_tot Hws_cands] [[Hrf_init [Hrf_cands Hrf_uni]] [Hsp [Hth Hvalid]]]];
  unfold write_serialization_well_formed in Hws_tot(*; unfold uniproc in Hsp*).

Definition s := SN.s.
Definition covered E X r :=
  forall e1 e2, (competing E X e1 e2) -> (r E X e1 e2 \/ r E X e2 e1).

Module A2nBasic := Basic A2n.
Lemma ppo2_in_ghb1 :
  forall E X x y,
  well_formed_event_structure E ->
  covered E X s ->
  A2n.ppo E x y ->
  (rel_union (SN.s E X) (A1Wmm.ghb E X)) x y.
Proof.
intros E X x y Hwf Hp Hxy.
  generalize (excluded_middle (A1.ppo E x y)); intro Hor.
  inversion Hor as [Hppo1 | Hnppo1].
   right; apply A1Basic.ppo_in_ghb; auto.
   assert (ppo_sub E x y) as Hppos.
     split; auto.
 assert (competing E X x y) as Hcxy.
   left; auto.
 generalize (Hp x y Hcxy); intro Hors; inversion Hors; [left; auto|].
 assert (tc (rel_union (s E X) (A2n.ppo E)) x x) as Hc.
   apply trc_ind with y; apply trc_step; [right | left]; auto.
 generalize (SN.s_ppo2 Hwf Hc); intro Ht; inversion Ht.
Qed.

Lemma rf_sub_in_srfs :
  forall E X x y,
  rfmaps_well_formed E (events E) (rf X) ->
  rf_sub X x y -> srfs E x y.
Proof.
intros E X x y [? [Hrfm ?]] Hrfs.
generalize Hrfs; intros [Hmrf2 ?].
assert (rf X x y) as Hrf.
inversion Hmrf2 as [Hi | He].
  unfold mrfi2 in Hi; case_eq A2.intra; intro Heq;
  rewrite Heq in Hi.
    destruct Hi; auto.
    inversion Hi.
  unfold mrfe2 in He; case_eq A2.inter; intro Heq;
  rewrite Heq in He.
    destruct He; auto.
    inversion He.
generalize (Hrfm x y Hrf); intros [? [? [l [[vx Hwx] [[vy Hry] ?]]]]];
  split; [|split; [|split]].
  unfold loc; rewrite Hwx; rewrite Hry; auto.
  split; auto. exists l; exists vx; auto.
  split; auto. exists l; exists vy; auto.
exists X; auto.
Qed.

Lemma rf_sub_seq_ppo2_in_ab1 :
  forall E X x z y,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  covered E X s ->
  (*AC X (SN.s E X) ->*)
  rf_sub X x z ->
  A2n.ppo E z y ->
  SN.s E X x y.
Proof.
intros E X x z y Hwf Hrfwf Hfb (*Hac*) Hxz Hzy.
assert (rf_sub X x z /\ SN.s E X z y) as Hs.
  split; auto.
assert (competing E X z y) as Hczy.
  right; split; auto.
  exists x; auto.
generalize (Hfb z y Hczy); intro Hor; inversion Hor; auto.
assert (tc (rel_union (s E X) (A2n.ppo E)) z z) as Hcy.
  apply trc_ind with y; apply trc_step; [right | left]; auto.
generalize (SN.s_ppo2 Hwf Hcy); intro Ht; inversion Ht.
(*fold (s E); rewrite <- Hfb; right.*)

apply (SN.s_ac Hs); split; auto.

(*apply rf_sub_in_srfs with X; auto.*)
Qed.

Lemma ghb1_eq :
  forall E X,
  A1Wmm.ghb E X = rel_union (rel_union (ws X) (fr E X))
                                        (rel_union (rel_union (mrf1 X) (A1.ppo E))
                                            (A1.abc E X)).
Proof.
intros E X; unfold A1Wmm.ghb; unfold mrf1; unfold mrfi1; unfold mrfe1;
  case_eq A1.inter; case_eq A1.intra; intros Hintra Hinter; simpl;
  apply ext_rel; split; intro Hxy.

  inversion Hxy as [Hrfe | Hr].
    right; left; left; right; auto.
    inversion Hr as [Hrfi | Hre].
      right; left; left; left; auto.
      inversion Hre as [Hab | Hres].
        right; right; auto.
        inversion Hres as [Hws_fr | Hppo].
          left; auto.
            right; left; right; auto.

  inversion Hxy as [Hws_fr | Hr].
    right; right; right; left; auto.
    inversion Hr as [Hre | Hab].
      inversion Hre as [Hrf | Hppo].
        inversion Hrf as [Hrfi | Hrfe]; [right; left; auto | left; auto].
        right; right; right; right; auto.
      right; right; left; auto.

  inversion Hxy as [Hrfe | Hr].
    right; left; left; right; auto.
    inversion Hr as [Hab | Hre].
      right; right; auto.
      inversion Hre as [Hws_fr | Hppo].
        left; auto.
          right; left; right; auto.

  inversion Hxy as [Hws_fr | Hr].
    right; right; left; auto.
    inversion Hr as [Hre | Hab].
      inversion Hre as [Hrf | Hppo].
        inversion Hrf as [Ht | Hrfi].
          inversion Ht.
          left; auto.
        right; right; right; auto.
      right; left; auto.

  inversion Hxy as [Hrfi | Hr].
    right; left; left; left; auto.
    inversion Hr as [Hab | Hre].
      right; right; auto.
      inversion Hre as [Hws_fr | Hppo].
        left; auto.
          right; left; right; auto.

  inversion Hxy as [Hws_fr | Hr].
    right; right; left; auto.
    inversion Hr as [Hre | Hab].
      inversion Hre as [Hrf | Hppo].
        inversion Hrf as [Hrfi | Ht].
          left; auto.
          inversion Ht.
        right; right; right; auto.
      right; left; auto.

  inversion Hxy as [Hab | Hr].
    right; right; auto.
    inversion Hr as [Hws_fr | Hppo].
      left; auto.
        right; left; right; auto.

  inversion Hxy as [Hws_fr | Hr].
    right; left; auto.
    inversion Hr as [Hre | Hab].
      inversion Hre as [Ht | Hppo].
        inversion Ht as [Ht1 | Ht2]; [inversion Ht1 | inversion Ht2].
        right; right; auto.
      left; auto.
Qed.

Lemma mhb1_eq :
  forall E X x y,
  A1Wmm.mhb E X x y ->
  tc
  (rel_union (rel_union (ws X) (fr E X))
     (rel_union (rel_union (mrf1 X) (A1.ppo E))
     (A1.abc E X) )) x y.
Proof.
unfold A1Wmm.mhb; case_eq A1.inter; case_eq A1.intra; intros Hintra Hinter;
unfold A1b.inter; unfold A1b.intra; unfold mrf1; unfold mrfi1; unfold mrfe1;
rewrite Hinter; rewrite Hintra; intros E X x y Hxy; apply trc_step; simpl.

inversion Hxy as [Hrfe | Hr].
  right; left; left; right; auto.
  inversion Hr as [Hrfi | Hws_fr].
    right; left; left; left; auto.
    left; auto.

inversion Hxy as [Hrfe | Hws_fr].
  right; left; left; right; auto.
  left; auto.

inversion Hxy as [Hrfi | Hws_fr].
  right; left; left; left; auto.
  left; auto.

left; auto.
Qed.

Lemma mhb'1_eq :
  forall E X x y,
  A1Wmm.mhb' E X x y ->
  tc
  (rel_union (rel_union (ws X) (fr E X))
     (rel_union (rel_union (mrf1 X) (A1.ppo E))
     (A1.abc E X) )) x y.
Proof.
intros E X x y Hxy;
inversion Hxy as [Hu | Hsfr].
  inversion Hu as [Hmhb | Hsws].
    apply mhb1_eq; auto.

    destruct Hsws as [z [Hxz Hzy]]; apply trc_ind with z; apply trc_step.
      left; left; auto.
      right; left; left; auto.

    destruct Hsfr as [z [Hxz Hzy]]; apply trc_ind with z; apply trc_step.
      left; right; auto.
      right; left; left; auto.
Qed.


Lemma seq_implies_ghb1_int :
  forall E X x y,
  weaker ->
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  covered E X s ->
  tc (rel_seq (rel_union (rel_union (A1Wmm.mhb' E X) (rf_sub X))
   (rel_union (rel_seq (ws X) (rf_sub X)) (rel_seq (fr E X) (rf_sub X)))) (tc (A2n.ppo E))) x y ->
  tc (rel_union (SN.s E X) (A1Wmm.ghb E X)) x y.
Proof.
intros E X x y Hwk Hwf Hrfwf Hfb (*Hac*) Hxy.

induction Hxy.
  destruct H as [z [Hxz Hzy]].
    inversion Hxz as [Hu | Hs].
    inversion Hu as [Hmhb'1 | Hrf_sub].
      apply trc_ind with z.
        rewrite (ghb1_eq E X).
        apply tc_incl with (rel_union (rel_union (ws X) (fr E X))
       (rel_union (rel_union (mrf1 X) (A1.ppo E)) (A1.abc E X))).
          intros e1 e2 H12; right; auto.
        apply (mhb'1_eq Hmhb'1).
        generalize Hzy; apply tc_incl.
        intros e1 e2 H12; apply ppo2_in_ghb1; auto.

        generalize (tc_dec Hzy); intros [z' [Hzz' Hor]].
        inversion Hor as [Htc | Heq].
          apply trc_ind with z'.
        rewrite (ghb1_eq E X).
      apply trc_step; left.
       apply (rf_sub_seq_ppo2_in_ab1 Hwf Hrfwf Hfb (*Hac*) Hrf_sub Hzz').
         change (A2n.ppo E) with (A2.ppo E) in Htc;
         generalize Htc; apply tc_incl;
         intros e1 e2 H12; apply ppo2_in_ghb1; auto.
         subst.
      apply trc_step; left.
       apply (rf_sub_seq_ppo2_in_ab1 Hwf Hrfwf Hfb (*Hac*) Hrf_sub Hzz').

  inversion Hs as [Hsws | Hsfr].
    destruct Hsws as [e [Hxe Hez]].
        generalize (tc_dec Hzy); intros [z' [Hzz' Hor]].
        inversion Hor as [Htc | Heq].
          apply trc_ind with z'.
    apply trc_ind with e; apply trc_step.
        rewrite (ghb1_eq E X).
      right; left; left; auto.
      left. apply rf_sub_seq_ppo2_in_ab1 with (*X*) z; auto.
        generalize Htc; apply tc_incl; intros e1 e2 H12;
        apply ppo2_in_ghb1; auto.

  subst;     apply trc_ind with e; apply trc_step.
        rewrite (ghb1_eq E X).
      right; left; left; auto.
      left. apply rf_sub_seq_ppo2_in_ab1 with (*X*) z; auto.

    destruct Hsfr as [e [Hxe Hez]].

        generalize (tc_dec Hzy); intros [z' [Hzz' Hor]].
        inversion Hor as [Htc | Heq].
          apply trc_ind with z'.
    apply trc_ind with e; apply trc_step.
        rewrite (ghb1_eq E X).
      right; left; right; auto.
      left;  apply rf_sub_seq_ppo2_in_ab1 with (*X*) z; auto.
      generalize Htc; apply tc_incl; intros e1 e2 H12;
      apply ppo2_in_ghb1; auto.

  subst;     apply trc_ind with e; apply trc_step.
        rewrite (ghb1_eq E X).
      right; left; right; auto.
      left;  apply rf_sub_seq_ppo2_in_ab1 with (*X*) z; auto.

apply trc_ind with z; auto.
Qed.

Lemma seq_implies_ghb1 :
  forall E X x y,
  weaker ->
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  covered E X s ->
  tc (rel_seq (maybe (rel_union (rel_union (A1bWmm.mhb' E X) (rf_sub X))
   (rel_union (rel_seq (ws X) (rf_sub X)) (rel_seq (fr E X) (rf_sub X))))) (tc (A2n.ppo E))) x y ->
  tc (rel_union (SN.s E X) (A1Wmm.ghb E X)) x y.
Proof.
intros E X x y Hwk Hwf Hrfwf Hfb (*Hac*) Hxy.

induction Hxy.
  destruct H as [z [Hor Hzy]].
    inversion Hor as [Hxz | Heq].
      apply seq_implies_ghb1_int; auto.
        apply trc_step; exists z; auto.
   subst; generalize Hzy; apply tc_incl.
  intros e1 e2 H12; apply ppo2_in_ghb1; auto.

  apply trc_ind with z; auto.
Qed.

Lemma barriers_thm :
  forall E X,
  weaker ->
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) -> (*AC X (SN.s E X) ->*)
    (covered E X s -> (exists x, tc (A2nWmm.ghb E X) x x) ->
      exists y, tc (rel_union (SN.s E X) (A1Wmm.ghb E X)) y y).
Proof.
intros E X Hwk Hwf Hs (*Hac*) Hp [x Hx].
rewrite (ghb2_is_mhb_ppo2 E X) in Hx.
change (A2.ppo E) with (A2n.ppo E) in Hx.
change (A2nWmm.mhb E X) with (A2nBasic.AWmm.mhb E X) in Hx.
assert (exists y, tc (rel_seq (maybe (A2nWmm.mhb' E X)) (tc (A2.ppo E))) y y) as Hc.
eapply (A2nBasic.mhb_union_ppo_cycle_implies_mhb'_seq_ppo_cycle2 X Hwf Hs Hx); auto; apply Hx.
destruct Hc as [y Hc].
generalize (mhb'_ppo2_is_u_seq Hwk Hwf Hc); intro Hcy.
destruct Hs as [? Hrfwf];
exists y; apply (seq_implies_ghb1 Hwk Hwf Hrfwf Hp (*Hac*) Hcy).
Qed.

Hypothesis wk : weaker.

Lemma convoluted_covering_holds : forall E X,
    well_formed_event_structure E ->
    A1Wmm.valid_execution E X ->
    (*AC X (SN.s E X) ->*)
    exists r,
    (acyclic (rel_union (SN.s E X) r)) /\
    (covered E X s -> (exists x, tc (A2nWmm.ghb E X) x x) ->
      exists y, tc (rel_union (SN.s E X) r) y y).
Proof.
intros E X Hwf Hv1 (*Hac*); exists (A1Wmm.ghb E X);
  split; [| intro Hp].
  apply SN.s_ghb; auto.
  apply barriers_thm; auto.
  apply wk. destruct_valid Hv1; split; split; auto.
Qed.

Definition convoluted_covering :=
  forall E X, well_formed_event_structure E ->
    A1Wmm.valid_execution E X ->
    exists r,
    (acyclic (rel_union (s E X) r)) /\
    (covered E X s -> (exists x, tc (A2nWmm.ghb E X) x x) ->
      exists y, tc (rel_union (s E X) r) y y).

Lemma covering_implied_by_convoluted_covering :
  convoluted_covering ->
   forall E X, well_formed_event_structure E ->
    A1Wmm.valid_execution E X ->
    covered E X s -> acyclic (A2nWmm.ghb E X).
Proof.
intros Hconv E X Hwf Hv1 Hc x Hx.
generalize (Hconv E X Hwf Hv1); intros [r [Hacsr Himpl]].
assert (exists x, tc (A2nWmm.ghb E X) x x) as Hcx.
  exists x; auto.
generalize (Himpl Hc Hcx); intros [y Hy].
apply (Hacsr y Hy).
Qed.

Lemma covering_s :
  forall E X, well_formed_event_structure E ->
    A1Wmm.valid_execution E X ->
    covered E X s -> acyclic (A2nWmm.ghb E X).
Proof.
apply covering_implied_by_convoluted_covering.
unfold convoluted_covering; apply convoluted_covering_holds.
Qed.

(*Lemma wf :
  forall E X x y,
  well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  competing E X x y ->
  ~ (s E X x y \/ s E X y x) ->
  (exists Y, A2nWmm.valid_execution E Y /\
  competing E Y x y /\ ~ (s E Y x y \/ s E Y y x)).
Proof.
apply SN.prop_stable.
Qed.*)

Lemma mrf_in_rf :
  forall X x y,
  A2nWmm.mrf X x y ->
  rf X x y.
Proof.
unfold A2nWmm.mrf; unfold A2nWmm.mrfi; unfold A2nWmm.mrfe;
intros X x y Hxy; case_eq A2n.inter; case_eq A2n.intra;
intros Hintra Hinter; rewrite Hintra in Hxy; rewrite Hinter in Hxy;
simpl in Hxy; inversion Hxy; destruct H; auto.
Qed.

Lemma rfs_seq_po_in_u :
  forall E X x y,
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  rf_sub X x y ->
  po_iico E y x ->
  pio_llh E y x.
Proof.
intros E X x y Hs [Hmrf ?] Hppo.
assert (rf X x y) as Hrf.
  apply mrf_in_rf; auto.
split; [|split]; auto.
apply sym_eq; apply A2nBasic.rf_implies_same_loc2 with E X; auto.
intros [? [? [? [? Hrx]]]].
destruct Hs as [? Hrfwf].
destruct_rf Hrfwf.
generalize (A2nBasic.dom_rf_is_write E X x y Hrf_cands Hrf);
intros [? [? Hwx]]; rewrite Hwx in Hrx; inversion Hrx.
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
  destruct H as [Hz ?]; generalize (A2.ppo_valid Hz); intro Hcy.
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
 generalize (A2.ppo_valid Hzz).
 apply A2Basic.po_ac; auto.
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
  destruct H as [Hz ?]; generalize (A2.ppo_valid Hz); intro Hxy.
  assert (po_iico E x x) as Hcy.
    apply A2Basic.po_trans with y; auto.
  apply (A2Basic.po_ac Hwf Hcy).
(*    destruct H as [z' [Hzz' Hz'z]].
  assert (po_iico E z' x) as Hpo. *)

    destruct H as [Hxy ?].
    assert (po_iico E x y) as Hpo.
    (*apply A2nBasic.po_trans with y; auto.*)
    apply A2.ppo_valid; auto.
    assert (po_iico E x x) as Hxx.
      apply A2nBasic.po_trans with y; auto.
    generalize Hxx; apply A2nBasic.po_ac; auto.
Qed.

Definition covering s :=
  forall E X, well_formed_event_structure E ->
    A1Wmm.valid_execution E X ->
    covered E X s -> acyclic (A2nWmm.ghb E X).

(*Lemma s_fun :
   forall E X r x y,
    well_formed_event_structure E ->
    (s E X x y /\ r x /\ r y <->
    s (mkes (Intersection Event (events E) r) (rrestrict (iico E) r))
    ((mkew (rrestrict (ws X) r) (rrestrict (rf X) r))) x y).
Proof.
unfold s; apply SN.s_fun.
Qed.*)
End Barriers.

(*Module BarriersGuarantee (SN:SafetyNet).
Module Bars := Barriers SN.
Module Pres := Preservation Bars.
Import Pres.

Lemma barriers_guarantee :
  (forall E X, A2nWmm.valid_execution E X -> Bars.covered E X Bars.s) ->
  (forall E X, well_formed_event_structure E ->
   (A1Wmm.valid_execution E X <-> A2nWmm.valid_execution E X)).
Proof.
apply stab_dir.
Qed.
End BarriersGuarantee.*)

End Racy.
