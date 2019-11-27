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
Require Import Classical_Prop.
Import OEEvt.
Set Implicit Arguments.

Module Covering (A1 A2: Archi) (dp:Dp).
Module Wk := (* Hierarchy. *)Weaker A1 A2 dp.
Import Wk.
Hypothesis wk : weaker.
Module VA2 := Valid A2n dp.
Import VA2. Import VA2.ScAx.
Set Implicit Arguments.
Definition rel_inter A (r1 r2 : Rln A) :=
  fun x => fun y => r1 x y /\ r2 x y.
Unset Implicit Arguments.
Definition pair (x y : Event): Rln Event :=
  fun e1 => fun e2 => (e1 = x /\ e2 = y).

Module Type Compete.
Parameter competing : Event_struct -> Execution_witness -> Rln Event.
Parameter compete_in_events :
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
Parameter competing_irr : forall E X,
  well_formed_event_structure E ->
    A1Wmm.valid_execution E X ->
  ~ (exists z, competing E X z z).
Parameter competing_not_po :
  forall E X x y, well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  competing E X x y -> ~ (po_iico E y x).
Parameter covering_s : covering s.
End Compete.

Module Preservation (C: Compete).

Import C.

Definition convoluted_wf :=
  forall E X Y x y,
  competing E X x y ->
  ~ (s E X x y \/ s E X y x) ->
  rf Y = so_rfm E
         (LE (tc (rel_union (rel_union (rel_inter (cns E X) (pair x y)) (A2.ppo E)) (pio_llh E)))) ->
  ws Y = so_ws
         (LE (tc (rel_union (rel_union (rel_inter (cns E X) (pair x y)) (A2.ppo E)) (pio_llh E)))) ->
  competing E Y x y /\ ~ (s E Y x y \/ s E Y y x).

Lemma udr_xy_ppo2_in_events :
  forall E X r x y,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  competing E X x y ->
  Included _   (Union _ (dom (tc (rel_union (rel_union (rel_inter r (pair x y)) (A2.ppo E)) (pio_llh E))))
     (ran (tc (rel_union (rel_union (rel_inter r (pair x y)) (A2.ppo E)) (pio_llh E))))) (events E).
Proof.
intros E X r x y Hwf Hwfrf Hc e1 Hudr.
generalize (compete_in_events E X x y Hwf Hwfrf Hc); intros [Hex Hey].
inversion Hudr as [e Hd |e Hr].
generalize (dom_tc_in_dom Hd); intros [e2 Hi];
  inversion Hi as [Hu | Hpio].
  inversion Hu as [Hp | Hppo].
  destruct Hp as [? [? ?]]; subst; auto.
apply A2Basic.po_iico_domain_in_events with e2; auto.
apply A2.ppo_valid; auto.
destruct Hpio as [? [Hpo ?]].
apply A2Basic.po_iico_domain_in_events with e2; auto.
generalize (ran_tc_in_ran Hr); intros [e2 Hi];
  inversion Hi as [Hu | Hpio].
  inversion Hu as [Hp | Hppo].
  destruct Hp as [? [? ?]]; subst; auto.
apply A2Basic.po_iico_range_in_events with e2; auto.
apply A2.ppo_valid; auto.
destruct Hpio as [? [Hpo ?]].
apply A2Basic.po_iico_range_in_events with e2; auto.
Qed.

Ltac destruct_valid H :=
  destruct H as [[Hws_tot Hws_cands] [[Hrf_init [Hrf_cands Hrf_uni]] [Hsp [Hth Hvalid]]]];
  unfold write_serialization_well_formed in Hws_tot(*; unfold uniproc in Hsp*).

Lemma u_in_pair_po :
  forall E X x y e1 e2,
  tc (rel_union (rel_union (rel_inter (cns E X) (pair x y)) (A2.ppo E))
          (pio_llh E)) e1 e2 ->
  tc (rel_union (rel_inter (cns E X) (pair x y)) (po_iico E)) e1 e2.
Proof.
intros E X x y e1 e2 H12.
induction H12 as [e1 e2 Hu |]; [apply trc_step|].
  inversion Hu as [Hun | Hpio].
    inversion Hun as [Hp | Hppo].
      left; auto.
      right; apply A2.ppo_valid; auto.
      right; destruct Hpio as [? [? ?]]; auto.
  apply trc_ind with z; auto.
Qed.

Lemma pair_irr :
  forall E X x y,
  well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  ~ (exists z, (rel_inter (cns E X) (pair x y) z z)).
Proof.
intros E X x y Hwf Hv1 [z [[Hx Hy] [Hc ?]]].
destruct Hc as [? [? [? [Hdp ?]]]].
   assert (exists z, competing E X z z) as Hc.
     exists z; auto.
    apply (competing_irr E X Hwf Hv1 Hc).
Qed.

Lemma tc_pair_po_in_pair_po :
  forall E X x y,
  well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
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
  A1Wmm.valid_execution E X ->
  competing E X x y ->
  (forall z, ~ tc (rel_union (rel_union (rel_inter (cns E X) (pair x y)) (A2.ppo E)) (pio_llh E)) z z).
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
  forall E X x y,
  well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  competing E X x y ->
  ~ (s E X x y \/ s E X y x) ->
  (exists Y, A2nWmm.valid_execution E Y /\
  competing E Y x y /\ ~ (s E Y x y \/ s E Y y x)).
Proof.
intros Hcwf E X x y Hwf Hv1 Hcxy Hns.
assert (exists so, vexec E so /\
               so_rfm E so = (so_rfm E
                 (LE (tc (rel_union (rel_union (rel_inter (cns E X) (pair x y))
                       (A2.ppo E)) (pio_llh E))))) /\
               so_ws so = (so_ws
               (LE (tc (rel_union (rel_union (rel_inter (cns E X) (pair x y))
                       (A2.ppo E)) (pio_llh E)))))) as Hvexec.
  exists (LE (tc (rel_union (rel_union (rel_inter (cns E X) (pair x y))
                       (A2.ppo E)) (pio_llh E)))).
  split; [|split]; auto.

  assert (partial_order (tc (rel_union (rel_union (rel_inter (cns E X) (pair x y)) (A2.ppo E)) (pio_llh E))) (events E)) as Hp.
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
              (rel_union (rel_union (rel_inter (cns E X) (pair x y)) (A2.ppo E))
                 (pio_llh E)))).
        intros e1 e2 H12; inversion H12 as [Hppo|]; auto.
        apply Hincl; apply trc_step; left; right; auto.
    generalize (lso_is_tc Hle); intro Htc.
    intros e He; rewrite Htc in He; destruct_lin Hle;
    apply (Hac e He).

      apply incl_ac with (LE
           (tc
              (rel_union (rel_union (rel_inter (cns E X) (pair x y)) (A2.ppo E))
                 (pio_llh E)))).
        intros e1 e2 H12; inversion H12 as [Hppo|]; auto.
        apply Hincl; apply trc_step; right; auto.
    generalize (lso_is_tc Hle); intro Htc.
    intros e He; rewrite Htc in He; destruct_lin Hle;
    apply (Hac e He).

generalize (ScModel.vexec_is_valid E
  (so_rfm E (LE (tc (rel_union (rel_union (rel_inter (cns E X) (pair x y))
                       (A2.ppo E)) (pio_llh E)))))
  (so_ws
               (LE (tc (rel_union (rel_union (rel_inter (cns E X) (pair x y))
                       (A2.ppo E)) (pio_llh E)))))
  Hwf Hvexec); intros [Y [Hv2Y [? ?]]].
  exists Y; split; auto.
  apply (Hcwf E X Y x y); auto.
Qed.

Lemma prop_implies_ac_ghb2 :
  forall E X,
  well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  covered E X s ->
  acyclic (A2nWmm.ghb E X).
Proof.
intros E X Hwf Hv1 Hp.
generalize (covering_s E X Hwf Hv1); intro Hc.
apply (Hc Hp).
Qed.

Lemma prop_implies_v2 :
  forall E X,
  well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  covered E X s ->
  A2nWmm.valid_execution E X.
Proof.
intros E X Hwf Hva1 Hp; generalize Hva1; intro Hv1; destruct_valid Hva1;
  split; [|split; [|split; [|split]]]; auto.
  split; auto. split; auto.
  apply prop_implies_ac_ghb2; auto.
Qed.

Module A2Basic := Basic A2.

Lemma not_prop_bak :
  forall E X,
  (exists x, exists y,
   competing E X x y /\ ~ (s E X x y \/ s E X y x)) ->
  ~ (covered E X s).
Proof.
intros E X [x [y [Hc Hns]]] Hp; apply Hns;
 apply (Hp x y Hc).
Qed.

Lemma not_prop_dir :
  forall E X,
  ~ (covered E X s) ->
  (exists x, exists y,
   (competing E X x y /\ ~ (s E X x y \/ s E X y x))).
Proof.
intros E X Hnp.
apply NNPP; intro Hxy; apply Hnp; unfold covered.
intros x y Hc.
  generalize (excluded_middle (s E X x y \/ s E X y x)); intro Hor;
  inversion Hor; auto.
  assert (exists x, exists y, (competing E X x y /\ ~ (s E X x y \/ s E X y x))) as Hco.
    exists x; exists y; split; auto.
  contradiction.
Qed.

Lemma ghb_incl' :
  forall E X,
  weaker -> rel_incl (A1.abc E X) (A2nWmm.ghb E X) ->
  rel_incl (A1Wmm.ghb E X) (A2nWmm.ghb E X).
Proof.
intros E X; rewrite (ghb2_eq E X).
unfold A1Wmm.ghb; unfold A2nWmm.mrf; unfold A2nWmm.mrfe; unfold A2nWmm.mrfi.
intros H12 Hi x y Hxy; case_eq A2n.inter; case_eq A2n.intra;
intros Hintra2 Hinter2; case_eq A1.inter; case_eq A1.intra;
intros Hintra1 Hinter1; rewrite Hintra1 in *; rewrite Hinter1 in *.
  (*A1 : true true ; A2 : true true*)
  inversion Hxy as [Hrfi | Hr].
    left; right; auto.
    inversion Hr as [Hrfi | Hre].
      left; left; auto.
      inversion Hre as [Ht | Hres].
      unfold A2nWmm.mrf; rewrite Hintra2 in Hi;
        rewrite Hinter2 in Hi; apply Hi; auto.
      right; fold (bot_ghb1 E X) in Hres.
      apply bot_ghb_incl; auto.
  (*A1 : false true ; A2 : true true*)
  inversion Hxy as [Hrfe | Hr].
    left; right; auto.
      inversion Hr as [Ht | Hres].
      unfold A2nWmm.mrf; rewrite Hintra2 in Hi;
        rewrite Hinter2 in Hi; apply Hi; auto.
      right; fold (bot_ghb2 E X); fold (bot_ghb1 E X) in Hr;
      apply bot_ghb_incl; auto.
  (*A1 : true false ; A2 : true true*)
  inversion Hxy as [Hrfi | Hr].
    left; left; auto.
      inversion Hr as [Ht | Hres].
      unfold A2nWmm.mrf; rewrite Hintra2 in Hi;
        rewrite Hinter2 in Hi; apply Hi; auto.
      right; fold (bot_ghb2 E X); fold (bot_ghb1 E X) in Hr;
      apply bot_ghb_incl; auto.
  (*A1 : false false ; A2 : true true*)
      inversion Hxy as [Ht | Hres].
      unfold A2nWmm.mrf; rewrite Hintra2 in Hi;
        rewrite Hinter2 in Hi; apply Hi; auto.
      right; fold (bot_ghb2 E X); fold (bot_ghb1 E X) in Hres;
      apply bot_ghb_incl; auto.
  (*A1 : true true ; A2 : false true*)
  destruct H12 as [? [Himpl ?]].
  unfold A1n.intra in Hintra1; unfold A2n.intra in Hintra2;
  rewrite Hintra1 in Himpl; rewrite Hintra2 in Himpl; inversion Himpl.
  (*A1 : false true ; A2 : false true*)
  inversion Hxy as [Hrfe | Hr].
    left; right; auto.
      inversion Hr as [Ht | Hres].
      unfold A2nWmm.mrf; rewrite Hintra2 in Hi;
        rewrite Hinter2 in Hi; apply Hi; auto.
      right; fold (bot_ghb2 E X); fold (bot_ghb1 E X) in Hres;
      apply bot_ghb_incl; auto.
  (*A1 : true false ; A2 : false true*)
  destruct H12 as [? [Himpl ?]].
  unfold A1n.intra in Hintra1; unfold A2n.intra in Hintra2;
  rewrite Hintra1 in Himpl; rewrite Hintra2 in Himpl; inversion Himpl.
  (*A1 : false false ; A2 : false true*)
      inversion Hxy as [Ht | Hres].
      unfold A2nWmm.mrf; rewrite Hintra2 in Hi;
        rewrite Hinter2 in Hi; apply Hi; auto.
      right; fold (bot_ghb2 E X); fold (bot_ghb1 E X) in Hres;
      apply bot_ghb_incl; auto.
  (*A1 : true true ; A2 : true false *)
 destruct_wk H12.
  unfold A1n.inter in Hinter1; unfold A2n.inter in Hinter2;
  rewrite Hinter1 in Hrfei; rewrite Hinter2 in Hrfei; inversion Hrfei.
  (*A1 : false true ; A2 : true false *)
 destruct_wk H12.
  unfold A1n.inter in Hinter1; unfold A2n.inter in Hinter2;
  rewrite Hinter1 in Hrfei; rewrite Hinter2 in Hrfei; inversion Hrfei.
  (*A1 : true false ; A2 : true false *)
  inversion Hxy as [Hrfi | Hr].
    left; left; auto.
      inversion Hr as [Ht | Hres].
      unfold A2nWmm.mrf; rewrite Hintra2 in Hi;
        rewrite Hinter2 in Hi; apply Hi; auto.
      right; fold (bot_ghb2 E X); fold (bot_ghb1 E X) in Hres;
      apply bot_ghb_incl; auto.
  (*A1 : false false ; A2 : true false *)
      inversion Hxy as [Ht | Hres].
      unfold A2nWmm.mrf; rewrite Hintra2 in Hi;
        rewrite Hinter2 in Hi; apply Hi; auto.
      right; fold (bot_ghb2 E X); fold (bot_ghb1 E X) in Hres;
      apply bot_ghb_incl; auto.
  (*A1 : true true ; A2 : false false *)
 destruct_wk H12.
  unfold A1n.inter in Hinter1; unfold A2n.inter in Hinter2;
  rewrite Hinter1 in Hrfei; rewrite Hinter2 in Hrfei; inversion Hrfei.
  (*A1 : false true ; A2 : false false *)
 destruct_wk H12.
  unfold A1n.inter in Hinter1; unfold A2n.inter in Hinter2;
  rewrite Hinter1 in Hrfei; rewrite Hinter2 in Hrfei; inversion Hrfei.
  (*A1 : true false ; A2 : false false *)
  destruct H12 as [? [Himpl ?]].
  unfold A1n.intra in Hintra1; unfold A2n.intra in Hintra2;
  rewrite Hintra1 in Himpl; rewrite Hintra2 in Himpl; inversion Himpl.
  (*A1 : false false ; A2 : false false*)
      inversion Hxy as [Ht | Hres].
      unfold A2nWmm.mrf; rewrite Hintra2 in Hi;
        rewrite Hinter2 in Hi; apply Hi; auto.
      right; fold (bot_ghb2 E X); fold (bot_ghb1 E X) in Hres;
      apply bot_ghb_incl; auto.
Qed.

Lemma ac2n_ac1 :
  forall E X,
  weaker -> rel_incl (A1.abc E X) (A2nWmm.ghb E X) ->
  acyclic (A2nWmm.ghb E X) ->
  acyclic (A1Wmm.ghb E X).
Proof.
intros E X Hwk Hi Hac2 x Hc1; unfold acyclic in Hac2; apply (Hac2 x).
generalize Hc1; apply tc_incl; apply ghb_incl'; auto.
Qed.

Hypothesis wk : weaker.
Hypothesis ab_wk : forall E X, rel_incl (A1.abc E X) (A2nWmm.ghb E X).

Lemma validity_decr :
  forall E X,
  well_formed_event_structure E ->
  A2nWmm.valid_execution E X ->
  A1Wmm.valid_execution E X.
Proof.
intros E X Hwf Hv; destruct_valid Hv;
  split; [|split; [|split; [|split]]]; auto.
  split; auto. split; auto.
  apply ac2n_ac1; auto.
  apply wk. apply ab_wk.
Qed.

End Preservation.

End Covering.
