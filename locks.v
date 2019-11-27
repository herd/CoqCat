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
From CoqCat Require Import sc.
From CoqCat Require Import valid.
From CoqCat Require Import covering.
From CoqCat Require Import drf.
Require Import Classical_Prop.
(*Require Import orders.*)
Import OEEvt.
Set Implicit Arguments.

Module Locks (A: Archi) (dp:Dp).

Axiom excluded_middle : forall (A:Prop), A \/ ~A.

Module ARes <: Archi.
Parameter ppo : Event_struct -> Rln Event.
Hypothesis ppo_valid : forall E, rel_incl (ppo E) (po_iico E).
Hypothesis ppo_fun :
  forall E s x y,
  ppo E x y /\ s x /\ s y <->
  ppo (mkes (Intersection Event (events E) s) (rrestrict (iico E) s)) x y.
Parameter inter : bool.
Parameter intra : bool.
Parameter abc : Event_struct -> Execution_witness -> Rln Event.
Hypothesis ab_evts : forall (E:Event_struct) (X:Execution_witness),
  forall x y, well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  abc E X x y -> In _ (events E) x /\ In _ (events E) y.
Hypothesis ab_incl :
  forall E X, rel_incl (abc E X) (tc (rel_union (hb E X) (po_iico E))).
Hypothesis ab_fun :
  forall E X s x y,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  (abc E X x y /\ s x /\ s y <->
  abc (mkes (Intersection Event (events E) s) (rrestrict (iico E) s))
    (mkew (rrestrict (ws X) s) (rrestrict (rf X) s)) x y).
Parameter stars : Event_struct -> set Event.
End ARes.
Import ARes.
(** locks *)
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

Module VA := Valid An dp.
Import VA. Import VA.ScAx.
Module Covering := Covering ARes An dp.
Import Covering.

Definition atom (E:Event_struct) (r w: Event) (l:Location): Prop :=
  reads E r /\ stars E r /\ loc r = l /\
  writes E w /\ stars E w /\ loc w = l /\ po_iico E r w /\
  ~(exists e, stars E e /\ po_iico E r e /\ po_iico E e w) /\
         (forall X, ~(exists w', proc_of w' <> proc_of r /\
                       writes E w' /\ loc w' = l /\ fr E X r w' /\ ws X w' w)). (*w' pas sur le meme proc*)

Ltac destruct_atom H :=
  destruct H as [Hr [Hatr [Hlr [Hw [Haw [Hlw [Hporw [Hnoc Hno]]]]]]]].

Definition taken (E:Event_struct) (l:Location) r : Prop :=
  (exists w, atom E r w l (*/\ value_of r = Some 0 /\ value_of w = Some 1*)).
Definition free (E:Event_struct) (l:Location) r w : Prop :=
  po_iico E r w /\ taken E l r /\ loc w = l (*/\ value_of w = Some 0*).

Definition ImportBarrier (E: Event_struct) (b: Event) : Prop :=
  forall X,
  (forall r e, reads E r -> stars E r -> po_iico E r b -> po_iico E b e -> abc E X r e) (*/\
  (forall r w rw, reads E r -> po_iico E r b -> po_iico E b w -> rf X w rw -> abc E X r rw)*).
Definition ExportBarrier (E: Event_struct) (b: Event) : Prop :=
  forall X,
  (forall e w r, stars E r ->
    po_iico E e b -> po_iico E b w -> rf X w r -> abc E X e r) (*/\
  (forall e1 e2, po_iico E e1 b -> po_iico E b e2 -> ~(writes E e1 /\ reads E e2) -> abc E X e1 e2)*).

Definition Lock (E:Event_struct) (l:Location) (r c:Event) : Prop :=
  taken E l r /\ ImportBarrier E c /\ po_iico E r c.
Definition Unlock (E:Event_struct) (l:Location) r (b w:Event) : Prop :=
  free E l r w /\ ExportBarrier E b /\ po_iico E b w.

Record Cs' : Type := mkcs
{Read: Event ;
  Ib: Event ;
  Eb: Event;
  Write: Event;
  Evts: set Event}.
Definition Cs := Cs'.
Definition cs (E:Event_struct) (l:Location) crit :=
  Lock E l crit.(Read) crit.(Ib) /\
  (forall e, crit.(Evts) e <-> po_iico E crit.(Ib) e /\ po_iico E e crit.(Eb)) /\
  Unlock E l crit.(Read) crit.(Eb) crit.(Write) /\
  po_iico E crit.(Ib) crit.(Eb).
Definition evts (cs:Cs) := Evts cs.
Definition sc E l :=
  fun s1 => fun s2 => cs E l s1 /\ cs E l s2 /\ s1 <> s2.
Definition s E (X:Execution_witness) :=
  fun e1 => fun e2 => exists l, exists s1, exists s2, sc E l s1 s2 /\ evts s1 e1 /\ evts s2 e2.
Definition css E X l :=
   fun s1 => fun s2 => sc E l s1 s2 /\
    (rf X) s1.(Write) s2.(Read).
Ltac destruct_css H :=
  destruct H as [[Hcs1 [Hcs2 Hdcs]] Hrf].
Definition css_lift E X l :=
  fun e1 => fun e2 => exists s1, exists s2,
    css E X l s1 s2 /\ (Evts s1) e1 /\ (Evts s2) e2.
Ltac destruct_csslift H :=
  destruct H as [s1 [s2 [Hcss [Hev1 Hev2]]]].
Inductive lockc' E X l : Event -> Event -> Prop :=
  | RF : forall e1 e2, css_lift E X l e1 e2 -> lockc' E X l e1 e2
  | Trans :
    forall e1 e e2,
    lockc' E X l e1 e -> lockc' E X l e e2 -> lockc' E X l e1 e2.
Definition lockc E X l := lockc' E X l.
Definition lock E X := fun e1 => fun e2 => exists l, lockc E X l e1 e2.

Parameter inite : Location -> Event.
Axiom init_evt : forall E l, events E (inite l).
Axiom init_store : forall l, write_to (inite l) l.
Axiom init_ws : forall X l, ~(exists e, ws X e (inite l)).
Axiom init_cs : forall E l cr, cs E l cr /\ Write cr = inite l -> Evts cr (inite l).

Module DaRaFr := DataRaceFree ARes A dp.
Import DaRaFr.
Module HB : HappensBefore.
Module AResDrf := DataRaceFree ARes A dp.
Import AResDrf.
Module AResBasic := Basic ARes dp.
Import AResBasic.
Module AResWmm := Wmm ARes dp.
Import AResWmm.
Import ARes.

Definition sync := s.
Definition happens_before E X :=
  tc (rel_union (po_iico E) (sync E X)).
Hypothesis happens_before_compat_com :
  forall E X x y, hb E X x y -> ~(happens_before E X y x).
Definition competing E (X:Execution_witness) :=
  fun e1 => fun e2 => events E e1 /\ events E e2 /\
    loc e1 = loc e2 /\ proc_of e1 <> proc_of e2 /\
    (writes E e1 \/ writes E e2).
Definition cns E X :=
  fun e1 => fun e2 => competing E X e1 e2 /\
  ~ (happens_before E X e1 e2 \/ happens_before E X e2 e1).

Definition convoluted_wf :=
  forall E X Y x y,
  competing E X x y ->
  ~ (happens_before E X x y \/ happens_before E X y x) ->
  rf Y = so_rfm E
         (LE (tc (rel_union (rel_union (rel_inter (cns E X) (pair x y)) (A.ppo E)) (pio_llh E)))) ->
  ws Y = so_ws
         (LE (tc (rel_union (rel_union (rel_inter (cns E X) (pair x y)) (A.ppo E)) (pio_llh E)))) ->
  competing E Y x y /\ ~ (happens_before E Y x y \/ happens_before E Y y x).
Lemma compete_in_events :
  forall E X x y,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  competing E X x y ->
  events E x /\ events E y.
Proof.
intros E X x y Hwf Hrfwf [Hex [Hey ?]]; split; auto.
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
generalize (compete_in_events Hwf Hwfrf Hc); intros [Hex Hey].
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
  AWmm.valid_execution E X ->
  ~ (exists z, competing E X z z).
Proof.
intros E X Hwf Hv [z [? [? [? [Hdp ?]]]]].
apply Hdp; trivial.
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
    apply (competing_irr Hwf Hv1 Hc).
Qed.
Lemma competing_not_po :
  forall E X x y,
  well_formed_event_structure E ->
    AWmm.valid_execution E X ->
  competing E X x y -> ~ (po_iico E y x).
Proof.
intros E X x y Hwf Hv [? [? [? [Hdp ?]]]] Hpo.
assert (In _ (events E) x) as Hx.
  apply AResBasic.po_iico_range_in_events with y; auto.
assert (In _ (events E) y) as Hy.
  apply AResBasic.po_iico_domain_in_events with x; auto.
generalize (AResBasic.po_implies_same_proc Hwf Hy Hx Hpo); intro Heq;
subst; auto.
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
  generalize (competing_not_po Hwf Hv1 Hc); intro; contradiction.
Qed.

Lemma competing_ac_ppo2 :
  forall E X x y,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  competing E X x y ->
  (forall z, ~ tc (rel_union (rel_union (rel_inter (cns E X) (pair x y)) (A.ppo E)) (pio_llh E)) z z).
Proof.
intros E X x y Hwf Hv Hc z Hz.
generalize (u_in_pair_po Hz); intro Hu.
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
    apply (pair_irr Hwf Hv Hco).
assert (trans (rel_inter (cns E X) (pair x y))) as Ht2.
  unfold trans; intros e1 e2 e3 H12 H23.
  destruct H12 as [? [? Hy]];
  destruct H23 as [[Hco ?] [Hx Hy2]].
  rewrite Hx in Hco; rewrite Hy2 in Hco.
  rewrite <- Hx in Hco; rewrite <- Hy in Hco.
  assert (exists z, competing E X z z) as Hcon.
    exists e2; auto.
  generalize (competing_irr Hwf Hv Hcon); intro Ht; inversion Ht.
assert (trans (po_iico E)) as Ht1.
  intros e1 e2 e3 H12 H23; apply A2Basic.po_trans with e2; auto.
generalize (union_cycle_implies_seq_cycle2 Hi1 Hi2 Hiu Ht2 Ht1 Hu);
  intros [e Htc].
generalize (tc_pair_po_in_pair_po Hwf Hv Htc); intro He.
destruct He as [e' [[[Hee' ?] ?] He'e]].
generalize (competing_not_po Hwf Hv Hee'); intro; contradiction.
Qed.

Lemma convoluted_wf_implies_wf :
  convoluted_wf ->
  (forall E X x y,
  well_formed_event_structure E ->
  AResWmm.valid_execution E X ->
  competing E X x y ->
  ~ (happens_before E X x y \/ happens_before E X y x) ->
  (exists Y, AnWmm.valid_execution E Y /\
  competing E Y x y /\ ~ (happens_before E Y x y \/ happens_before E Y y x))).
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
Qed.

Lemma convoluted_wf_holds :
  convoluted_wf.
Proof.
intros E X Y x y Hcxy Hnxy Hrf Hwf.
split; [apply Hcxy |apply Hnxy].
Qed.

Lemma hb_stable :
 (* forall E X x y,
  well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  competing E X x y ->
  ~ (happens_before E X x y \/ happens_before E X y x) ->
  (exists Y, A2nWmm.valid_execution E Y /\
  competing E Y x y /\ ~ (happens_before E Y x y \/ happens_before E Y y x)).*)

  forall E X x y,
  well_formed_event_structure E ->
  valid_execution E X ->
  competing E X x y ->
  ~ (happens_before E X x y \/ happens_before E X y x) ->
  (exists Y, AnWmm.valid_execution E Y /\
  competing E Y x y /\ ~ (happens_before E Y x y \/ happens_before E Y y x)).
Proof.
intros E X x y Hwf HX Hcxy Hnxy.
apply convoluted_wf_implies_wf with X; auto.
unfold convoluted_wf; apply convoluted_wf_holds.
Qed.

(*Import OEEvt.*)

(** DRF progs have SC sem *)

Lemma in_lockc_rf_case_implies_in_ab :
  forall E X l e1 e2,
    well_formed_event_structure E ->
    valid_execution E X ->
    css_lift E X l e1 e2 ->
    tc (abc E X) e1 e2.
Proof.
intros E X l e1 e2 Hwf Hv Hcsslift.
destruct_csslift Hcsslift.
  destruct_css Hcss.
destruct Hcs1 as [HL1 [Hee1 [HUL1 Hib1]]].
  destruct HUL1 as [Hur1 [Heb1 Hpobw1]].
destruct Hcs2 as [[Hres2 [Hib2 Hporc2]] [Hee2 HUL2]].
apply trc_ind with (Read s2); auto; apply trc_step; auto.

  (*destruct (Heb1 X) as [Hcumul Hbase].*) generalize (Heb1 X); intro Hcumul.
  apply (Hcumul e1 (Write s1) (Read s2)).
  destruct Hres2 as [? (*[*)Hat2 (*?]*)]; destruct_atom Hat2; auto.
  destruct (Hee1 e1) as [Hee1d Hee1b].
  subst; destruct (Hee1d Hev1); auto.
  auto.
  auto.

  (*destruct (Hib2 X) as [Hbase Hcumul]*)
  generalize (Hib2 X); intro Hbase.
  apply (Hbase (Read s2) e2); auto.
    split; destruct_valid Hv;
      [apply ran_rf_in_events with X (Write s1) |
       apply ran_rf_is_read with E X (Write s1)]; auto; split; auto.
  destruct Hres2 as [? (*[*)Hat2 (*?]*)]; destruct_atom Hat2; auto.
  destruct (Hee2 e2) as [Hee2d Hee2b].
  subst; destruct (Hee2d Hev2); auto.
Qed.

Lemma in_lockc_implies_in_ab :
  forall E X l e1 e2,
    well_formed_event_structure E ->
    valid_execution E X ->
    lockc E X l e1 e2 ->
    tc (abc E X) e1 e2.
Proof.
intros E X l e1 e2 Hwf Hv H12.
induction H12.
  apply (in_lockc_rf_case_implies_in_ab Hwf Hv H).
  apply trc_ind with e; auto.
Qed.

Lemma lockc_u_ghb_in_ghb :
  forall E X l,
    well_formed_event_structure E ->
    valid_execution E X ->
    rel_incl (tc (rel_union (lockc E X l) (ghb E X))) (tc (ghb E X)).
Proof.
intros E X l Hwf Hv x y H.
induction H as [x y Hxy |].
inversion Hxy.

  assert (rel_incl (abc E X) (ghb E X)) as Hi.
    apply ab_in_ghb; auto.
  apply (tc_incl Hi).
  apply in_lockc_implies_in_ab with l; auto.

  apply trc_step; auto.

apply trc_ind with z; auto.
Qed.

Lemma lockc_ghb : forall E X l,
    well_formed_event_structure E ->
    valid_execution E X ->
    acyclic (rel_union (lockc E X l) (ghb E X)).
Proof.
intros E X l Hwf Hv x Hx.
generalize (lockc_u_ghb_in_ghb Hwf Hv Hx); intro Hcy.
destruct_valid Hv; apply (Hvalid x Hcy).
Qed.

Lemma lockc_irrefl :
  forall E X l,
  well_formed_event_structure E ->
  valid_execution E X ->
  ~(exists x, lockc E X l x x).
Proof.
intros E X l Hwf Hv [x Hx].
generalize (in_lockc_implies_in_ab Hwf Hv Hx); intro Hc.
destruct_valid Hv; unfold acyclic in Hvalid; apply (Hvalid x).
assert (rel_incl (abc E X) (ghb E X)) as Hi.
  intros e1 e2; apply ab_in_ghb; auto.
apply (tc_incl Hi Hc).
Qed.
Lemma lock_irrefl :
  forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
  ~(exists x, lock E X x x).
Proof.
intros E X Hwf Hv [x [l Hx]].
generalize (in_lockc_implies_in_ab Hwf Hv Hx); intro Hc.
destruct_valid Hv; unfold acyclic in Hvalid; apply (Hvalid x).
assert (rel_incl (abc E X) (ghb E X)) as Hi.
  intros e1 e2; apply ab_in_ghb; auto.
apply (tc_incl Hi Hc).
Qed.

Lemma po_irrefl :
  forall E, well_formed_event_structure E ->
  ~(exists x, po_iico E x x).
Proof.
intros E Hwf [x Hx]. apply (po_ac Hwf Hx).
Qed.
Lemma lockc_po_irrefl :
  forall E X l,
  well_formed_event_structure E ->
  valid_execution E X ->
  ~(exists x, (rel_union (po_iico E) (lockc E X l)) x x).
Proof.
intros E X l Hwf Hv [x Hx]; inversion Hx.
  assert (exists x, po_iico E x x) as He.
    exists x; auto.
  apply (po_irrefl Hwf He); auto.
  assert (exists x, lockc E X l x x) as He.
    exists x; auto.
  apply (lockc_irrefl Hwf Hv He).
Qed.
Lemma lock_po_irrefl :
  forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
  ~(exists x, (rel_union (po_iico E) (lock E X)) x x).
Proof.
intros E X Hwf Hv [x Hx]; inversion Hx.
  assert (exists x, po_iico E x x) as He.
    exists x; auto.
  apply (po_irrefl Hwf He); auto.
  assert (exists x, lock E X x x) as He.
    exists x; auto.
  apply (lock_irrefl Hwf Hv He).
Qed.
Lemma lockc_trans :
  forall E X l,
  well_formed_event_structure E ->
  valid_execution E X ->
  trans (lockc E X l).
Proof.
intros E X l Hwf Hv x y z Hxy Hyz.
unfold lockc in * |- *;
apply Trans with y; auto.
Qed.
Lemma po_trans :
  forall E, well_formed_event_structure E ->
  trans (po_iico E).
Proof.
  intros E Hwf x y z Hxy Hyz. apply po_trans with y; auto.
Qed.

Lemma lockc_rf_implies_in_ab_with_lwarx :
 forall E X l e1 s1 s2,
    well_formed_event_structure E ->
    valid_execution E X ->
    Evts s1 e1 ->
    css E X l s1 s2 ->
    tc (abc E X) e1 (Read s2).
Proof.
intros E X l e1 s1 s2 Hwf Hv Hev1 Hcss.
destruct_css Hcss.
destruct Hcs1 as [HL1 [Hee1 [HUL1 Hib1]]].
destruct HUL1 as [Hur1 [Heb1 Hpobw1]].
destruct Hcs2 as [[Hres2 [Hib2 Hporc2]] [Hee2 HUL2]].
apply trc_step; auto.

  (*destruct (Heb1 X) as [Hcumul Hbase].*) generalize (Heb1 X); intro Hcumul.
  apply (Hcumul e1 (Write s1) (Read s2)).
  destruct Hres2 as [? (*[*)Hat2 (*?]*)]; destruct_atom Hat2; auto.
  destruct (Hee1 e1) as [Hee1d Hee1b].
  subst;
  destruct (Hee1d Hev1); auto.
  auto.
  auto.
Qed.

Lemma lockc_seq_po_in_ab :
  forall E X l x y z,
  well_formed_event_structure E ->
  valid_execution E X ->
  lockc E X l x y -> po_iico E y z -> tc (abc E X) x z.
Proof.
intros E X l x y z Hwf Hv Hxy Hyz.
induction Hxy.
  destruct_csslift H.
  destruct_css Hcss.
  assert (po_iico E (Eb s2) z \/ po_iico E z (Eb s2)) as Hor.
    apply same_proc_implies_po; auto.
    assert (In _ (events E) e2) as Hee2.
      apply po_iico_domain_in_events with z; auto.
    assert (In _ (events E) z) as Hez.
      apply po_iico_range_in_events with e2; auto.
    rewrite <- (po_implies_same_proc Hwf Hee2 Hez Hyz).
    destruct Hcs2 as  [HL2 [Heve2 [HUL2 Hib2]]].
    destruct HUL2 as [Hur2 [Heb2 Hpobw2]].
    generalize (Heve2 e2); intros [Hd Hb].
    subst; destruct (Hd Hev2) as [Hpoce2 Hpobe2].
    assert (In _ (events E) (Eb s2)) as Heeb2.
      apply po_iico_range_in_events with e2; auto.
    rewrite <- (po_implies_same_proc Hwf Hee2 Heeb2 Hpobe2); trivial.
    destruct Hcs2 as  [HL2 [Heve2 [HUL2 Hib2]]].
    destruct HUL2 as [Hur2 [Heb2 Hpobw2]].
    generalize (Heve2 e2); intros [Hd Hb].
    subst; destruct (Hd Hev2) as [Hpoce2 Hpobe2].
      apply po_iico_range_in_events with e2; auto.
      apply po_iico_range_in_events with e2; auto.

  inversion Hor as [Haf | Hbef].

    apply trc_ind with (Read s2).
    apply lockc_rf_implies_in_ab_with_lwarx
      with l s1; auto.
     split; auto.
     split; auto.
(*    destruct Hcs2 as [HL2 [Hee2 [Hur2 [Heb2 Hpobw2]]]].

    apply trc_step; destruct (Heb2 X) as [Hcumul Hbase];
      apply (Hbase (Read s2) z); auto.
      destruct (Hee2 e2) as [Hee2d Hee2b].
      apply po_trans with (Ib s2); auto.
      destruct HL2 as [? [? Hrc2]]; auto.
      apply po_trans with e2; auto.
        destruct (Hee2d Hev2); auto.
        destruct (Hee2d Hev2); auto.
      destruct_valid Hv; generalize (ran_rf_is_read E X (Write s1) (Read s2) Hrf_cands Hrf);
      intros [lr [vr Har]] [[? [lr' [vr' Hwr]]] ?].
      rewrite Hwr in Har; inversion Har. *)
      destruct Hcs2 as [[Htk2 [Hib2 Hporb]] [? HUL2]].
      destruct Htk2 as [? (*[*)Hat2 (*?]*)]; destruct_atom Hat2.
      apply trc_step; apply (Hib2 X); auto.
      apply po_trans with (Eb s2); auto.
      destruct HUL2 as [? ?]; auto.

    apply in_lockc_rf_case_implies_in_ab
      with l; auto.
     exists s1; exists s2.
     split; auto.
      split; auto.
    split; auto.
    split; auto.
    destruct Hcs2 as [HL2 [Hee2 [HUL2 Hieb2]]].
    destruct HUL2 as [Hur2 [Heb2 Hpobw2]].
    destruct (Hee2 z) as [? Hee2b].
    apply Hee2b; split; auto.
    apply po_trans with e2; auto.
    destruct (Hee2 e2) as [Hee2d ?].
    destruct (Hee2d Hev2); auto.

  apply trc_ind with e.
    apply in_lockc_implies_in_ab with l; auto.
  apply (IHHxy2 Hyz).
(*x in cs1 y in cs2 and y -po-> z
   thus x -ab-> r2 by Bcumul of b1
   and r2 -ab-> z by commit rule or lwsync base*)
Qed.

Lemma lockc_seq_po_ghb :
  forall E X l x y,
  well_formed_event_structure E ->
  valid_execution E X ->
  tc (rel_seq (lockc E X l) (po_iico E)) x y ->
  tc (ghb E X) x y.
Proof.
intros E X l x y Hwf Hv Hxy.
induction Hxy as [x y Hs |].

  destruct Hs as [z [Hxz Hzy]].
    generalize (lockc_seq_po_in_ab Hwf Hv Hxz Hzy); apply tc_incl.
      apply ab_in_ghb; auto.

  apply trc_ind with z; auto.
Qed.

Lemma lockc_in_ghb :
  forall E X l x y,
  well_formed_event_structure E ->
  valid_execution E X ->
  lockc E X l x y ->
  tc (ghb E X) x y.
Proof.
intros E X l x y Hwf Hv Hxy.
induction Hxy.
 destruct_csslift H. destruct_css Hcss.

  apply trc_ind with (Read s2).
    assert (rel_incl (abc E X) (ghb E X)) as Hincl.
      intros x y Hxy; apply ab_in_ghb; auto.
    apply (tc_incl Hincl).

    apply lockc_rf_implies_in_ab_with_lwarx
      with l s1; auto.
     split; auto. split; auto.

     destruct Hcs2 as [[Hres2 [Hib2 Hporc2]] [Hee2 HUL2]].

        assert (rel_incl (abc E X) (ghb E X)) as Hincl.
      intros x y Hxy; apply ab_in_ghb; auto.
    apply (tc_incl Hincl). apply trc_step.
    (*destruct (Hib2 X) as [Hbase Hcumul].*)
      generalize (Hib2 X); intro Hbase.
      apply (Hbase (Read s2) e2); auto.

      destruct_valid Hv; split.

      apply (ran_rf_in_events X (Write s1) (Read s2) Hwf). split; auto. auto.
      generalize (ran_rf_is_read E X (Write s1) (Read s2) Hrf_cands Hrf); intros [lr (*[vr*) Har(*]*)].
      exists lr; (*exists vr;*) auto.
      destruct Hres2 as [? (*[*)Hat2 (*?]*)]; destruct_atom Hat2; auto.
      destruct (Hee2 e2) as [Hee2d Hee2b].
      destruct (Hee2d Hev2); auto.

    apply trc_ind with e; auto.
Qed.
Lemma lock_in_ghb :
  forall E X x y,
  well_formed_event_structure E ->
  valid_execution E X ->
  lock E X x y ->
  tc (ghb E X) x y.
Proof.
intros E X x y Hwf Hv Hxy.
destruct Hxy as [l Hxy]; apply lockc_in_ghb with l; auto.
Qed.
Lemma tclock_in_ghb :
  forall E X x y,
  well_formed_event_structure E ->
  valid_execution E X ->
  tc (lock E X) x y ->
  tc (ghb E X) x y.
Proof.
intros E X x y Hwf Hv Hxy.
induction Hxy.
  apply lock_in_ghb; auto.
  apply trc_ind with z; auto.
Qed.

Lemma lock_seq_po_ghb :
  forall E X x y,
  well_formed_event_structure E ->
  valid_execution E X ->
  tc (rel_seq (tc (lock E X)) (maybe (po_iico E))) x y ->
  tc (ghb E X) x y.
Proof.
intros E X x y Hwf Hv Hxy.
induction Hxy as [x y Hs |].

  destruct Hs as [z [Htc_xz Hor_zy]].
  induction Htc_xz as [x z Hxz |].

  destruct Hxz as [l Hxz].
   inversion Hor_zy as [Hzy | Heq].
    generalize (lockc_seq_po_in_ab Hwf Hv Hxz Hzy); apply tc_incl.
      apply ab_in_ghb; auto.


    subst; apply lockc_in_ghb with l; auto.

  apply trc_ind with z.
    apply tclock_in_ghb; auto.
    apply (IHHtc_xz2 Hor_zy).

  apply trc_ind with z; auto.
Qed.

Lemma lockc_po : forall E X l,
  well_formed_event_structure E ->
  valid_execution E X ->
  acyclic (rel_union (lockc E X l) (po_iico E)).
Proof.
intros E X l Hwf Hv x Hx.
rewrite union_triv in Hx.
generalize (lockc_irrefl); intro Hlir.
generalize (po_irrefl); intro Hpoir.
generalize (lockc_po_irrefl); intro Hlpoir.
generalize (lockc_trans); intro Hlt.
generalize (po_trans); intro Hpot.
generalize (union_cycle_implies_seq_cycle2 (Hpoir E Hwf) (Hlir E X l Hwf Hv) (Hlpoir E X l Hwf Hv) (Hlt E X l Hwf Hv)  (Hpot E Hwf) Hx);
intros [y Hy].
generalize (lockc_seq_po_ghb Hwf Hv Hy); intro Hc.
destruct_valid Hv; unfold acyclic in Hvalid; unfold not in Hvalid; apply (Hvalid y Hc).
Qed.

Lemma lock_pop : forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
  acyclic (rel_union (lock E X) (po_iico E)).
Proof.
intros E X Hwf Hv x Hx.
rewrite union_triv in Hx.
generalize (lock_irrefl); intro Hlir.
generalize (po_irrefl); intro Hpoir.
generalize (lock_po_irrefl); intro Hlpoir.
generalize (po_trans); intro Hpot.
generalize (union_cycle_implies_seq_cycle3 (Hpoir E Hwf) (Hlir E X Hwf Hv) (Hlpoir E X Hwf Hv) (Hpot E Hwf) Hx);
intros [y Hy].
generalize (lock_seq_po_ghb Hwf Hv Hy); intro Hc.
destruct_valid Hv; unfold acyclic in Hvalid; unfold not in Hvalid; apply (Hvalid y Hc).
Qed.

Lemma rf_irrefl :
  forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
  ~(exists x, rf X x x).
Proof.
intros E X Hwf Hv [x Hx].
destruct_valid Hv.
generalize (dom_rf_is_write E X x x Hrf_cands Hx); intros [l [v Hwx]].
generalize (ran_rf_is_read E X x x Hrf_cands Hx); intros [l' [v' Hrx]].
rewrite Hrx in Hwx; inversion Hwx.
Qed.
Lemma lockc_rf_irrefl :
  forall E X l,
  well_formed_event_structure E ->
  valid_execution E X ->
  ~(exists x, (rel_union (rf X) (lockc E X l)) x x).
Proof.
intros E X l Hwf Hv [x Hx]; inversion Hx.
  assert (exists x, rf X x x) as He.
    exists x; auto.
  apply (rf_irrefl Hwf Hv He); auto.
  assert (exists x, lockc E X l x x) as He.
    exists x; auto.
  apply (lockc_irrefl Hwf Hv He).
Qed.
Lemma rf_trans :
  forall E X, well_formed_event_structure E ->
  valid_execution E X ->
  trans (rf X).
Proof.
  intros E X Hwf Hv x y z Hxy Hyz.
  destruct_valid Hv.
  generalize (dom_rf_is_write E X y z Hrf_cands Hyz); intros [l [v Hwy]].
  generalize (ran_rf_is_read E X x y Hrf_cands Hxy); intros [l' [v' Hry]].
  rewrite Hry in Hwy; inversion Hwy.
Qed.

Axiom unic_css :
  forall E l e,
    forall cs1 cs2,
    cs E l cs1 ->
    cs E l cs2 ->
    Evts cs1 e -> Evts cs2 e ->
    cs1 = cs2.
Axiom cs_wf : forall E l c, cs E l c ->
  (forall X, ~(exists w, fr E X (Read c) w /\ ws X w (Write c))).
Axiom cs_fr : (*provable from uniproc equivs*)
  forall E X l c, cs E l c -> fr E X (Read c) (Write c).
Axiom diff_cs : forall E X l1 l2 c1 c2, cs E l1 c1 -> cs E l2 c2 ->
  rf X (Write c1) (Read c2) -> c1 <> c2.
Axiom cs_diff : forall E cs1 cs2, cs1 <> cs2 ->
  (forall e1 e2, Evts cs1 e1 -> Evts cs2 e2 -> e1 <> e2) /\
  (forall l ws1 ws2, atom E (Read cs1) ws1 l -> atom E (Read cs2) ws2 l -> ws1 <> ws2).
Axiom no_other_stores : forall E l w, write_to w l -> (exists crit, cs E l crit /\ (Write crit) = w /\ exists e, Evts crit e).

Set Implicit Arguments.
Inductive nsteps (A:Set) (r:Rln A) : nat -> A -> A -> Prop :=
 (* | rtriv : forall x y, x = y -> nsteps r 0 x y *)
  | rintro : forall x y, r x y -> ~(exists z, r x z /\ r z y) -> nsteps r 1 x y
  | rtrans : forall x y z n, r x y -> nsteps r n y z -> nsteps r (S n) x z.
Lemma n1_is_r : forall A r x y,
  @nsteps A r 1 x y -> r x y.
Proof.
intros A r x y H1.
inversion H1; auto.
inversion H2.
Qed.
Definition discrete (A:Set) (r:Rln A) := forall x y, r x y -> exists n, nsteps r n x y. (*has a meaning only if r irrefl*)
Definition decr (A:Set) (r:Rln A) := forall x y n, nsteps r (S n) x y -> exists z, nsteps r 1 x z /\ nsteps r n z y.
Unset Implicit Arguments.
Axiom dis_ws : forall X, discrete (ws X).
Axiom dec_ws : forall X, decr (ws X).
Definition pio_cs E := fun e1 => fun e2 => exists l, exists cr, cs E l cr /\ e1 = Read cr /\ e2 = Write cr /\ (exists e, Evts cr e).
Axiom dec_rfpio : forall E X, decr (rel_seq (rf X) (pio_cs E)).

Lemma nws_implies_write :
  forall X n w1 w2,
  nsteps (ws X) n w1 w2 ->
  exists l, write_to w2 l.
Proof.
intros X n.
induction n; intros w1 w2 H12.
  inversion H12.
  generalize (dec_ws X); intro Hd.
  generalize (Hd w1 w2 n H12); intros [w [H1w Hw2]].
  apply (IHn w w2 Hw2).
Qed.

Lemma nsteps_implies_nrfpio :
  forall E X n,
  well_formed_event_structure E ->
  valid_execution E X ->
  forall w1 w2,
  nsteps (ws X) n w1 w2 ->
  nsteps (rel_seq (rf X) (pio_cs E)) n w1 w2 (*\/ exists w, ws X w w1*).
Proof.
intros E X n Hwf Hv.
induction n.

  intros w1 w2 H0.
  inversion H0.

  intros w1 w2 Hsn.
  generalize (dec_ws X); intro Hde.
  generalize (Hde w1 w2 n Hsn); intros [z [H1z Hz2]].

  generalize (IHn z w2 Hz2); intro Htc (* Hor.
    inversion Hor as [Htc | Hws]*).

    assert (exists l, write_to z l) as Hwz.
      apply nws_implies_write with X 1 w1; auto.
    destruct Hwz as [l Hwz].
    generalize (no_other_stores E Hwz); intros [cz [Hcz [Hwwz ?]]].
    assert (In _ (reads E) (Read cz)) as Hercz.
      destruct Hcz as [Hlcz ?]; destruct Hlcz as [Htk ?];
        destruct Htk as [w [[Hez ?] ?]]; split; auto.
    destruct_valid Hv; generalize (Hrf_init (Read cz) Hercz);
    intros [wrcz [Horcz Hrfcz]].
 (*inversion Horcz as [Hecz | Hicz].*)
    destruct (eqEv_dec w1 wrcz) as [Heq | Hneq].
        (*left.*) apply rtrans with z; auto.
        exists (Read cz); split.
          subst; auto.
          unfold pio_cs; exists l; exists cz; split; auto; split; auto.

        assert (ws X w1 wrcz \/ ws X wrcz w1) as Horw.
          assert (In Event (writes_to_same_loc_l (events E) l) w1) as Hww1.
            split.
              inversion H1z.
                apply dom_ws_in_events with X z; auto.
                split; auto.
                inversion H2.
              inversion H1z.
                assert (write_serialization_well_formed (events E) (ws X)) as Hwswf.
                  split; auto.
                generalize (dom_ws_is_write E X w1 z Hwswf H0); intros [l1 [v1 Hww1]].
                assert (write_serialization_well_formed (events E) (ws X) /\
                             rfmaps_well_formed E (events E) (rf X)) as Hs.
                  split; split; auto.
                generalize (ws_implies_same_loc X w1 z Hs H0); intro Heql.
                destruct Hwz as [? Hwz]; unfold loc in Heql; rewrite Hwz in Heql; rewrite Hww1 in Heql.
                subst; exists v1; auto.
                inversion H2.
          assert (In Event (writes_to_same_loc_l (events E) l) wrcz) as Hwwrcz.
            generalize (Hrf_cands wrcz (Read cz) Hrfcz); intros [? [? [lz [Hwzw ?]]]]; auto.
            split; auto.
  destruct Hcz as [HLz ?]; destruct HLz as [Htkz ?]; destruct Htkz as [xz (*[*)Hatz (*?]*)].
(*  destruct Hatz as [? [? [Hlz ?]]]. *)
    destruct Hatz as [? [? Hlz]].
  destruct H2 as [[? ?] ?]; unfold loc in Hlz; rewrite H2 in Hlz; inversion Hlz; subst; auto.
          apply ws_tot with E l; auto.
        inversion Horw.
          (*then wrcz in between w1 and z, contrad H1z*)
          inversion H1z.
            rewrite <- H4 in H1; rewrite <- H5 in H1;
            rewrite <- H4 in H2; rewrite <- H5 in H2;
            assert (exists z, ws X x z /\ ws X z y) as Hc.
              exists wrcz; split; auto.
                rewrite H4; auto.
                rewrite H5.
                  assert (fr E X (Read cz) z) as Hfr.
                    rewrite <- Hwwz.
          apply cs_fr with l; auto.
                  destruct Hfr as [? [? [w [Hrf Hws]]]].
                  generalize (Hrf_uni (Read cz) w wrcz Hrf Hrfcz); intro Heq; rewrite <- Heq; auto.
                  contradiction.
                 inversion H3.
          (*right; exists wrcz; auto.*)
          assert (fr E X (Read cz) w1) as Hfr.
            split.
              apply ran_rf_in_events with X wrcz; auto.
               split; auto.
              split.
                apply ran_ws_in_events with X wrcz; auto.
                split; auto.
                exists wrcz; split; auto.
           generalize (cs_wf Hcz); intro HnoX; generalize (HnoX X); intro Hno.
           assert (exists w : Event, fr E X (Read cz) w /\ ws X w (Write cz)) as Hc.
             exists w1; split; auto.
           rewrite Hwwz; inversion H1z; auto.
           inversion H3.
           contradiction.
Qed.

Lemma wsrf_implies_rfpio :
  forall E X l cr1 cr2,
  well_formed_event_structure E ->
  valid_execution E X ->
  cs E l cr1 -> cs E l cr2 ->
  (rel_seq (ws X) (rf X)) (Write cr1) (Read cr2) ->
  (exists n, rel_seq (nsteps (rel_seq (rf X) (pio_cs E)) n) (rf X) (Write cr1) (Read cr2)) (*\/
    exists w, ws X w (Write cr1)*).
Proof.
intros E X l cr1 cr2 Hwf Hv Hcs1 Hcs2 [wr2 [Hws12 Hrf2]].
generalize (dis_ws X); intro Hd.
generalize (Hd (Write cr1) wr2 Hws12); intros [n Hn].
generalize (nsteps_implies_nrfpio E X n Hwf Hv (Write cr1) wr2 Hn); intro Htc (*Hor.
inversion Hor as [Htc | Hws]*).
 (* left;*) exists n; exists wr2; split; auto.
 (* right; auto. *)
Qed.

Lemma nrfpio_implies_lock :
  forall E X l n,
  well_formed_event_structure E ->
  valid_execution E X ->
  forall cr1 cr2, cs E l cr1 -> cs E l cr2 ->
  nsteps (rel_seq (rf X) (pio_cs E)) n (Write cr1) (Write cr2) ->
  forall e1 e2, Evts cr1 e1 -> Evts cr2 e2 -> lockc' E X l e1 e2.
Proof.
intros E X l n Hwf Hv.
induction n; intros cr1 cr2 Hcs1 Hcs2 H12 e1 e2 He1 He2.
  inversion H12.
    generalize (dec_rfpio E X); intro Hde.
    generalize (Hde (Write cr1) (Write cr2) n H12); intros [z [H1z Hz2]].
        generalize (n1_is_r H1z); intros [r [Hrf [lz [cz [Hcsz [Hrcz [Hwcz [e He]]]]]]]].
       assert (l = lz) as Heql.
        assert (l = loc (Write cr1)) as Hl.
          destruct Hcs1 as [? [? HUL1]]; destruct HUL1 as [Hfr1 ?].
          destruct Hfr1 as [Hfr1 ?]; destruct Hfr1 as [? [? (*[*)Hl1 (*?]*)]].
          rewrite Hl1; auto.
        assert (lz = loc r) as Hlz.
          destruct Hcsz as [HLz ?]; destruct HLz as [Htkz ?]; destruct Htkz as [xz (*[*)Hatz (*?]*)];
          destruct Hatz as [? [? [Hlz ?]]]. rewrite Hrcz; rewrite Hlz; auto.

        rewrite Hl; rewrite Hlz.
        apply rf_implies_same_loc2 with E X; auto.
          split; split; destruct_valid Hv; auto.
    apply Trans with e.

      apply RF; unfold css_lift; exists cr1; exists cz; split; [unfold css| split; auto].
      split; auto. split; auto. split; auto.
        subst; auto.
        apply diff_cs with E X l lz; auto.
        rewrite <- Hrcz; auto.
        subst; auto.

      rewrite <- Heql in Hcsz; rewrite Hwcz in Hz2; apply (IHn cz cr2 Hcsz Hcs2 Hz2 e e2 He He2).
Qed.

Lemma nrfpio_rf_implies_lock :
  forall E X l cr1 cr2 n,
  well_formed_event_structure E ->
  valid_execution E X ->
  cs E l cr1 -> cs E l cr2 ->
  rel_seq (nsteps (rel_seq (rf X) (pio_cs E)) n) (rf X) (Write cr1) (Read cr2) ->
  forall e1 e2, Evts cr1 e1 -> Evts cr2 e2 -> lockc E X l e1 e2.
Proof.
intros E X l cr1 cr2 n Hwf Hv Hcs1 Hcs2 H12 e1 e2 He1 He2.
destruct H12 as [wr2 [Htc Hrf]].
assert (write_to wr2 l) as Hwwr2.
  destruct_valid Hv; generalize (Hrf_cands wr2 (Read cr2) Hrf); intros [? [? [l2 [Hwr2 ?]]]].
  destruct Hcs2 as [HL2 ?]; destruct HL2 as [Htk2 ?]; destruct Htk2 as [x2 (*[*)Hat2 (*?]*)]; destruct Hat2 as [? [? [Hl2 ?]]].
  destruct H1 as [[? ?] ?]; unfold loc in Hl2; rewrite H1 in Hl2; inversion Hl2; subst; auto.
  generalize (no_other_stores E Hwwr2); intros [c [Hcs [Hec [e He]]]].

unfold lockc; apply Trans with e.

  apply nrfpio_implies_lock with n cr1 c; subst; auto.

  apply RF; unfold css_lift; exists c; exists cr2; split; [unfold css|split]; auto.
  split; auto. split; auto. split; auto.
  apply diff_cs with E X l l; auto.
    rewrite Hec; auto.
  rewrite Hec; auto.
Qed.

Lemma mws_rf_implies_lock :
  forall E X l crit,
  well_formed_event_structure E ->
  valid_execution E X ->
  cs E l crit ->
  rel_seq (ws X) (rf X) (inite l) (Read crit) ->
  (forall e, (Evts crit) e -> lockc E X l (inite l) e).
Proof.
intros E X l crit Hwf Hv Hcs Hmwsrf (*[w [Hmws Hrf]]*) e He.
    generalize (init_store l); intro Hiw.
    generalize (no_other_stores E Hiw); intros [ci [Hcsi [Hecsi ?]]].
    rewrite <- Hecsi in Hmwsrf.
generalize (wsrf_implies_rfpio E X l ci crit Hwf Hv Hcsi Hcs Hmwsrf); intro (*Hor.
inversion Hor as [Htc | Hws].*) Htc.
destruct Htc as [n Htc]; apply nrfpio_rf_implies_lock with ci crit n; auto.
assert (cs E l ci /\ Write ci = inite l) as Hand.
  split; auto.
apply (init_cs Hand).

 (* rewrite Hecsi in Hws; generalize (init_ws X l); intro Hc; contradiction.*)
Qed.

Lemma init_rf_implies_lock :
  forall E X l crit,
  well_formed_event_structure E ->
  valid_execution E X ->
  cs E l crit ->
  (rf X) (inite l) (Read crit) ->
  (forall e, (Evts crit) e -> lockc E X l (inite l) e).
Proof.
intros E X l cr Hwf Hv Hcs Hrf e He.
generalize (init_store l); intro Hwi.
generalize (no_other_stores E Hwi); intros [ci [Hcsi [Hwcsi ?]]].
assert (cs E l ci /\ Write ci = inite l) as Hand.
  split; auto.
generalize (init_cs Hand); intro Hei.
unfold lockc; apply RF; unfold css_lift.
  exists ci; exists cr; split; [unfold css| split; auto].
    split; auto. split; auto. split; auto.
  apply diff_cs with E X l l; auto.
  rewrite Hwcsi; auto.
  rewrite Hwcsi; auto.
Qed.

Lemma css_init : forall E X l,
  well_formed_event_structure E ->
  valid_execution E X ->
  forall crit, cs E l crit ->
  (forall e, (Evts crit) e -> lockc E X l (inite l) e).
Proof.
intros E X l Hwf Hv crit Hcs e He.
generalize Hv; intro Hva.
    assert (In _ (reads E) (Read crit)) as Hercrit.
      destruct Hcs as [Hlcs ?]; destruct Hlcs as [Htk ?];
        destruct Htk as [w [[Hev ?] ?]]; split; auto.
destruct_valid Hv;
generalize (Hrf_init (Read crit) Hercrit); intros [w [Horc Hrfw]].
  destruct (eqEv_dec (inite l) w) as [Heq | Hneq].
    subst.
      apply init_rf_implies_lock with crit; auto.

  assert (rel_seq (ws X) (rf X) (inite l) (Read crit)) as Hir.
    exists w; split; auto.

    generalize (Hws_tot l); intro Hlin; destruct_lin Hlin.
    assert (In Event (writes_to_same_loc_l (events E) l) (inite l)) as Hinit.
      split; [apply (init_evt E l) | apply (init_store l)].
    assert (In Event (writes_to_same_loc_l (events E) l) w) as Hw.
      split; auto.
      (*apply dom_rf_in_events with X (Read crit); auto.
        split; auto.*)
      apply rf_implies_same_loc with E X (Read crit); auto.
        destruct Hcs as [HL ?]. destruct HL as [Htk ?]. destruct Htk as [wr (*[*)Hat (*?]*)].
        destruct_atom Hat.
        destruct Hr as [Her [lr [vr Hrr]]].
        exists vr; unfold loc in Hlr; rewrite Hrr in Hlr; inversion Hlr as [Heq]; rewrite <- Heq; auto.
    generalize (Htot (inite l) w Hneq Hinit Hw); intro Hor; inversion Hor as [Hiw | Hwi].
    destruct Hiw; auto.
    destruct Hwi; generalize (init_ws X l); intro Hn.
    assert (exists e, ws X e (inite l)) as Hc.
      exists w; auto.
    contradiction.
    apply mws_rf_implies_lock with crit; auto.
Qed.

Lemma rf_contrad :
  forall E X l,
  well_formed_event_structure E ->
  valid_execution E X ->
  forall w cs2 cs3,
  rf X w (Read cs2) -> rf X w (Read cs3) -> cs2 <> cs3 ->
  ~(cs E l cs2 /\ cs E l cs3).
Proof.
intros E X l Hwf Hv w cs2 cs3 Hrf2 Hrf3 Hd [Hcs2 Hcs3].
generalize Hcs2; intro Hcs2'; generalize Hcs3; intro Hcs3'.
destruct Hcs2 as [[Htk2 ?] ?]; destruct Hcs3 as [[Htk3 ?] ?].
  destruct Htk2 as [ws2 (*[*)Hrmw2 (*?]*)]; destruct Htk3 as [ws3 (*[*)Hrmw3 (*?]*)].
      generalize Hrmw2; intro Hrmw2b; generalize Hrmw3; intro Hrmw3b.
      destruct Hrmw2 as [Hr2 [Hatr2 [Hlr2 [Hw2 [Haw2 [Hlw2 [Hporw2 [Hnoc2 Hno2]]]]]]]];
      destruct Hrmw3 as [Hr3 [Hatr3 [Hlr3 [Hw3 [Haw3 [Hlw3 [Hporw3 [Hnoc3 Hno3]]]]]]]].
        assert (ws X w ws2) as Hws_wws2.

          destruct (eqEv_dec w ws2) as [Heq | Hneq].

          assert (tc (rel_union (hb E X) (pio_llh E)) w w) as Hcy.
            apply trc_ind with (Read cs2); apply trc_step.
            left; left; left; auto.
            right; split; auto; subst; auto.
            (*  rewrite Hlr2; rewrite Hlw2; auto. *)
            split; auto.
              intros [? [? [? [? Hrws2]]]]; destruct Hw2 as [? [? [? Hw2]]];
              rewrite Hrws2 in Hw2; inversion Hw2.
          destruct_valid Hv; unfold not in Hsp; unfold acyclic in Hsp;
            generalize (Hsp w Hcy); intro Ht; inversion Ht.

          assert (In _ (writes_to_same_loc_l (events E) l) w) as Hww.
            split.
              apply dom_rf_in_events with X (Read cs2); auto.
              split; destruct_valid Hv; auto.
              assert (read_from (Read cs2) l) as Hrcs2.
                destruct Hr2 as [? [l2 [v2 Har2]]]; exists v2.
                unfold loc in Hlr2; rewrite Har2 in Hlr2; inversion Hlr2 as [Heq]; rewrite <- Heq; auto.
              apply (rf_implies_same_loc w Hv Hrf2 Hrcs2); auto.
             (*   destruct_valid Hv;
                generalize (ran_rf_is_read E X w (Read cs2) Hrf_cands Hrf2);
                intros [l2 [v2 Har2]]; exists v2.
                unfold loc in Hlr2; rewrite Har2 in Hlr2; inversion Hlr2 as [Heq].
                rewrite <- Heq; auto. *)
          assert (In _ (writes_to_same_loc_l (events E) l) ws2) as Hww2.
            split; destruct Hw2 as [Hews2 [lws2 [vws2 Haws2]]]; auto; exists vws2.
                unfold loc in Hlw2; rewrite Haws2 in Hlw2; inversion Hlw2 as [Heq].
                rewrite <- Heq; auto.
         assert (In _ (writes_to_same_loc_l (events E) l) w /\
                     In _ (writes_to_same_loc_l (events E) l) ws2) as Hand.
           split; auto.
          destruct_valid Hv; generalize (ws_tot E X (Hws_tot l) Hand Hneq); intro Hor.
          inversion Hor; auto.
          assert (tc (rel_union (hb E X) (pio_llh E)) w w) as Hcy.
            apply trc_ind with (Read cs2). apply trc_step;
            left; left; left; auto.
            apply trc_ind with ws2; apply trc_step.
            right; split; auto; subst; auto.
            split; auto.
              intros [? [? [? [? Hrws2]]]]; destruct Hw2 as [? [? [? Hw2]]];
              rewrite Hrws2 in Hw2; inversion Hw2.
            left; right; auto.
          unfold not in Hsp; unfold acyclic in Hsp;
            generalize (Hsp w Hcy); intro Ht; inversion Ht.

        assert (fr E X (Read cs3) ws2) as Hfr_r3ws2.
          split. destruct Hr3; auto.
            split; destruct Hw2; auto.
              exists w; split; auto.
        assert (ws X w ws3) as Hws_wws3.

          destruct (eqEv_dec w ws3) as [Heq | Hneq].

          assert (tc (rel_union (hb E X) (pio_llh E)) w w) as Hcy.
            apply trc_ind with (Read cs3); apply trc_step.
            left; left; left; auto.
            right; split; auto; subst; auto.
              rewrite Hlr3; rewrite Hlw3; auto.
            split; auto.
              intros [? [? [? [? Hrws3]]]]; destruct Hw3 as [? [? [? Hw3]]];
              rewrite Hrws3 in Hw3; inversion Hw3.
          destruct_valid Hv; unfold not in Hsp; unfold acyclic in Hsp;
            generalize (Hsp w Hcy); intro Ht; inversion Ht.

          assert (In _ (writes_to_same_loc_l (events E) l) w) as Hww.
            split.
              apply dom_rf_in_events with X (Read cs2); auto.
              split; destruct_valid Hv; auto.
              assert (read_from (Read cs2) l) as Hrcs2.
                destruct Hr2 as [? [l2 [v2 Har2]]]; exists v2.
                unfold loc in Hlr2; rewrite Har2 in Hlr2; inversion Hlr2 as [Heq]; rewrite <- Heq; auto.
              apply (rf_implies_same_loc w Hv Hrf2 Hrcs2); auto.
              (*  destruct_valid Hv;
                generalize (ran_rf_is_read E X w (Read cs2) Hrf_cands Hrf2);
                intros [l2 [v2 Har2]]; exists v2.
                unfold loc in Hlr2; rewrite Har2 in Hlr2; inversion Hlr2 as [Heq].
                rewrite <- Heq; auto. *)
          assert (In _ (writes_to_same_loc_l (events E) l) ws3) as Hww3.
            split; destruct Hw3 as [Hews3 [lws3 [vws3 Haws3]]]; auto; exists vws3.
                unfold loc in Hlw3; rewrite Haws3 in Hlw3; inversion Hlw3 as [Heq].
                rewrite <- Heq; auto.
         assert (In _ (writes_to_same_loc_l (events E) l) w /\
                     In _ (writes_to_same_loc_l (events E) l) ws3) as Hand.
           split; auto.
          destruct_valid Hv; generalize (ws_tot E X (Hws_tot l) Hand Hneq); intro Hor.
          inversion Hor; auto.
          assert (tc (rel_union (hb E X) (pio_llh E)) w w) as Hcy.
            apply trc_ind with (Read cs3). apply trc_step;
            left; left; left; auto.
            apply trc_ind with ws3; apply trc_step.
            right; split; auto; subst; auto.
              rewrite Hlr3; rewrite Hlw3; auto.
            split; auto.
              intros [? [? [? [? Hrws3]]]]; destruct Hw3 as [? [? [? Hw3]]];
              rewrite Hrws3 in Hw3; inversion Hw3.
            left; right; auto.
          unfold not in Hsp; unfold acyclic in Hsp;
            generalize (Hsp w Hcy); intro Ht; inversion Ht.

        assert (fr E X (Read cs2) ws3) as Hfr_r2ws3.
          split. destruct Hr2; auto.
            split; destruct Hw3; auto.
              exists w; split; auto.

        assert (ws X ws2 ws3 \/ ws X ws3 ws2) as Hor_ws.
          assert (ws2 <> ws3) as Hneq.
            generalize (cs_diff E Hd); intros [? Hws].
              apply (Hws l ws2 ws3); auto.

          assert (In _ (writes_to_same_loc_l (events E) l) ws2) as Hww2.
            split; destruct Hw2 as [Hews2 [lws2 [vws2 Haws2]]]; auto; exists vws2.
                unfold loc in Hlw2; rewrite Haws2 in Hlw2; inversion Hlw2 as [Heq].
                rewrite <- Heq; auto.
          assert (In _ (writes_to_same_loc_l (events E) l) ws3) as Hww3.
            split; destruct Hw3 as [Hews3 [lws3 [vws3 Haws3]]]; auto; exists vws3.
                unfold loc in Hlw3; rewrite Haws3 in Hlw3; inversion Hlw3 as [Heq].
                rewrite <- Heq; auto.
         assert (In _ (writes_to_same_loc_l (events E) l) ws2 /\
                     In _ (writes_to_same_loc_l (events E) l) ws3) as Hand.
           split; auto.
          destruct_valid Hv; apply (ws_tot E X (Hws_tot l) Hand Hneq).

        inversion Hor_ws as [H23 | H32].

          destruct (eqProc_dec (proc_of ws2) (proc_of (Read cs3))) as [Heqp23 | Hdiffp23].

      assert (exists e : Event, stars E e /\ po_iico E (Read cs3) e /\ po_iico E e ws3) as Hco.
        exists ws2; split; auto.
          split.
           assert (In _ (events E) ws2) as Hews2.
             destruct Hw2; auto.
           assert (In _ (events E) (Read cs3)) as Her3.
             destruct Hr3; auto.
           generalize (same_proc_implies_po ws2 (Read cs3) Hwf Heqp23 Hews2 Her3); intro Hor.
           inversion Hor; auto.
           assert (tc (rel_union (hb E X) (pio_llh E)) (Read cs3) (Read cs3)) as Hcy.
             apply trc_ind with ws2; apply trc_step.
               left; left; right; auto.
               right; split; auto.
               apply sym_eq; apply fr_implies_same_loc with E X; auto.
                 destruct_valid Hv; split; split; auto.
               split; auto.
              intros [[? [? [? Hrws2]]] ?]; destruct Hw2 as [? [? [? Hw2]]];
              rewrite Hrws2 in Hw2; inversion Hw2.
               destruct_valid Hv; unfold not in Hsp; unfold acyclic in Hsp;
               generalize (Hsp (Read cs3) Hcy); intro Ht; inversion Ht.
         assert (proc_of ws2 = proc_of ws3) as Heqp.
           rewrite Heqp23.
           apply po_implies_same_proc with E; auto.
           apply po_iico_domain_in_events with ws3; auto.
           apply po_iico_range_in_events with (Read cs3); auto.
           assert (In _ (events E) ws2) as Hews2.
             destruct Hw2; auto.
           assert (In _ (events E) ws3) as Hews3.
             destruct Hw3; auto.
           generalize (same_proc_implies_po ws2 ws3 Hwf Heqp Hews2 Hews3); intro Hor.
           inversion Hor; auto.
           assert (tc (rel_union (hb E X) (pio_llh E)) ws3 ws3) as Hcy.
             apply trc_ind with ws2; apply trc_step.
               right; split; auto.
               apply sym_eq;
               apply ws_implies_same_loc with E X; auto.
                 destruct_valid Hv; split; split; auto.
               split; auto.
              intros [[? [? [? Hrws3]]] ?]; destruct Hw3 as [? [? [? Hw3]]];
              rewrite Hrws3 in Hw3; inversion Hw3.
               left; right; auto.

               destruct_valid Hv; unfold not in Hsp; unfold acyclic in Hsp;
               generalize (Hsp ws3 Hcy); intro Ht; inversion Ht.
      contradiction.

            assert (exists w' : Event,
          proc_of w' <> proc_of (Read cs3) /\
          writes E w' /\ loc w' = (*Some*) l /\ fr E X (Read cs3) w' /\ ws X w' ws3) as Hc.
            exists ws2; split; auto.
            generalize (Hno3 X); intro Hco; contradiction.

          destruct (eqProc_dec (proc_of ws3) (proc_of (Read cs2))) as [Heqp23 | Hdiffp23].

            assert (exists e : Event, stars E e /\ po_iico E (Read cs2) e /\ po_iico E e ws2) as Hc.
              exists ws3; split; auto.
          split.
           assert (In _ (events E) ws3) as Hews3.
             destruct Hw3; auto.
           assert (In _ (events E) (Read cs2)) as Her2.
             destruct Hr2; auto.
           generalize (same_proc_implies_po ws3 (Read cs2) Hwf Heqp23 Hews3 Her2); intro Hor.
           inversion Hor; auto.
           assert (tc (rel_union (hb E X) (pio_llh E)) (Read cs2) (Read cs2)) as Hcy.
             apply trc_ind with ws3; apply trc_step.
               left; left; right; auto.
               right; split; auto.
               apply sym_eq; apply fr_implies_same_loc with E X; auto.
                 destruct_valid Hv; split; split; auto.
               split; auto.
              intros [[? [? [? Hrws3]]] ?]; destruct Hw3 as [? [? [? Hw3]]];
              rewrite Hrws3 in Hw3; inversion Hw3.
               destruct_valid Hv; unfold not in Hsp; unfold acyclic in Hsp;
               generalize (Hsp (Read cs2) Hcy); intro Ht; inversion Ht.
         assert (proc_of ws3 = proc_of ws2) as Heqp.
           rewrite Heqp23.
           apply po_implies_same_proc with E; auto.
           apply po_iico_domain_in_events with ws2; auto.
           apply po_iico_range_in_events with (Read cs2); auto.
           assert (In _ (events E) ws3) as Hews3.
             destruct Hw3; auto.
           assert (In _ (events E) ws2) as Hews2.
             destruct Hw2; auto.
           generalize (same_proc_implies_po ws3 ws2 Hwf Heqp Hews3 Hews2); intro Hor.
           inversion Hor; auto.
           assert (tc (rel_union (hb E X) (pio_llh E)) ws2 ws2) as Hcy.
             apply trc_ind with ws3; apply trc_step.
               right; split; auto.
               apply sym_eq;
               apply ws_implies_same_loc with E X; auto.
                 destruct_valid Hv; split; split; auto.
               split; auto.
              intros [[? [? [? Hrws2]]] ?]; destruct Hw2 as [? [? [? Hw2]]];
              rewrite Hrws2 in Hw2; inversion Hw2.
               left; right; auto.

               destruct_valid Hv; unfold not in Hsp; unfold acyclic in Hsp;
               generalize (Hsp ws2 Hcy); intro Ht; inversion Ht.

            contradiction.

            assert (exists w' : Event,
          proc_of w' <> proc_of (Read cs2) /\
          writes E w' /\ loc w' = (*Some*) l /\ fr E X (Read cs2) w' /\ ws X w' ws2) as Hc.
            exists ws3; split; auto.
          generalize (Hno2 X); intro Hco; contradiction.
Qed.

Lemma rf_contrad_or :
  forall E X l,
  well_formed_event_structure E ->
  valid_execution E X ->
  forall w cs2 cs3,
  rf X w (Read cs2) -> rf X w (Read cs3) ->
  ~(cs E l cs2 /\ cs E l cs3) \/ cs2 = cs3.
Proof.
intros E X l Hwf Hv w cs2 cs3 Hrf2 Hrf3.
  generalize (excluded_middle (cs2 = cs3)); intro Hor; inversion Hor; auto.
  left; apply rf_contrad with X w; auto.
Qed.

 Lemma same_cs_lock :
    forall E X l, forall x y z crit,
    well_formed_event_structure E ->
    valid_execution E X ->
    cs E l crit ->
    Evts crit x -> Evts crit y ->
    lockc E X l x z ->
    lockc E X l y z.
Proof.
intros E X l x y z crit Hwf Hv Hcrit Hx Hy Hxz.
induction Hxz.
  destruct_csslift H.
  generalize Hcss; intro Hcssb;
  destruct_css Hcss.
  generalize (unic_css e1 Hcrit Hcs1 Hx Hev1); intro Heq; subst.
    unfold lockc; apply RF; unfold css_lift.
      exists s1; exists s2; split; auto.
  unfold lockc; apply Trans with e; auto.
    apply (IHHxz1 Hx).
Qed.

Lemma lockc_step_contrad :
  forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
  forall l z x cs1 cs2,
    css E X l cs1 cs2 ->
    Evts cs1 z -> Evts cs2 x ->
   forall y, (lockc E X l z y) ->
   (lockc E X l x y) \/ (x = y) \/ Evts cs2 y.
Proof.
intros E X Hwf Hv l z x cs1 cs2 Hcsszx Hez Hex y Hzy.
induction Hzy as [z y Hszy |].
    destruct_css Hcsszx.
    destruct_csslift Hszy.
generalize (excluded_middle (x = y)); intro Hore.
inversion Hore; auto.
generalize (excluded_middle (cs2 = s2)); intro Horcs.
inversion Horcs.
  subst; auto.
  destruct Hcss as [[Hcs1' [Hcs2' Hdcs']] Hrf'].
  generalize (unic_css z Hcs1 Hcs1' Hez Hev1); intro Heq; subst.
  generalize (rf_contrad_or E X l Hwf Hv (Write s1) cs2 s2 Hrf Hrf'); intro Hor.
  inversion Hor.
    assert (cs E l cs2 /\ cs E l s2) as Hc.
      split; auto. contradiction.
   subst; auto.

  generalize (IHHzy1 Hez); intro Hor.
  inversion Hor.
  left; unfold lockc in * |- *;apply Trans with e; auto; apply IHlockc1; auto.
  inversion H.
    subst; auto.
  left; apply same_cs_lock with e cs2; auto.
    destruct_css Hcsszx; auto.
Qed.

Lemma same_source_implies_ordered :
  forall E X l, forall x y z,
  well_formed_event_structure E ->
  valid_execution E X ->
  (lockc E X) l z x /\ (lockc E X) l z y ->
  (lockc E X) l x y \/ (lockc E X) l y x \/  x = y \/ (exists crit, cs E l crit /\ Evts crit x /\ Evts crit y).
Proof.
intros E X l x y z Hwf Hv [Hzx Hzy].
induction Hzx.
  destruct_csslift H.
  generalize (lockc_step_contrad E X Hwf Hv l e1 e2 s1 s2 Hcss Hev1 Hev2 y Hzy); intro Hor.
  inversion Hor.
    left; auto.
    inversion H.
    right; right; auto.
    right; right; right.
    exists s2; split; auto.
    destruct_css Hcss; auto.

  generalize (IHHzx1 Hzy); intro Hor.
  inversion Hor as [Hley | Hulye].
  apply IHHzx2; auto.

  inversion Hulye as [Hlye | Hueq].
  right; left; unfold lockc in * |- *;apply Trans with e; auto.

  inversion Hueq.
    subst; auto.
  destruct H as [crit [Hcscrit [Hecrit Hycrit]]].
  right; left; apply same_cs_lock with e crit; auto.
Qed.

Lemma lockc_tot : forall E X l,
  well_formed_event_structure E ->
  valid_execution E X ->
  forall e1 e2, (events E e1 /\ events E e2) /\
  (exists cs1, exists cs2, (cs E l) cs1 /\ cs E l cs2 /\
    cs1 <> cs2 /\ (Evts cs1) e1 /\ (Evts cs2) e2) -> (lockc E X l) e1 e2 \/ (lockc E X l) e2 e1.
Proof.
intros E X l Hwf Hv e1 e2 [[He1 He2] [cs1 [cs2 [Hcs1 [Hcs2 [Hdiff [Hee1 Hee2]]]]]]].
generalize (css_init E X l Hwf Hv cs1 Hcs1 e1 Hee1); intro Hl1.
generalize (css_init E X l Hwf Hv cs2 Hcs2 e2 Hee2); intro Hl2.
(*generalize (init_css E X l); intros [cri [ei [Heei Hncr]]].*)
assert (lockc E X l (inite l) e1 /\ lockc E X l (inite l) e2) as Hand.
 (* assert (lockc E X l ei e1 /\ lockc E X l ei e2) as Hand. *)
  split; auto.
generalize (same_source_implies_ordered E X l e1 e2 (inite l) Hwf Hv Hand); intro Htor.
inversion Htor.
  left; auto.
  inversion H.
  right; auto.
  inversion H0.
  generalize (cs_diff E Hdiff); intros [Hed ?].
    generalize (Hed e1 e2 Hee1 Hee2); intro Hc.
    contradiction.
  destruct H1 as [crit [Hcrit [Hcrit1 Hcrit2]]].
    generalize (unic_css e1 Hcs1 Hcrit Hee1 Hcrit1); intro Heq.
    generalize (unic_css e2 Hcs2 Hcrit Hee2 Hcrit2); intro Heq2.
    rewrite <- Heq2 in Heq; contradiction.
Qed.

Lemma s_tot_l :
forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
  forall e1 e2, (events E e1 /\ events E e2) /\ s E X e1 e2->
  (exists l, (lockc E X l) e1 e2 \/ (lockc E X l) e2 e1).
Proof.
intros E X Hwf Hv e1 e2 [[He1 He2] Hs].
destruct Hs as [l [s1 [s2 [Hsc [Hes1 Hes2]]]]].
exists l; apply lockc_tot; auto; split; auto.
exists s1; exists s2; destruct Hsc as [Hcs1 [Hcs2 Hdcs]];
split; auto; split; auto.
Qed.

Lemma s_tot :
forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
  forall e1 e2, (events E e1 /\ events E e2) /\ s E X e1 e2->
  ((lock E X) e1 e2 \/ (lock E X) e2 e1).
Proof.
intros E X Hwf Hv e1 e2 Hand;
generalize (s_tot_l E X Hwf Hv e1 e2 Hand); intros [l Hor];
inversion Hor; [left | right]; exists l; auto.
Qed.

Hypothesis ac_s_lock :
  forall E X, acyclic (rel_union (s E X) (lock E X)).

Lemma s_lock :
  forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
  rel_incl (s E X) (lock E X).
Proof.
intros E X Hwf Hv x y Hxy.
assert ((events E x /\ events E y) /\ s E X x y) as Hand.
  split; [split|]; auto; destruct Hxy as [l [s1 [s2 [Hs12 [Hex Hey]]]]];
  destruct Hs12 as [Hcs1 [Hcs2 ?]].
    destruct Hcs1 as [? [Hev ?]].
    generalize (Hev x); intro Heq; destruct Heq as [Hd Hb].
    generalize (Hd Hex); intros [Hpo1 Hpo2];
    change (events E x) with (In _ (events E) x);
    apply po_iico_domain_in_events with (Eb s1); auto.
    destruct Hcs2 as [? [Hev ?]].
    generalize (Hev y); intro Heq; destruct Heq as [Hd Hb].
    generalize (Hd Hey); intros [Hpo1 Hpo2];
    change (events E y) with (In _ (events E) y);
    apply po_iico_domain_in_events with (Eb s2); auto.
generalize (s_tot E X Hwf Hv x y Hand); intro Hor; inversion Hor; auto.
generalize (ac_s_lock E X); intro Hac; assert False as Ht.
  unfold acyclic in Hac; assert (tc (rel_union (s E X) (lock E X)) x x) as Hin.
    apply trc_ind with y; apply trc_step; [left | right]; auto.
  apply (Hac x Hin).
inversion Ht.
Qed.

Lemma s_po_ac :
  forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
  acyclic (rel_union (s E X) (po_iico E)).
Proof.
intros E X Hwf Hv;
apply incl_ac with (rel_union (lock E X) (po_iico E)).
intros x y Hxy; inversion Hxy; [left | right]; auto.
apply s_lock; auto.
apply lock_pop; auto.
Qed.

Lemma happens_before_irr :
  forall E X x,
  well_formed_event_structure E ->
  valid_execution E X ->
  ~(happens_before E X x x).
Proof.
intros E X x Hwf Hv Hx.
(*generalize (lock_pop Hwf Hv); intro Hac;*)
generalize (s_po_ac E X Hwf Hv); intro Hac;
  unfold happens_before in Hx; rewrite union_triv in Hx;
  apply (Hac x Hx).
Qed.

Definition covered E X r :=
  forall e1 e2, (competing E X e1 e2) -> (r E X e1 e2 \/ r E X e2 e1).

Definition covering s :=
  forall E X, well_formed_event_structure E ->
    AResWmm.valid_execution E X ->
    covered E X s -> acyclic (AnWmm.ghb E X).

End HB.

(*Module DrfG := DrfGuarantee HB.
Module AWmm := Wmm A dp.

Module AResWmm := Wmm ARes dp.
Lemma locks_provide_drf_guarantee :
  (forall E X, AnWmm.valid_execution E X -> DrfG.Drf.covered E X DrfG.Drf.s) ->
  (forall E X, well_formed_event_structure E ->
   (AResWmm.valid_execution E X <-> AnWmm.valid_execution E X)).
Proof.
apply DrfG.drf_guarantee.
Qed.*)

End Locks.
