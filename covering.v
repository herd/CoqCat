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

(** * Covering relation 

The goal of this module is to define a relation that arbitrates all the competing events of an execution in such way that if all the conflicts of an execution on a weak architecture are arbitrated, the execution is valid on a strong architecture
*)

Module Covering (A1 A2: Archi) (dp:Dp).

(** We suppose that A1 is a weaker architecture than A2 *)

Module Wk := Weaker A1 A2 dp.
Import Wk.
Hypothesis wk : weaker.

(** Takes two arguments and produce the relation that relates only these two arguments *)

Definition pair (x y : Event): Rln Event :=
  fun e1 => fun e2 => (e1 = x /\ e2 = y).

(** We import the lemmas about validity of executions on A2 without barriers *)

Module VA2 := Valid A2n dp.
Import VA2. Import VA2.ScAx.

(** ** Competition, Covered Execution and Covering

This module type describes an abstract notion of:

- Competition between the events of an execution, and the properties such a competing relation should have
- Covered execution, i.e. there is a _synchronisation_ relation relating all the pairs of competing events of the execution (in any direction)
- Covering, i.e. a notion of competing events and a relation [s], such that for every execution valid on the weak architecture [A1], if the execution is covered by [s], the execution is valid on the stronger architecture [A2]
*)

Module Type Compete.

(** The competing relation is an arbitrary relation *)

Parameter competing : Event_struct -> Execution_witness -> Rln Event.

(** To be well-formed, a competing relation must relate only the events of the event structure it is applied on *)

Parameter compete_in_events :
  forall E X x y,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  competing E X x y ->
  events E x /\ events E y.

(** An arbitrary _synchronisation_ relation on the events of an execution, on which we will defined the notion of covering *)

Parameter s : Event_struct -> Execution_witness -> Rln Event.

(** An execution is covered by a relation, if all the competing events of this execution are related by the relation in either direction *)

Definition covered E X r :=
  forall e1 e2, (competing E X e1 e2) -> (r E X e1 e2 \/ r E X e2 e1).

(** A competing relation and a relation are covering if any execution covered by the synchronisation relation and valid on the weak architecture [A1] is also valid on the stronger architecture [A2] *)

Definition covering s :=
  forall E X, well_formed_event_structure E ->
    A1Wmm.valid_execution E X ->
    covered E X s -> acyclic (A2nWmm.ghb E X).

(** For a given execution, [cns] is the subset of competing events that are not related by the synchronisation relation *)

Definition cns E X :=
  fun e1 => fun e2 => competing E X e1 e2 /\ ~ (s E X e1 e2 \/ s E X e2 e1).

(** We assume that in a well-formed event structure and with an execution valid on the weak architecture [A1], no event is competing with itself *)

Parameter competing_irr : forall E X,
  well_formed_event_structure E ->
    A1Wmm.valid_execution E X ->
  ~ (exists z, competing E X z z).

(** We assume that in a well-formed event structure and with an execution valid on the weak architecture [A1], an event cannot occur in the program order after an event he is competing with *)

Parameter competing_not_po :
  forall E X x y, well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  competing E X x y -> ~ (po_iico E y x).

(** This is just an alias to the predicate [covering] called on the synchronisation relation *)

Parameter covering_s : covering s.

End Compete.

(** ** Preservation

This module takes a module of type [Compete] and states lemmas about how the coverage of competing pairs of events preserves the validity from a weak architecture to a stronger architecture *)

Module Preservation (C: Compete).

Import C.

(** Two architectures [A1] and [A2] are said to be convoluted if, from any execution witness containing unsynchronised competing events, we can build another execution witness valid on the stronger memory model [A2Wmm], in which the two events are still competing, and still unsynchronised.

If for a given event structure, we have an execution witness in which:

- Two events are competing on a first execution witness
- These two events are not related by the synchronisation relation

We can build another execution witness valid on [A2Wmm] for the same event structure. 

We build the read-from and the write serialization relations by calling respectively the functions [so_rfm] and [so_ws] from the module [VA2] on the linear extension of the transitive closure of the union of:

- The relation relating the two conflicting events
- The preserved program order on the stronger memory model [A2Wmm]
- The by-location program order

The two architectures are convoluted if the two events are still competing and unsynchronised in the obtained execution witness
*)

Definition convoluted_wf :=
  forall E X Y x y,
  competing E X x y ->
  ~ (s E X x y \/ s E X y x) ->
  rf Y = so_rfm E
         (LE (tc (rel_union (rel_union (rel_inter (cns E X) (pair x y)) (A2.ppo E)) (pio_llh E)))) ->
  ws Y = so_ws
         (LE (tc (rel_union (rel_union (rel_inter (cns E X) (pair x y)) (A2.ppo E)) (pio_llh E)))) ->
  competing E Y x y /\ ~ (s E Y x y \/ s E Y y x).

(** In a well-formed event structure with a well-formed read-from relation and two competing events, the range and domain the transitive closure of the the union of:

- The relation relating the two competing events
- The preserved program order on the stronger memory model [A2Wmm]
- The by-location program order

Are included in the set of events of the event structure *)

Lemma udr_xy_ppo2_in_events :
  forall E X r x y,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  competing E X x y ->
  Included _   (Union _ (dom (tc (rel_union (rel_union (rel_inter r (pair x y)) (A2.ppo E)) (pio_llh E))))
     (ran (tc (rel_union (rel_union (rel_inter r (pair x y)) (A2.ppo E)) (pio_llh E))))) (events E).
Proof.
intros E X r x y Hwf Hwfrf Hc e1 Hudr.
generalize (compete_in_events (*E X x y*) Hwf Hwfrf Hc); intros [Hex Hey].
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

(** For a given event structure, execution witness and pair of events, the transitive closure of the union of:

- The relation relating the two events if they are competing and the empty relation otherwise
- The preserved program order on the stronger memory model [A2Wmm]
- The by-location program order

Is included in the transitive closure of the union of:

- The relation relating the two events if they are competing and the empty relation otherwise
- The program order 
*)

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

(** In a well-formed event structure with a valid execution on the weaker architecture [A1Wmm], no event is competing with itself *)

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
    apply (competing_irr Hwf Hv1 Hc).
Qed.

(** In a well-formed event structure with a valid execution on the weaker architecture [A1Wmm], the transitive closure of the sequence of:

- The relation relating the two events if they are competing and the empty relation otherwise
- The pogram order

Is included in the sequence of:

- The relation relating the two events if they are competing and the empty relation otherwise
- The program order 
*)

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
  generalize (competing_not_po Hwf Hv1 Hc); intro; contradiction.
Qed.

(** In a well-formed event structure with a valid execution on the weaker architecture [A1Wmm] and two competing events on this execution, the union of:

- The relation relating the two competing events
- The preserved program order on the stronger memory model [A2Wmm]
- The by-location program order

is an acyclic relation
*)

Lemma competing_ac_ppo2 :
  forall E X x y,
  well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  competing E X x y ->
  (forall z, ~ tc (rel_union (rel_union (rel_inter (cns E X) (pair x y)) (A2.ppo E)) (pio_llh E)) z z).
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

(** If the two architectures are convoluted, we have a well-formed event structure, we have an execution valid on the weaker architecture [A1Wmm] in which two events are competing but unsynchronised, then there exists another execution on the same event structure, valid on the stronger architecture [A2Wmm], in which the two same events are still competing and unsynchronised *)

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

(** In a well-formed event structure with an execution valid on [A1Wmm], if the execution is covered by the synchronisation relation, the global happens-before relation of the execution on [A2nWmm] is acyclic *)

Lemma prop_implies_ac_ghb2 :
  forall E X,
  well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  covered E X s ->
  acyclic (A2nWmm.ghb E X).
Proof.
apply covering_s.
Qed.

(** In a well-formed event structure with an execution valid on [A1Wmm], if the execution is covered by the synchronisation relation, the execution is valid on [A2Wmm].
*)

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

(** This is an alternative proof of the same lemma, using only the definition of [covering_s] and not intermediate lemmas. *)

Lemma prop_implies_v2':
  forall E X,
  well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  covered E X s ->
  A2nWmm.valid_execution E X.
Proof.
  intros E X Hwf Hva1 Hp.
  unfold A1Wmm.valid_execution in Hva1;
  unfold A2nWmm.valid_execution.
  destruct Hva1 as [Hws [Hrf [Huproc [Hoota Hac]]]].
  repeat (try (split; auto)).
  apply covering_s; auto.
  unfold A1Wmm.valid_execution.
  repeat (try (split; auto)).
Qed.

Module A2Basic := Basic A2.

(** If two events of an execution are competing and unsynchronised, then the execution is not covered *)

Lemma not_prop_bak :
  forall E X,
  (exists x, exists y,
   competing E X x y /\ ~ (s E X x y \/ s E X y x)) ->
  ~ (covered E X s).
Proof.
intros E X [x [y [Hc Hns]]] Hp; apply Hns;
 apply (Hp x y Hc).
Qed.

(** If the execution is not covered, then there are some events that are competing and unsynchronised *)

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

(** In any execution, if the barrier relation of a weaker architecture is included in the global happens-before relation of the stronger architecture (without the barriers), then the global-happens of the weaker architecture is included in the global happens-before of the stronger architecture (without the barriers) *)

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

(** In any execution, if the barrier relation of the weaker architecture is included in the global happens-before of the stronger architecture (without the barriers), then the acyclicity of the global happens-before of the stronger architecture (without the barriers) implies the acyclicity of the global happens-before of the weaker architecture *)

Lemma ac2n_ac1 :
  forall E X,
  weaker -> rel_incl (A1.abc E X) (A2nWmm.ghb E X) ->
  acyclic (A2nWmm.ghb E X) ->
  acyclic (A1Wmm.ghb E X).
Proof.
intros E X Hwk Hi Hac2 x Hc1; unfold acyclic in Hac2; apply (Hac2 x).
generalize Hc1; apply tc_incl; apply ghb_incl'; auto.
Qed.

Hypothesis ab_wk : forall E X, rel_incl (A1.abc E X) (A2nWmm.ghb E X).

(** In a well-formed event structure, if an execution is valid on a stronger architecture (without the barriers), it is valid on a weaker architecture

This is stronger than [v2_implies_v1], because there can be barriers in [A1] in this lemma *)

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
