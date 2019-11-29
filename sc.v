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
Set Implicit Arguments.

(** * Sequentially consistent execution

In this module, we define 
- A notion of sequential execution
- A way to extract an SC execution witness from a sequential execution
- Two different possible implementation of a sequentially consistant memory models
- Lemmas that relate these three notions together *)

Module Sc (dp : Dp).
Import dp.

(** ** Definition *)

(** Create a relation that relates the event [er] to all the write events of
the event structure E that precede [er] in a relation [r] *)

Definition previous_writes (E:Event_struct) (r : Rln Event) (er:Event) :=
  fun ew => writes E ew /\ r ew er /\ loc ew = loc er.

(* begin hide *)
Set Implicit Arguments.
(* end hide *)

(** Given a set [xs] and a relation [r] on this set, the set of maximum elements
is such that :

- all its elements belong to [xs]
- for any element [x] of the set of maximum elements, if there is an element [x'] belonging to [xs], then [x = x']

Simply put, all the elements of [xs] that are related to no elements or to themselves.
*)

Definition maximal_elements (A:Set) (xs:set A) (r:Rln A) : set A :=
  fun x => In _ xs x /\ forall x', In _ xs x'/\ r x x' -> (x = x').

(* begin hide *)
Unset Implicit Arguments.
(* end hide *)

(** A sequential execution on an event structure is an order on the events of this structure such that:

- this order is a strict linear order (i.e. it is total)
- the program order is included in this order *)

Definition seq_exec (E:Event_struct) (so:Rln Event) : Prop :=
  linear_strict_order so (events E) /\
  rel_incl (po_iico E) so.

(** ** Building a SC execution witness

We show how to build an execution witness (a read-from relation and a write serialization from a sequential execution *)

(** *** read-from of SC execution *)

(** Two events are related by the read-from relation extracted from the sequential execution if:

- they are events from the domain or the range of the sequential execution
- the first one is a write event and the second one is a read event
- they access the same location
- they read/write the same value
- the first event belongs to the maximal elements of the previous writes (w.r.t. to the sequential execution) of the second event. Simply put, the first event
is the most recent write before the second event in the sequential execution *)

Definition so_rfm (E:Event_struct) (so : Rln Event) :=
  fun ew => fun er =>
    (rfmaps (udr so)) ew er /\
    (maximal_elements
       (previous_writes E so er) so) ew.

(** For any sequential execution on a event structure, for every read event in this structure, there is a write such that the read-from extracted from the sequential execution relates the write event to the read event *)

Hypothesis so_rfm_init :
  forall E so,
  forall er, In _ (reads E) er ->
             exists ew, In _ (events E) ew /\ so_rfm E so ew er .

(** *** write serialization of sequential execution *)

(** Two events are related by the write serialization extracted from the sequential execution if:

- They are related by the sequential execution
- They are both writes to the same location *)

Definition so_ws (so:Rln Event) : (Rln Event) :=
    fun e1 => fun e2 =>
    so e1 e2 /\
    exists l, In _ (writes_to_same_loc_l (udr so) l) e1 /\
      In _ (writes_to_same_loc_l (udr so) l) e2.

(** ** Definition of a SC witness

A SC witness associated to an event structure and a sequential execution is composed of the read-from relation and write serialization extracted from the sequential execution.
*)

Definition sc_witness (E:Event_struct) (so:Rln Event) : Execution_witness :=
  mkew (so_ws so) (so_rfm E so).

(** ** An SC-compatible architecture

The definition of [AiSc] is exactly the same as the one of its module type [Archi], but it adds an extra hypothesis [ab_sc_compat]. The goal of this extra-hypothesis is to ensure that the barrier relation will not enforce an ordering on events that would be incoherent with an SC architecture *)

Module AiSc <: Archi.

(** The preserved program order of the architecture is arbitrary but it respect the properties defined in [Archi] *)

Parameter ppo : Event_struct -> Rln Event.

Hypothesis ppo_valid : forall E, rel_incl (ppo E) (po_iico E).

Hypothesis ppo_fun :
  forall E s x y,
  ppo E x y /\ s x /\ s y <->
  ppo (mkes (Intersection Event (events E) s) (rrestrict (iico E) s)) x y.

(** The global read-from relation is arbitrary *)

Parameter inter : bool.
Parameter intra : bool.

(** The barrier relation is arbitrary but it respects the properties defined in [Archi] and the extra hypothesis [ab_sc_compat] *)

Parameter abc  : Event_struct -> Execution_witness -> Rln Event.

(** The barrier relation must be included in the sequence of:

- The reflexive closure of read-from
- The sequence of the program order and of the reflexive closure of read-from

This condition disallows the three following scenarios:

- An event [e1] must occur before an event [e2] according to the barrier, but [e2] must occur before [e1] according to the program order. Since we are on a
SC architecture, all the program order is preserved an this situation creates
a conflict.
- An event [e] must occur before a write [w] according to the barrier, and a read [r] that reads the value written by [w] must occur before [e] according to the program order.
- An read [r] must occur before an event [e] according to the barrier and reads a value written by a write [w], but [w] must occur after [e] according to program order.
*)

Parameter ab_sc_compat :
  forall E X, rel_incl (abc E X) (rel_seq (maybe (rf X)) (rel_seq (po_iico E) (maybe (rf X)))).

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

End AiSc.

Import AiSc.

(** ** Lemmas about SC executions

The module [ScAx] takes an architecture as a parameter, and contains lemmas about SC executions *)

Module ScAx (A:Archi).

Definition bimpl (b1 b2:bool) : Prop:=
  if (negb b1) || b2 then True else False.

(** This is an alias of boolean implication, aimed at the comparison of the global read-from relation of two architectures *)

Definition rf_impl (rf1 rf2 : bool) :=
  bimpl rf1 rf2.

(** This is an alias of relation inclusion for any possible event structure, aimed at the comparison of the preserved program order of two architectures *)

Definition ppo_incl (ppo1 ppo2 : Event_struct -> Rln Event) :=
  forall E, rel_incl (ppo1 E) (ppo2 E).

(** This is an alias of relation inclusion for any possible event structure and any possible execution witness, aimed at the comparison of the barrier relation of two architectures *)

Definition ab_incl (ab1 ab2 : Event_struct -> Execution_witness -> Rln Event) :=
  forall E X, rel_incl (ab1 E X) (ab2 E X).

(** We suppose that:

- The preserved program order of [A] is included in the preserved program order of [AiSc] in any event structure
- If the intra-threads read-froms are global on [A], they are global on [AiSc]
- If the inter-threads read-froms are global on [A], they are global on [AiSc]
- The barrier relation of [A] is include in the barrier relation of [AiSc] in any event structure and for any execution witness 

I.e. we suppose that [A] is weaker than [AiSc] *)

Hypothesis AwkAiSc :
  ppo_incl (A.ppo) (AiSc.ppo) /\
  bimpl (A.intra) (AiSc.intra) /\
  bimpl (A.inter) (AiSc.inter) /\
  ab_incl (A.abc) (AiSc.abc).

(** We immport the basic facts about A and we build a weak memory model on it *)

Module ABasic := Basic A dp.
Import ABasic.
Module AWmm := Wmm A dp.
Import AWmm.
Import A.

(** We define the SC check condition, which is the acyclicity of the program order and of the happens-before relation. This corresponds to the ghb acyclicity part of the condition of the generic condition of validity. Indeed, on an SC architectures, there are no barriers, all the program order is preserved and the whole read-from relation is global *)

Definition sc_check (E:Event_struct) (X:Execution_witness) : Prop :=
  acyclic (rel_union (po_iico E) (hb E X)).

(** *** Validy of SC execution

We show that an SC execution is valid on any architecture *)

Section sc_valid.

(** The domain and the range of a write serialization extracted from a sequential execution are included in the events of the event structure of this sequential execution *)

Lemma so_ws_dom_ran_wf :
  forall E so l,
  seq_exec E so ->
  Included _
  (Union _
    (dom (rrestrict (so_ws so) (writes_to_same_loc_l (events E) l)))
    (ran (rrestrict (so_ws so) (writes_to_same_loc_l (events E) l)))) (* = *)
  (writes_to_same_loc_l (events E) l).
Proof.
intros E so l Hsc.
unfold Included; intros x Hx.
inversion Hx as [e Hd | e Hr].
  unfold dom in Hd; unfold In in Hd; unfold rrestrict in Hd.
  destruct Hd as [y [Hso [Hmx Hmy]]]; apply Hmx.
  unfold ran in Hr; unfold In in Hr; unfold rrestrict in Hr.
  destruct Hr as [y [Hso [Hmy Hmx]]]; apply Hmx.
Qed.

(** The write serialization extracted from a sequential execution is a well-formed write serialization *)

Lemma sc_ws_wf :
  forall E so,
  seq_exec E so ->
  write_serialization_well_formed (events E) (so_ws so).
Proof.
intros E so Hsc_ord; split.
(*lin*)
intro l;split.
  (*dom/ran*)
  eapply (so_ws_dom_ran_wf). apply Hsc_ord.
  destruct Hsc_ord as [[Hdr [Htrans [Hac Htot]]] Hincl]; split.
  (*trans*)
  intros x1 x2 x3 H123; destruct H123 as [H12 H23].
  unfold In in * |- * ; unfold rrestrict in * |- * ;
  destruct H12 as [Hso12 [H1 H2]]; destruct H23 as [Hso23 [H2' H3]];
  split; [| split; [exact H1 | exact H3]].
  unfold In in * |- *; unfold so_ws in * |- *;
  destruct Hso12 as [Hso12 Hl12]; destruct Hso23 as [Hso23 Hl23]; split;
    [unfold In; eapply Htrans; split; [apply Hso12 | apply Hso23] |
      exists l; split].
  unfold writes_to_same_loc_l; unfold In; split.
    unfold udr; apply incl_union_left_in; exists x2; apply Hso12.
    destruct H1 as [Hevt1 Hw1]; apply Hw1.
  unfold writes_to_same_loc_l; unfold In; split.
    unfold udr; apply incl_union_right_in; exists x2; apply Hso23.
    destruct H3 as [Hevt3 Hw3]; apply Hw3.
  split.
  (*ac*)
  unfold not; intros x Hx; destruct Hx as [[Hso Hl] Hrest]; unfold not in Hac;
  apply (Hac x); exact Hso.
  (*tot*)
  intros x1 x2 Hdiff H1 H2.
  assert (In _ (events E) x1) as Hevt1.
    destruct H1 as [He1 Hrest]; unfold udr in He1.
    apply He1.
   assert (In _ (events E) x2) as Hevt2.
    destruct H2 as [He2 Hrest]; unfold udr in He2.
    apply He2.
  generalize (Htot x1 x2 Hdiff Hevt1 Hevt2); intro Ht.
  inversion Ht as [H12 | H21]; unfold rrestrict; unfold so_ws; unfold In;
  [left | right]; split.
  split; [apply H12 | exists l; split].
  unfold writes_to_same_loc_l; unfold In; split.
    unfold udr; apply incl_union_left_in; exists x2; apply H12.
    destruct H1 as [He1 Hw1]; apply Hw1.
  unfold writes_to_same_loc_l; unfold In; split.
    unfold udr; apply incl_union_right_in; exists x1; apply H12.
    destruct H2 as [He2 Hw2]; apply Hw2.
  unfold In in H1; unfold In in H2; split; [apply H1 | apply H2].
  split; [apply H21 | exists l; split].
  unfold writes_to_same_loc_l; unfold In; split.
    unfold udr; apply incl_union_left_in; exists x1; apply H21.
    destruct H2 as [He2 Hw2]; apply Hw2.
  unfold writes_to_same_loc_l; unfold In; split.
    unfold udr; apply incl_union_right_in; exists x2; apply H21.
    destruct H1 as [He1 Hw1]; apply Hw1.
  unfold In in H1; unfold In in H2; split; [apply H2 | apply H1].
(*mem*)
intros x e Hws.
destruct Hsc_ord as [[Hdr ?] ?].
destruct Hws as [Hso [l [[Hex Hwx] [Hee Hwe]]]]; exists l; split;
  unfold In; unfold writes_to_same_loc_l.
  split; [apply Hdr; apply Hex |apply Hwx].
  split; [apply Hdr; apply Hee |apply Hwe].
Qed.

Ltac destruct_lin H :=
  destruct H as [Hdr [Htrans [Hac Htot]]].

(** In the execution witness extracted from a sequential execution, no read event reads a value written by a write event that occurs later in the program order *)

Lemma sc_caus_wf :
  forall E so,
  seq_exec E so ->
  acyclic (rel_union (so_rfm E so) (ls E)).
Proof.
intros E so Hsc.
destruct Hsc as [Hlin Hincl].
apply ac_incl with so.
generalize (lso_is_tc Hlin); intro Heq.
destruct Hlin as [Hdr [Htrans [Hac Htot]]].
rewrite <- Heq in Hac; trivial.
unfold rel_incl; unfold rel_union;
intros x y Hin.
inversion Hin as [Hrf | Hdp].
  destruct Hrf as [? [[? [Hso ?]] Hmax]]; exact Hso.
  apply Hincl.
  unfold ls in Hdp.
  destruct Hdp as [Hrx [Hwy Hpo_xy]]; apply Hpo_xy.
Qed.

(** The read-from relation extracted from a sequential execution is a well-formed read-from relation *)

Lemma sc_rf_wf :
  forall E so,
  seq_exec E so ->
  rfmaps_well_formed E (events E) (so_rfm E so).
Proof.
intros E so (*Hdp*) Hsc_ord; unfold rfmaps_well_formed; split.
  destruct Hsc_ord as [Hlin Hincl]; destruct_lin Hlin.
  intros er Her; generalize (so_rfm_init E so er Her);
  intros [ew [Hew Hrfw]]; exists ew.
  split; auto.
 split; [intros e1 e2 H12 | ].
destruct H12 as [Hso12 [Hrf12 Hno12]].
destruct Hsc_ord as [[Hdr Hrest] Hincl].
unfold rfmaps.
destruct Hrf12 as [[Hevt1 Hw1] [Hso Heq]].
destruct Hso12 as [H1 [H2 Hl]].
split; [ | split; [|apply Hl]].
apply Hevt1.
apply Hdr; apply H2.
intros x w1 w2 [Hrf_w1x [Hpw_w1x Hmax_w1x]] [Hrf_w2x [Hpw_w2x Hmax_w2x]].
destruct (eqEv_dec w1 w2) as [Hy | Hn].
    apply Hy.
    assert (so w1 w2 \/ so w2 w1) as Hor.
      destruct Hsc_ord as [[Hdr [Htrans [Hac Htot]]] ?].
      apply (Htot w1 w2 Hn).
        destruct Hpw_w1x as [[Hew1 ?] ?]; apply Hew1.
        destruct Hpw_w2x as [[Hew2 ?] ?]; apply Hew2.
      inversion Hor as [H12 | H21].
        apply (Hmax_w1x w2); split; auto.
        apply sym_eq; apply (Hmax_w2x w1); split; auto.
Qed.

(** For any location, there are no contradictions between a sequential execution and the program order on the events reading from/writing to this location *)

Lemma so_ac_pio :
  forall E so,
  seq_exec E so ->
  acyclic
  (rel_union so (pio E)).
Proof.
intros E so Hsc.
apply ac_incl with (rel_union so (po_iico E)).
generalize (rel_union_refl so (po_iico E)); intro Heq; rewrite Heq.
destruct Hsc as [Hlin Hincl]; apply incl_implies_ac_union.
apply Hincl.
unfold acyclic; unfold not; intros x Htc.
generalize (lso_is_tc Hlin); intro Hso; rewrite Hso in Htc.
destruct Hlin as [Hdr [Htrans [Hac Htot]]].
unfold not in Hac; eapply Hac; apply Htc.
apply rel_incl_left.
unfold rel_incl; unfold pio;
  intros x y [Hloc Hpo].
apply Hpo.
Qed.

(** For any location, there are no contradictions between a sequential execution and the program order on the events reading from/writing to the same location and to the pairs of events for which at least one of the event is a write *)

Lemma so_ac_pio_llh :
  forall E so,
  seq_exec E so ->
  acyclic
  (rel_union so (pio_llh E)).
Proof.
intros E so Hsc.
eapply incl_ac with (rel_union so (pio E)).
  intros x y Hxy; inversion Hxy; [left |
    right; unfold pio; destruct H as [? [? ?]]]; auto.
apply so_ac_pio; auto.
Qed.

(** The happens-before extracted from a sequential execution is included in the sequential execution itself *)

Lemma hb_in_so :
  forall E so,
  seq_exec E so ->
  rel_incl (hb E (sc_witness E so)) so.
Proof.
unfold rel_incl; intros E so Hsc_ord x y Hhb.
inversion Hhb as [Hrf_fr | Hws]; unfold sc_witness in *; simpl in *.
  inversion Hrf_fr as [Hrf | Hfr].
  (*in rf*)
    destruct Hrf as [Hrf [[? [Hso ?]] ?]]; apply Hso.
  (*in fr*)
    destruct Hfr as [Hx [Hy [wr [Hwrx Hwry]]]]; simpl in *.
destruct Hsc_ord as [[Hdom [Htrans [Hac Htot]]] Hincl];
destruct Hwrx as [Hso_wrx [Hrf_wrx Hno]];
destruct Hso_wrx as [Hso_wr [Hso_x [lx [Hwwr [Hr_x ?]]]]];
  destruct Hwry as [Hso_wry [l2 [Hw_wr [Hevt_y [vy Hw_y]]]]].
  destruct Hrf_wrx as [? [Hso ?]].
  (*destruct Hw_y as [Hevt_y Hw_y].*)
destruct (eqEv_dec x y) as [Heq | Hdiff].
  rewrite Heq in Hr_x.
  case_eq (action y); unfold read_from in Hr_x; unfold write_to in Hw_y.
  intros d l v He2; rewrite He2 in Hr_x; rewrite He2 in Hw_y; case_eq d.
    intro Hr; rewrite Hr in Hw_y; (*destruct Hw_y as [? Hw_y];*) inversion Hw_y.
    intro Hw; rewrite Hw in Hr_x; destruct Hr_x as [? Hr_x]; inversion Hr_x.
  assert (In _ (events E) x) as He1.
   apply Hdom; apply Hso_x.
  assert (In _ (events E) y) as He2.
    apply Hdom; apply Hevt_y.
  generalize (Htot x y Hdiff He1 He2); intro Hor2.
  inversion Hor2 as [H12 | H21].
    exact H12.
    assert (wr = y) as Heq.
      apply (Hno y); split; auto.
      (*destruct Hw_y as [vy Hwy]; *)
      unfold In; unfold previous_writes; split; [ |split; auto].
      unfold writes; split; auto; exists l2; exists vy; auto.
       rewrite <- H1; destruct Hw_wr as [? [lwr Hw_wr]]; unfold write_to in *;
       unfold loc; rewrite Hw_wr;  rewrite Hw_y; trivial.
       subst; generalize (Hac y); intro Hc.
    contradiction.
  (*in ws*)
  destruct Hws as [Hso Hrest]; apply Hso.
Qed.

(** For any given location, there are no conflicts between the happens-before relation extracted from a sequential execution and the program order restricted to events reading from/writing to this location *)

Lemma sc_hb_wf :
  forall E so,
  seq_exec E so ->
  acyclic
  (rel_union (hb E (sc_witness E so)) (pio E)).
Proof.
intros E so Hsc_ord.
eapply ac_incl;
  [apply so_ac_pio; apply Hsc_ord |
    apply rel_incl_right; apply hb_in_so;
      apply Hsc_ord].
Qed.

(** For any given location, there are no conflicts between the happens-before relation extracted from a sequential execution and the program order restricted to events reading from/writing to this location, and to pairs of events for which at least one of the events is a write

This condition corresponds to the [uniproc] condition *)

Lemma sc_hb_llh_wf :
  forall E so,
  seq_exec E so ->
  acyclic
  (rel_union (hb E (sc_witness E so)) (pio_llh E)).
Proof.
intros E so Hsc_ord.
eapply ac_incl;
  [apply so_ac_pio_llh; apply Hsc_ord |
    apply rel_incl_right; apply hb_in_so;
      apply Hsc_ord].
Qed.

(** The read-from relation extracted from a sequential execution is included in the sequential execution *)

Lemma sc_rf_in_so :
  forall E so,
  rel_incl (rf (sc_witness E so)) so.
Proof.
intros E so; unfold rel_incl; unfold sc_witness; simpl; unfold so_rfm.
intros e1 e2 Hin; destruct Hin as [? [[? [Hso ?]] Hmax]]; exact Hso.
Qed.

(** The write serialization extracted from a sequential execution is included in the sequential execution *)

Lemma sc_ws_in_so :
  forall E so,
  rel_incl (ws (sc_witness E so)) so.
Proof.
intros E so; unfold sc_witness; simpl; unfold so_ws.
intros e1 e2 Hin; destruct Hin as [Hso Hrest]; exact Hso.
Qed.

(** The from-read relation extracted from a sequential execution is included in the sequential execution *)

Lemma sc_fr_in_so :
  forall E so,
  seq_exec E so ->
  rel_incl (fr E (sc_witness E so)) so.
Proof.
intros E so Hsc_ord; unfold sc_witness; unfold fr; unfold frmaps; simpl.
intros e1 e2 Hin.
destruct Hin as [Hevt1 [Hevt2 [wr [Hrf_wr1 Hws_wr2]]]];
destruct Hsc_ord as [[Hdom [Htrans [Hac Htot]]] Hincl];
destruct Hrf_wr1 as [Hrf_wr1 [Hpw_wr1 Hmax_wr1]];
  destruct Hws_wr2 as [Hso_wr2 [l2 [Hw_wr Hw_e2]]].
  destruct Hrf_wr1 as [Hevt_wr [Hevt_e2 [l1 [Hww_wr [Hr_e2 ?]]]]];
  destruct Hw_e2 as [Hevtb_e2 Hw_e2].
destruct (eqEv_dec e1 e2) as [Heq | Hdiff].
  rewrite Heq in Hr_e2.
  case_eq (action e2); unfold read_from in Hr_e2; unfold write_to in Hw_e2.
  intros d l v He2; rewrite He2 in Hr_e2; rewrite He2 in Hw_e2; case_eq d.
    intro Hr; rewrite Hr in Hw_e2; destruct Hw_e2 as [? Hw_e2]; inversion Hw_e2.
    intro Hw; rewrite Hw in Hr_e2; destruct Hr_e2 as [? Hr_e2]; inversion Hr_e2.
  assert (In _ (events E) e1) as He1.
    apply Hevt1.
  assert (In _ (events E) e2) as He2.
    apply Hevt2.
  generalize (Htot e1 e2 Hdiff He1 He2); intro Hor2.
  inversion Hor2 as [H12 | H21].
    exact H12.
    assert (wr = e2) as Heq.
      apply (Hmax_wr1 e2); split; auto.
      destruct Hw_e2 as [ve2 Hwe2];
      unfold In; unfold previous_writes; split; [ |split; auto].
      unfold writes; split; auto; exists l2; exists ve2; auto.
       destruct Hw_wr as [? [v2 Hwwr]];
       destruct Hpw_wr1 as [? [Hso Hlwr]]; unfold write_to in *;
       rewrite <- Hlwr; unfold loc; rewrite Hwwr; rewrite Hwe2; trivial.
       subst; generalize (Hac e2); intro Hc.
    contradiction.
Qed.

(** In any event structure, the preserved program order of [AWmm] is included in any sequential execution over this event structure *)

Lemma sc_ppo_in_so :
  forall E so,
  seq_exec E so ->
  rel_incl (ppo E) so.
Proof.
unfold rel_incl;
intros E so Hsc_ord e1 e2 Hin_c.
  destruct Hsc_ord as [Hlin Hincl]; apply Hincl.
  apply A.ppo_valid ; exact Hin_c.
Qed.

(** In any event structure, the sequence of:

- The reflexive closure of read-from
- The program order
- The reflexive closure of read-from

is included in any sequential execution over this event structure *)

Lemma rf_po_rf_in_so :
  forall E so x y,
  seq_exec E so ->
  rel_seq (maybe (rf (sc_witness E so)))
        (rel_seq (po_iico E) (maybe (rf (sc_witness E so)))) x y ->
  so x y.
Proof.
intros E so x y Hse [z [Hxz [e [Hze Hey]]]].
destruct Hse as [Hlin Hincl]; destruct_lin Hlin.
inversion Hxz as [Hrfxz | Heqxz]; inversion Hey as [Hrfey | Heqey].
  destruct Hrfxz as [? [[? [Hsoxz ?]] ?]] ; destruct Hrfey as [? [[? [Hsoey ?]] ?]].
  apply Htrans with z; split; auto. apply Htrans with e; split; auto.
  rewrite <- Heqey.
    destruct Hrfxz as [? [[? [Hsoxz ?]] ?]]; apply Htrans with z; split; auto.
  rewrite Heqxz.
    destruct Hrfey as [? [[? [Hsoey ?]] ?]]; apply Htrans with e; split; auto.
  rewrite Heqxz; rewrite <- Heqey; auto.
Qed.

(** For any event structure, the union of the barrier relation, write serialization, from-read relation, and preserved program order of the architecture [AWmm] is included in any sequential execution over this structure *)

Lemma bot_ghb_in_so :
  forall E so,
  seq_exec E so ->
  rel_incl (rel_union (abc E (sc_witness E so))
    (rel_union (rel_union (ws (sc_witness E so)) (fr E (sc_witness E so))) (ppo E))) so.
Proof.
unfold rel_incl; intros E so Hsc_ord e1 e2 Hx.
  inversion Hx as [Hab | Hrest].
  (*ab*)
  generalize Hsc_ord; intro Hse.
   destruct Hsc_ord as [Hlin ?]; destruct_lin Hlin.
    generalize (AwkAiSc); intros [? [? [? Habi]]].
    generalize (ab_sc_compat E (sc_witness E so) e1 e2 (Habi E (sc_witness E so) e1 e2 Hab));
    intro Hin.  apply (rf_po_rf_in_so E so e1 e2 Hse Hin).
    inversion Hrest as [Hws_fr | Hppo].
      inversion Hws_fr as [Hws | Hfr].
    (*ws*)
    generalize Hws; apply sc_ws_in_so.
  (*fr*)
    generalize Hfr; apply sc_fr_in_so; apply Hsc_ord.
  (*ppo*)
    generalize Hppo; apply sc_ppo_in_so; apply Hsc_ord.
Qed.

(** For any event structure, the global happens-before of the architecture [AWmm] is included in any sequential execution over this structure *)

Lemma sc_ghb_in_so :
  forall E so,
  seq_exec E so ->
  rel_incl (ghb E (sc_witness E so)) so.
Proof.
unfold rel_incl; intros E so Hsc_ord e1 e2 Hx.
case_eq inter; case_eq intra; unfold ghb in Hx.
  (*true, true*)
  intros Hintra Hinter; rewrite Hintra in Hx; rewrite Hinter in Hx.
  inversion Hx as [Hrf_inter | Hrest].
  (*rf_inter*)
  destruct Hrf_inter as [Hrf Hprocs].
  generalize Hrf; apply sc_rf_in_so.
    inversion Hrest as [Hrf_intra | Hres].
    (*rf_intra*)
    destruct Hrf_intra as [Hrf Hprocs].
    generalize Hrf; apply sc_rf_in_so.
    generalize Hres; apply (bot_ghb_in_so);
    apply Hsc_ord.
  (*true, false*)
  intros Hintra Hinter; rewrite Hintra in Hx; rewrite Hinter in Hx.
  inversion Hx as [Hrf_inter | Hrest].
  (*rf_inter*)
  destruct Hrf_inter as [Hrf Hprocs].
  generalize Hrf; apply sc_rf_in_so.
    generalize Hrest; apply (bot_ghb_in_so);
    apply Hsc_ord.
  (*false, true*)
  intros Hintra Hinter; rewrite Hintra in Hx; rewrite Hinter in Hx.
  inversion Hx as [Hrf_intra | Hrest].
  (*rf_intra*)
  destruct Hrf_intra as [Hrf Hprocs].
  generalize Hrf; apply sc_rf_in_so.
    generalize Hrest; apply (bot_ghb_in_so);
    apply Hsc_ord.
  (*false,false*)
  intros Hintra Hinter; rewrite Hintra in Hx; rewrite Hinter in Hx.
  generalize Hx; apply (bot_ghb_in_so);
  apply Hsc_ord.
Qed.

(** For any event structure, the global happens-before on the memory model [Awmm] is always acyclic on the execution witness extracted of the sequential execution *)

Lemma sc_exec_wf:
  forall E so,
  seq_exec E so ->
  acyclic (ghb E (sc_witness E so)).
Proof.
intros E so Hsc_ord.
eapply incl_ac.
- apply sc_ghb_in_so; auto.
- destruct Hsc_ord as [Hlin Hincl].
  eapply lin_strict_ac; apply Hlin.
Qed.

(** For any event structure, the execution witness extracted from any sequential execution over the event structure respects the out-of-[thin]-air condition *)

Lemma sc_exec_thin :
  forall E so,
  seq_exec E so ->
  acyclic (rel_union (so_rfm E so) (dp E)).
Proof.
intros E so Hsc x Hx.
assert (rel_incl (rel_union (so_rfm E so) (dp E)) so) as Hi.
  intros e1 e2 H12.
    inversion H12 as [Hrf | Hdp].
      generalize (sc_rf_in_so E so); intros Hi.
        unfold sc_witness in Hi; simpl in Hi; apply Hi; auto.
      destruct Hsc as [? Hpo]; apply Hpo.
      generalize (dp_valid E); intros [? ?]; auto.
assert (so x x) as Hc.
destruct Hsc as [Hlin ?].
  rewrite <- (lso_is_tc Hlin).
  generalize Hx; apply tc_incl; auto.
destruct Hsc as [Hlin ?].
destruct_lin Hlin.
apply (Hac x Hc).
Qed.

(** In a well-formed event structure, an execution witness extracted from any sequential execution over this structure is a valid execution on [AWmm].

I.e. an SC execution is valid on any architecture *)

Lemma sc_witness_valid:
  forall E so,
  well_formed_event_structure E ->
  seq_exec E so ->
  valid_execution E (sc_witness E so).
Proof.
intros E so Hwf Hsc_ord.
unfold valid_execution. simpl.
split.
(* write serialization is well-formed *)
{ eapply sc_ws_wf; auto. }
split.
(* read-from is well-formed *)
{ eapply sc_rf_wf; auto. }
split.
(* uniprocessor condition *)
{ eapply sc_hb_llh_wf; auto. }
split.
(* out-of-thin-air condition *)
{ eapply sc_exec_thin; auto. }
(* ghb is acyclic *)
{ apply sc_exec_wf; auto. }
Qed.

(** *** SC executions SC-check *)

(** For any event structure, the union of the program order and of the program order is included in any sequential execution over this structure *)

Lemma hb_po_in_so :
  forall E so,
  seq_exec E so ->
  rel_incl (rel_union (po_iico E)
    (hb E (sc_witness E so))) so.
Proof.
intros E so Hsc x y Hxy.
inversion Hxy.
  destruct Hsc as [? Hincl]; apply Hincl; auto.
  apply (hb_in_so E so Hsc x y H).
Qed.

(** For any event structure, the execution witness extracted from any sequential execution over this structure satisfies the [sc_check] condition *)

Lemma sc_witness_sc :
  forall E so,
  seq_exec E so ->
  sc_check E (sc_witness E so).
Proof.
intros E so Hsc; unfold sc_check.
eapply incl_ac.
  apply hb_po_in_so; auto.
  destruct Hsc as [Hlin ?]; generalize Hlin; intro Hl; destruct_lin Hlin;
  unfold acyclic; rewrite (lso_is_tc Hl); auto.
Qed.

End sc_valid.

(** *** Characterisation of an SC execution *)

Section sc_carac.

(** In a well-formed event structure with a well-formed execution witness, if:

- The union of the program order and of the happens-before relation is acyclic
- There exists a total order on the events of the event structure
- The union of the program order and of the happens-before relation is included in this total order

Then, the write serialization of the execution witness is the same as the one extracted from the total order after applying [sc_witness] on it *)

Lemma ac_po_hb_implies_same_ws :
  forall E X so,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  acyclic (rel_union (po_iico E) (hb E X))->
  linear_strict_order so (events E) ->
  rel_incl (rel_union (po_iico E) (hb E X)) so ->
  ws X = ws (sc_witness E so).
Proof.
intros E X so Hwf Hs Hacy Hlin Hincl.
generalize Hs; intros [Hwswf Hrfwf].
assert (forall x y, (ws X) x y <-> (ws (sc_witness E so)) x y) as Hext.
  split; intro Hin;
unfold sc_witness; unfold so_ws; simpl.
  split.
  apply Hincl; right; unfold hb;
  right; apply Hin.
  destruct_lin Hlin.
    generalize (ws_cands E X x y Hwswf Hin).
    intros [l [Hx Hy]]; exists l; split.
  split; destruct Hx as [Hudr Hwx]; auto.
  unfold udr; apply incl_union_left_in; exists y; apply Hincl; right; right; auto.

  split; destruct Hy as [Hudr Hwy]; auto.
  unfold udr; apply incl_union_right_in; exists x; apply Hincl; right; right; auto.

  unfold sc_witness in Hin; simpl in Hin.
  unfold so_ws in Hin;
  unfold udr in Hin.
  destruct Hin as [Hin [l Hm]];
 assert (In _ (writes_to_same_loc_l (events E) l) x /\
    In _ (writes_to_same_loc_l (events E) l) y) as Hmem.
  split; split; destruct Hm as [[Hx Hwx] [Hy Hwy]].
  destruct_lin Hlin.
  apply Hdr; auto.
  auto.
  destruct_lin Hlin.
  apply Hdr; auto.
  auto.
  destruct Hwswf as [Hws_tot Hws_cands].
  generalize (ws_tot E X (Hws_tot l) Hmem); intro Hor.
  assert (x <> y) as Hneq.
  destruct_lin Hlin.
    unfold not; intro Heq_xe; unfold acyclic in Hac; unfold not in Hac; apply (Hac x).
    rewrite <- Heq_xe in Hin; exact Hin.
  generalize (Hor Hneq); intro Horb.
  inversion Horb as [Hws_xe | Hws_ex].
    exact Hws_xe.
    assert (so y x) as Hin_ex.
      apply Hincl; unfold hb;
        right; right; exact Hws_ex.
    assert (~(acyclic so)) as Hcontrad.
      unfold acyclic; unfold not; intro Hcy; apply (Hcy x).
      eapply trc_ind with y; apply trc_step; [apply Hin | exact Hin_ex].
  generalize Hlin; intro Hli; destruct_lin Hlin; unfold acyclic in Hcontrad.
  generalize (lso_is_tc Hli); intro Heq; rewrite Heq in Hcontrad.
    contradiction.
apply (ext_rel (ws X) (ws (sc_witness E so)) Hext).
Qed.

Ltac destruct_lin H :=
  destruct H as [Hdr [Htrans [Hac Htot]]].

(** In well-formed event structure with an execution valid on the architecture [AWmm], if:

- There exists a total order on the events of the event structure
- The union of the program order and of the happens-before relation is included in this total order
- Two events are related by the read-from relation extracted from this total order

Then, these two events are related by the read-from relation of the execution.
*)

Lemma sc_rf_ax :
  forall E X so x y,
  well_formed_event_structure E ->
  valid_execution E X ->
  linear_strict_order so (events E) ->
  rel_incl (rel_union (po_iico E) (hb E X)) so ->
  so_rfm E so x y ->
  rf X x y.
Proof.
intros E X so x y Hwf Hv Hlin Hincl [Hrf [Hpw Hmax]].
generalize Hv; intro Hva.
assert (exists w, rf X w y) as Hrf_y.
  assert (In _ (reads E) y) as Hey.
    destruct Hrf as [? [Hey [l [? [Hry ?]]]]]; destruct_lin Hlin;
    split; [apply Hdr | exists l]; auto.
  destruct_valid Hv; generalize (Hrf_init y Hey); intros [w [Hor Hrfw]].
  exists w; auto.
destruct Hrf_y as [w Hrf_wy].
destruct (eqEv_dec w x)  as [Heq | Hdiff].
  subst; trivial.
  assert (ws X x w \/ ws X w x) as Hor.
    destruct Hpw as [[Hex [l Hwx]] [Hsoxy Hl]].
    assert (In _ (writes_to_same_loc_l (events E) l) x) as Hmx.
      split; auto.
    assert (In _ (writes_to_same_loc_l (events E) l) w) as Hmw.
      split; auto.
     destruct_lin Hlin; apply Hdr.
      apply incl_union_left_in; exists y; apply Hincl; right; left; left; auto.
      destruct Hrf as [? [? [ly [? [Hry ?]]]]]; destruct Hwx as [vx Hwx].
       unfold loc in Hl; rewrite Hwx in Hl; generalize Hry; intro Hy;
       destruct Hry as [vy Hry]; rewrite Hry in Hl; inversion Hl; auto.
      apply (rf_implies_same_loc w Hv Hrf_wy Hy).
    destruct_valid Hva; destruct_lin (Hws_tot l).
    generalize (Htot w x Hdiff Hmw Hmx); intro Horw.
    inversion Horw as [Hwswx | Hwsxw].
      destruct Hwswx; auto.
      destruct Hwsxw; auto.
  inversion Hor as [Hxw | Hwx].
  assert (so w y) as Hso_wy.
    apply Hincl; right; left; left; auto.
  assert (so x w) as Hso_xw.
    apply Hincl; right; right; auto.
  destruct_valid Hv.
  generalize (Hrf_cands w y Hrf_wy); intros [Hew [Hey [l [Hww [Hry ?]]]]].
  assert (exists e3 : Event, write_to e3 l /\ so x e3 /\ so e3 y) as Hcontrad.
    exists w; split; auto.
  assert (write_to x l) as Hwx.
    destruct Hrf as [? [? [l' [Hwx' [Hry' ?]]]]].
    rewrite (read_from_implies_same_loc Hry Hry'); auto.
    destruct Hcontrad as [e3 [[v3 Hwe3] [Hxe3 He3y]]].
    assert (x = e3) as Heq.
      apply (Hmax e3); split; auto.
      split; [unfold writes; split; [|exists l; exists v3; auto] |split; auto].
       destruct_lin Hlin; apply Hdr; apply incl_union_left_in; exists y; auto.
      destruct Hry as [vy Hry]; unfold loc; rewrite Hry; rewrite Hwe3; trivial.
      subst; destruct_lin Hlin; generalize (Hac e3); intro Hc; contradiction.

    assert (fr E X y x) as Hfr_yx.
      unfold fr; unfold frmaps; split; [|split; [| exists w]].
      assert (rfmaps_well_formed E (events E) (rf X)) as Hrfwf.
        destruct_valid Hv.
        split; auto.
      apply (ran_rf_in_events X w y Hwf Hrfwf Hrf_wy).
      assert (write_serialization_well_formed (events E) (ws X)) as Hwswf.
        destruct_valid Hv.
        split; auto.
      apply (ran_ws_in_events X w x Hwf Hwswf Hwx).
      auto.
      assert (so y x) as Hso_yx.
        apply Hincl; right; left; right; auto.
      destruct Hpw as [? [Hso_xy ?]].
  destruct_lin Hlin;
  assert (so y y) as Hso_yy.
    apply Htrans with x; auto.
  generalize (Hac y); intro Hc; contradiction.
Qed.

(** For any execution valid on [AWmm], the read-from relation is included in the happens-before relation *)

Lemma rf_in_hb :
  forall E X x y,
  valid_execution E X ->
  rf X x y ->
  hb E X x y.
Proof.
intros E X x y Hv Hrf.
left; left; auto.
Qed.

(** In well-formed event structure with a valid execution that verifies the [sc_check] condition, if there is a total order on the events of the event structure such that the union of the program order and of the happens-before relation is included in it, then the read-from relation we can extract from this total order is equal to the read-from relation of the execution witness *)

Lemma so_rfm_po_hb_is_rf :
  forall E X so,
  well_formed_event_structure E ->
  valid_execution E X ->
  sc_check E X ->
  linear_strict_order so (events E) ->
  rel_incl (rel_union (po_iico E) (hb E X)) so ->
  so_rfm E so = rf X.
Proof.
intros E X so Hwf Hvalid Hsc Hlin Hincl;
  apply (ext_rel (so_rfm E so) (rf X)); intros x y; split; intro Hxy.
    apply (sc_rf_ax E X so x y Hwf Hvalid Hlin Hincl Hxy).
  unfold so_rfm; split.
  split; generalize Hvalid; intro Hv; destruct_valid Hvalid.
  unfold udr; apply incl_union_left_in; exists y; apply Hincl; right; left; left; auto.
  split.
  unfold udr; apply incl_union_right_in; exists x; apply Hincl; right; left; left; auto.
  generalize (Hrf_cands x y Hxy); intros [Hex [Hey Hwxry]]; auto.

  split; [split; [|split] |].
  destruct_valid Hvalid; split; generalize (Hrf_cands x y Hxy);
  intros [Hex [Hey [l [[v Hwx] Hry]]]]; auto; exists l; exists v; auto.
  apply Hincl; right; left; left; auto.
  destruct_valid Hvalid; generalize (Hrf_cands x y Hxy);
  intros [Hex [Hey [l [[v Hwx] [[vy Hry] ?]]]]]; unfold loc;
  rewrite Hwx; rewrite Hry; auto.

  intros x' [[Hwx' [Hso_x'y Hloc]] Hso_xx'].
  generalize (eqEv_dec x x'); intros [Heq | Hdiff].
    exact Heq.
    generalize Hvalid; intro Hv; destruct_valid Hvalid.
    destruct Hwx' as [Hex' [l [v Hwx']]].

  assert (In _ (writes_to_same_loc_l (events E) l) x /\
  In _ (writes_to_same_loc_l (events E) l) x') as Hand.
  destruct_lin Hlin.
  split; split.
    apply Hdr; apply incl_union_left_in; exists x'; auto. auto.
    generalize (Hrf_cands x y Hxy); intros [? [? [lx [[vx Hx] [[vy Hy] ?]]]]].
    exists vx; unfold write_to; rewrite Hx.
    unfold loc in Hloc; rewrite Hwx' in Hloc; rewrite Hy in Hloc; inversion Hloc; trivial.
    apply Hdr; apply incl_union_right_in; exists x; auto.
    unfold write_to; exists v; auto.

    generalize (ws_tot E X (Hws_tot l) Hand Hdiff); intro Hor.
  inversion Hor.
      assert (fr E X y x') as Hfr_y3.
      split; [| split].
        eapply ran_rf_in_events; auto.
          split; auto. apply Hxy.
        eapply ran_ws_in_events; auto.
          split; auto. apply H.
        exists x; split; auto.
  assert (so y x') as Hso_y3.
    apply Hincl; right; left; right; auto.
  destruct_lin Hlin.
  assert (so x' y /\ so y x') as Ha.
    split; auto.
  generalize (Htrans x' y x' Ha); intro Hc.
  generalize (Hac x'); intro Hco; contradiction.
  assert (so x' x) as Hso_3x.
    apply Hincl; right; right; auto.
  assert (so x' x /\ so x x') as Ha.
    split; auto.
  destruct_lin Hlin.
  generalize (Htrans x' x x' Ha); intro Hc.
  generalize (Hac x'); intro Hco; contradiction.
Qed.

(** In a well-formed event structure with an execution valid on [AWmm], the domain and ranges of the union of the program order and of the happens-before relation are included in the set of events of the event structure *)

Lemma incl_udr_sc_check_in_events :
  forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
    Included _ (udr (rel_union (po_iico E) (hb E X))) (events E).
Proof.
intros E X Hwf Hv.
unfold udr; apply dom_ran_so_incl_po_hb; auto.
destruct_valid Hv; split; split; auto.
Qed.

(** In a well-formed event structure, if there exists an execution that:

- is valid on [AWmm]
- verifies the [sc_check] condition

Then there exists a sequential execution, from which we can extract a read-from relation and write serialization that are equal to the one of the execution valid on [AWmm]
*)

Lemma sc_carac :
  forall E rfm wsn,
  well_formed_event_structure E ->
  ((exists X, valid_execution E X /\ sc_check E X /\ (rf X) = rfm /\ (ws X) = wsn) <->
    (exists so, seq_exec E so /\ so_rfm E so = rfm /\ so_ws so = wsn)).
Proof.
intros E rfm wsn Hwf; split; intro Hsc;
  [destruct Hsc as [X [Hvalid [Hsc [Hrf Hws]]]] | destruct Hsc as [so [Hseq Hrf]]].
  generalize (incl_udr_sc_check_in_events E X Hwf Hvalid); intro Hinc.
  generalize (topo_ordering_correct Hinc Hsc); intros [so [Hlin Hincl]].
 exists so; unfold seq_exec; split;
    [split; [ | intros x y Hxy; apply Hincl; left; auto] | split].
auto.
rewrite (so_rfm_po_hb_is_rf E X so Hwf Hvalid Hsc Hlin Hincl); auto.
assert (write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X)) as Hs.
  destruct_valid Hvalid; split; split; auto.
rewrite <- Hws;
rewrite (ac_po_hb_implies_same_ws E X so Hwf Hs Hsc Hlin Hincl); auto.
(*rewrite <- Hsync;
rewrite (ac_po_hb_implies_same_synchro E X so Hwf Hs Hsc Hlin Hincl); auto.*)
exists (sc_witness E so); split;
  [apply sc_witness_valid; auto |
     split; [apply sc_witness_sc; auto | unfold sc_witness; simpl; auto]].
Qed.

End sc_carac.

End ScAx.

(** ** The SC memory model

The [ScModel] module defines the SC architecture, and prove somme lemmas about the memory model based on this architecture *)

Module ScModel.

(** *** The SC architecture *)

Module ScArch <: Archi.

(** The SC architecture preserves the whole program order *)

Definition ppo (E:Event_struct) := (po_iico E).

(** By definition of inclusion, the program order is included in itself *)

Lemma ppo_valid : forall E, rel_incl (ppo E) (po_iico E).
  unfold rel_incl; trivial.
Qed.

(** Given an event structure and a subset of its events, we can restrict the preserved program order to the elements of the event structure that belong to this subset *)

Lemma ppo_fun :
  forall E s x y,
  ppo E x y /\ s x /\ s y <->
  ppo (mkes (Intersection Event (events E) s) (rrestrict (iico E) s)) x y.
Proof.
unfold ppo; intros E s x y; split.
intros [Hppo [Hsx Hsy]].
inversion Hppo as [Hpo | Hiico].
  left; destruct Hpo as [? [? [? ?]]]; split; [|split; [|split]]; auto.
    simpl; split; auto.
    simpl; split; auto.
  right; simpl; split; [|split]; auto.

intro Hporr; inversion Hporr as [Hpo | Hiico].
  destruct Hpo as [? [? [Hex Hey]]].
  split; [|split].
    left; split; [|split; [|split]]; auto.
      destruct Hex; auto. destruct Hey; auto.
      destruct Hex; auto. destruct Hey; auto.

  destruct Hiico as [? [? ?]]; split; [right |split]; auto.
Qed.

(** All the read-froms are global in the SC architecture *)

Definition inter := true.
Definition intra := true.

(** We leave the barrier relation as a parameter of the architecture, but we postulate that it has the necessary properties as documented in [Archi] *)

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
  abc (mkes
   (Intersection Event (events E) s) (rrestrict (iico E) s))
    (mkew (rrestrict (ws X) s) (rrestrict (rf X) s)) x y).

Parameter stars : Event_struct -> set Event.
End ScArch.

(** Our SC memory model has no dependencies between the events. It is not necessary to take them into account because no reordering can be performed and thus no dependency might be broken, because the dependency ordering must be compatible with the program order *)

Definition dp (E:Event_struct) := fun e1:Event => fun e2:Event => False.

(** The empty relation is trivially included in the program order for any event structure *)

Lemma dp_valid : forall E, rel_incl (dp E) (po_iico E).
  unfold rel_incl; intros; inversion H.
Qed.

Import ScArch.

(** We import the basic facts about the SC architecture *)

Module ScBasic := Basic ScArch dp.
Import ScBasic.

(** We create a memory model based on the SC architecture *)

Module ScWmm := Wmm ScArch dp.
Import ScWmm.

(** We import the basic facts about sequential executions on the SC architecture *)

Module ScAx := ScAx ScArch.
Import ScAx.

(** For any event structure, the program order is included in the preserved program order of the SC architecture *)

Lemma po_is_ppo_po :
  forall E e1 e2,
  po_iico E e1 e2 ->
  (ppo E) e1 e2.
Proof.
intros E e1 e2 Hpo;
apply Hpo.
Qed.

(** For any event structure, the union of the program order and of the happens-before relation is included in the global happens-before relation of the SC architecture *)

Lemma po_hb_in_ghb :
  forall E X,
  rel_incl (rel_union (po_iico E) (hb E X)) (ghb E X).
Proof.
intros E X x y Hxy.
inversion Hxy.
right; right; right; right; apply po_is_ppo_po; auto.
inversion H.
  inversion H0.
    destruct (eqProc_dec (proc_of x) (proc_of y)) as [Heq | Hdiff].
      right; left; split; auto.
      left; split; auto.
    right; right; right; left; right; auto.
    right; right; right; left; left; auto.
Qed.

(** In well-formed event structure, any execution valid on the SC architecture verifies the [sc_check] condition *)

Lemma exec_sc_check :
  forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
  sc_check E X.
Proof.
unfold sc_check;
intros E X Hwf Hvalid.
destruct_valid Hvalid.
generalize (po_hb_in_ghb); intro Hincl.
apply (incl_ac (Hincl E X)); auto.
Qed.

(** In a well-formed event structure, if there is a sequential execution over the event structure, then there is an execution witness valid on the SC architecture, and their read-from relations and write serializations are equal *)

Lemma sc_is_sc :
  forall E rfm wsn,
  well_formed_event_structure E ->
  ((exists so, seq_exec E so /\ so_rfm E so = rfm /\ so_ws so = wsn) <->
    (exists X, (*ScWmm.*)valid_execution E X /\ (rf X) = rfm /\ (ws X) = wsn)).
Proof.
intros E rfm wsn Hwf; split; intro Hex.
  destruct Hex as [so [Hseq [Hrf Hws]]].
  exists (sc_witness E so); split.
  apply sc_witness_valid;
    [apply Hwf | apply Hseq].
  unfold sc_witness; simpl; auto.
  generalize (sc_carac E rfm wsn Hwf); intros [dir bak].
  apply dir; destruct Hex as [X [? ?]]; exists X; split; [auto | split; auto].
  apply exec_sc_check; auto.
Qed.

End ScModel.

(** ** An alternative SC model enforced by barriers

The goal of this module is to build an architecture on which only SC executions are valid, no matter what the preserved program order and/or global read-from of this architecture are. This will be achieved by having a barrier relation that strictly enforces the program order and the potential read-froms *)

Module ABTh (A:Archi).

(** We consider an arbitrary architecture, the basic facts associated to it and the memory model based on it *)

Module ABasic := Basic A dp.
Import ABasic.
Import A.
Module AWmm := Wmm A dp.
Import AWmm.

(** *** The SC-enforcing barrier relation

We define a barrier relation that enforces the order between:

- [e1] and [e2] if [e1] must occur before [e2] according to program order.
- An event [e] and a read [r], if there is a write [w] such that [e] must occur before [w] according to the program order and [r] reads the value written by [w]
- A write [w] and an event [e], if there is a read [r] such that [r] reads the value written by [w] and [r] must occur before [e] according to the program order *)

Inductive ABTh (E:Event_struct) (X:Execution_witness) : Event -> Event -> Prop :=
  | Base : forall e1 e2, (*events E e1 -> events E e2 ->*)
      (po_iico E) e1 e2 -> ABTh E X e1 e2
  | Right : forall e1 w2 r2, (*events E e1 -> events E w2 -> events E r2 ->*)
      po_iico E e1 w2 /\ (rf X) w2 r2 -> ABTh E X e1 r2
  | Left : forall w1 r1 e2, (*events E w1 -> events E r1 -> events E e2 ->*)
      (rf X) w1 r1 /\ po_iico E r1 e2 -> ABTh E X w1 e2.

(** *** The alternative SC architecture *)

Module SyncTh <: Archi.

(** The preserved program order is arbitrary but it respect the properties defined in [Archi] *)

Parameter ppo : Event_struct -> Rln Event.
Hypothesis ppo_valid : forall E, rel_incl (ppo E) (po_iico E).
Hypothesis ppo_fun :
  forall E s x y,
  ppo E x y /\ s x /\ s y <->
  ppo (mkes (Intersection Event (events E) s) (rrestrict (iico E) s)) x y.

(** The global read-from relation is arbitrary *)

Parameter intra : bool.
Parameter inter : bool.

(** The barrier relation is [ABTh], documented just above. *)

Definition abc := ABTh.

(** In a well-formed event structure with a well-formed read-from relation, the events ordered by [ABTh] belong to the set of events of the event structure *)

Lemma ab_evts : forall (E:Event_struct) (X:Execution_witness),
  forall x y, well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  abc E X x y -> In _ (events E) x /\ In _ (events E) y.
Proof.
 intros E X x y Hwf Hrfwf Hxy; split; induction Hxy; auto.
   apply ABasic.po_iico_domain_in_events with e2; auto.
   destruct H; apply ABasic.po_iico_domain_in_events with w2; auto.
   destruct H; apply ABasic.dom_rf_in_events with X r1; auto.

   apply ABasic.po_iico_range_in_events with e1; auto.
   destruct H; apply ABasic.ran_rf_in_events with X w2; auto.
   destruct H; apply ABasic.po_iico_range_in_events with r1; auto.
Qed.

(** For any event structure and execution witness, [ABTh] is included in the transitive closure of the union of the happens-before relation and of the program order *)

Lemma ab_incl :
  forall E X, rel_incl (abc E X) (tc (rel_union (hb E X) (po_iico E))).
Proof.
intros E X x y Hxy.
induction Hxy as [x y z Hnc | x y z Hac | x y z Hbc].
  apply trc_step; right; auto.
  destruct Hac as [Hpoa Hrfa].
      apply trc_ind with y; apply trc_step; [right | left]; auto.
        left; left; auto.
  destruct Hbc as [Hrfb Hpob].
      apply trc_ind with y; apply trc_step; [left | right]; auto.
        left; left; auto.
Qed.

(** It is not exactly clear what this represents, and it seems to be left as a parameter everywhere. Needs further documentation *)

(*
Hypothesis ab_fun :
  forall E X s x y,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  (abc E X x y /\ s x /\ s y <->
  abc (mkes
     (Intersection Event (events E) s) (rrestrict (iico E) s))
    (mkew (rrestrict (ws X) s) (rrestrict (rf X) s)) x y).
*)

(*
Lemma ab_fun :
  forall E X s x y,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  (abc E X x y /\ s x /\ s y <->
  abc (mkes
     (Intersection Event (events E) s) (rrestrict (iico E) s))
    (mkew (rrestrict (ws X) s) (rrestrict (rf X) s)) x y).
Proof.
intros E X s x y Hwf Hrfwf; split.
  intros [Hxy [Hx Hy]].
  induction Hxy as [x y z Hnc | x y z Hac | x y z Hbc].
    apply Base; simpl.
      apply ABasic.po_rr; auto.

  apply Right with y.
  generalize (excluded_middle (s y)); intros [Hin | Hnin];
      destruct Hac; simpl; auto.
        split. apply ABasic.po_rr; auto.
        split; auto.
        assert (wmm.init (mkes (fun w : Event =>
           (exists e : Event, rf X w e /\ s e /\ ~ s w) \/ init w)
   (Intersection Event (events E) s) (rrestrict (iico E) s) final) y) as Hiw.
                    simpl; left; exists z; split; [|split]; auto.
      generalize (ABasic.po_iico_domain_in_events Hwf H); intro Hex.
      generalize (ABasic.po_iico_range_in_events Hwf H); intro Hey.
      generalize (ABasic.po_implies_same_proc Hwf Hex Hey H); intro Heqp.
      assert (events
    (mkes
       (fun w : Event =>
        (exists e : Event, rf X w e /\ s e /\ ~ s w) \/ init w)
       (Intersection Event (events E) s) (rrestrict (iico E) s) final) x) as Herx.
        simpl; split; auto.
     generalize (init_po (mkes
     (fun w : Event =>
      (exists e : Event, rf X w e /\ s e /\ ~ s w) \/ init w)
     (Intersection Event (events E) s) (rrestrict (iico E) s) final)
     y Hiw x Herx Heqp); intro Hpoyx.
      generalize (ABasic.po_rr_bak Hwf Hpoyx); intro Hpo.
      assert (po_iico E x x) as Hpox.
        apply ABasic.po_trans with y; auto.
      generalize (ABasic.po_ac Hwf Hpox); intro Ht; inversion Ht.

  apply Left with y.
  generalize (excluded_middle (s y)); intros [Hin | Hnin];
      destruct Hbc; simpl; auto.
        split; auto. split; auto.
        apply ABasic.po_rr; auto.
        assert (wmm.final (mkes init
  (Intersection Event (events E) s) (rrestrict (iico E) s)
    (fun r : Event => (exists w : Event, rf X w r /\ s w /\ ~ s r) \/ wmm.final E r)
    ) y) as Hfy.
                    simpl; left; exists x; split; [|split]; auto.
      generalize (ABasic.po_iico_domain_in_events Hwf H0); intro Hey.
      generalize (ABasic.po_iico_range_in_events Hwf H0); intro Hez.
      generalize (ABasic.po_implies_same_proc Hwf Hey Hez H0); intro Heqp.
      assert (events
    (mkes
       (fun w : Event =>
        (exists e : Event, rf X w e /\ s e /\ ~ s w) \/ init w)
       (Intersection Event (events E) s) (rrestrict (iico E) s)
(fun r : Event => (exists w : Event, rf X w r /\ s w /\ ~ s r) \/ wmm.final E r)
       ) z) as Herz.
        simpl; split; auto.
     assert (proc_of z = proc_of y) as Heqp'.
       auto.
     generalize (final_po (mkes
     (fun w : Event =>
      (exists e : Event, rf X w e /\ s e /\ ~ s w) \/ init w)
     (Intersection Event (events E) s) (rrestrict (iico E) s)
(fun r : Event => (exists w : Event, rf X w r /\ s w /\ ~ s r) \/ wmm.final E r)
)
     y Hfy z Herz Heqp'); intro Hpozy.
      generalize (ABasic.po_rr_bak Hwf Hpozy); intro Hpo.
      assert (po_iico E z z) as Hpoz.
        apply ABasic.po_trans with y; auto.
      generalize (ABasic.po_ac Hwf Hpoz); intro Ht; inversion Ht.

intro Hxy; split; induction Hxy.
  apply Base.
    apply ABasic.po_rr_bak with (fun w => (exists e, rf X w e /\ s e /\ ~ s w ) \/ init w) final s; auto.

  apply Right with w2; destruct H.
    split.
      apply ABasic.po_rr_bak with (fun w => (exists e, rf X w e /\ s e /\ ~ s w ) \/ init w) final s; auto.
      destruct H0; auto.

  apply Left with r1; destruct H.
    split.
      destruct H; auto.
      apply ABasic.po_rr_bak with (fun w => (exists e, rf X w e /\ s e /\ ~ s w ) \/ init w) final s; auto.

      apply ABasic.po_rr_bak_s with E final s; auto.

      destruct H as [? ?]; auto.
      generalize (ABasic.po_rr_bak_s Hwf H); intros [? ?]; split; auto.
      destruct H0 as [? [? ?]]; auto.

      destruct H as [? ?]; auto.
      generalize (ABasic.po_rr_bak_s Hwf H0); intros [? ?]; split; auto.
      destruct H as [? [? ?]]; auto.
Qed.  *)

Parameter stars : Event_struct -> set Event.
End SyncTh.

(** We consider an arbitrary dependency relation *)

Parameter dp : Event_struct -> Rln Event.

Hypothesis dp_valid : forall E, rel_incl (dp E) (po_iico E).

Import SyncTh.

(** We import the basic facts about our alternative SC architecture *)

Module SyncThBasic := Basic SyncTh dp.
Import SyncThBasic.

(** We build a memory model on this architecture *)

Module SyncThWmm := Wmm SyncTh dp.
Import SyncThWmm.

(** We import facts about sequential executions over our alternative SC memory model *)

Module SyncThAx := ScAx SyncTh.
Import SyncThAx.

(** We import our first SC memory model *)

Import ScModel.

(** In a well-formed event structure with an execution valid on the alternative SC memory model, the sequence of the happens-before relation and of the program order is included in the union of:

- the sequence of the union of write serialization and from-read, and of [ABTh]
- [ABTh] *)

Lemma hb_seq_pb_incl_ws_u_fr_seq_ab :
  forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
  rel_incl (rel_seq (hb E X) (pb E)) (rel_union (rel_seq (rel_union (ws X) (fr E X)) (abc E X)) (abc E X)).
Proof.
intros E X Hwf Hv x y [z [Hhb_xz Hpo_zy]].
  inversion Hhb_xz as [Hrf_fr | Hws].
    inversion Hrf_fr as [Hrf | Hfr].
   right;
   eapply Left with z.
     split; [apply Hrf | apply Hpo_zy].
(*        eapply Base.
     change (events E z) with (In _ (events E) z); eapply po_iico_domain_in_events; auto.
       apply Hpo_zy.
     change (events E y) with (In _ (events E) y); eapply po_iico_range_in_events; auto.
       apply Hpo_zy.
    auto. *)
    left; exists z; split; [right; apply Hfr|].
     eapply Base.
       apply Hpo_zy.
 (* auto. *)
    left; exists z; split; [left; apply Hws|].
    eapply Base.
       apply Hpo_zy.
  (* auto. *)
Qed.

(** In a well-formed event structure with an execution valid on the alternative SC memory model, the sequence of write serializaton, read-from and program order is included in the sequence of the union of write serialization and from-read, and of [ABTh] *)

Lemma wsrf_seq_pb_incl_ws_u_fr_seq_ab :
  forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
  rel_incl (rel_seq (rel_seq (ws X) (rf X)) (pb E)) (rel_seq (rel_union (ws X) (fr E X)) (abc E X)).
Proof.
intros E X Hwf Hv x y [z [ [e [Hws_xe Hrf_ez]] Hpo_zy]].
exists e; split; [left; auto |].
eapply Left with z.
 split; auto.

(* apply Hrf_ez.
     change (events E z) with (In _ (events E) z); eapply ran_rf_in_events; auto.
       destruct_valid Hv; split; auto. apply Hrf_ez.
     change (events E y) with (In _ (events E) y); eapply po_iico_range_in_events; auto.
       apply Hpo_zy.
   split;
      [apply Hrf_ez | (*eapply Base*) apply Hpo_zy].
   (*  change (events E z) with (In _ (events E) z); eapply po_iico_domain_in_events; auto.
       apply Hpo_zy.
     change (events E y) with (In _ (events E) y); eapply po_iico_range_in_events; auto.
       apply Hpo_zy.
auto. *) *)
Qed.

(** In a well-formed event structure with an execution valid on the alternative SC memory model, the sequence of from-read, read-from and program order is included in the sequence of the union of write serialization and from-read, and of [ABTh] *)

Lemma frrf_seq_pb_incl_ws_u_fr_seq_ab :
  forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
  rel_incl (rel_seq (rel_seq (fr E X) (rf X)) (pb E)) (rel_seq (rel_union (ws X) (fr E X)) (abc E X)).
Proof.
intros E X Hwf Hv x y [z [ [e [Hfr_xe Hrf_ez]] Hpo_zy]].
exists e; split; [right; auto |].
eapply Left with z.
(*     change (events E e) with (In _ (events E) e); eapply dom_rf_in_events; auto.
       destruct_valid Hv; split; auto. apply Hrf_ez.
     change (events E z) with (In _ (events E) z); eapply ran_rf_in_events; auto.
       destruct_valid Hv; split; auto. apply Hrf_ez.
     change (events E y) with (In _ (events E) y); eapply po_iico_range_in_events; auto.
       apply Hpo_zy.*)
     split;
      [apply Hrf_ez | (*eapply Base*) apply Hpo_zy].
(*     change (events E z) with (In _ (events E) z); eapply po_iico_domain_in_events; auto.
       apply Hpo_zy.
     change (events E y) with (In _ (events E) y); eapply po_iico_range_in_events; auto.
       apply Hpo_zy.
 auto. *)
Qed.

(** In a well-formed event structure with an execution valid on the alternativ SC memory model, the sequence of [hb'] and program order is included in the union of:

- the sequence of the union of write serialization and from-read, and of the [ABTh]
- [ABTh] *)

Lemma hb'_seq_po_incl_ws_u_fr_seq_ab :
  forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
  (rel_incl (po_iico E) (pb E)) ->
  rel_incl (rel_seq (hb' E X) (po_iico E)) (rel_union (rel_seq (rel_union (ws X) (fr E X)) (abc E X)) (abc E X)).
Proof.
intros E X Hwf Hv Hincl x y Hxy.
destruct Hxy as [z [Hhb'_xz Hpo_zy]].
generalize (Hincl z y Hpo_zy); intro Hpb_zy.
inversion Hhb'_xz as [Hhb_wsrf | Hfr_rf_xz].
  inversion Hhb_wsrf as [Hhb_xz | Hwsrf_xz].
    assert (rel_seq (hb E X) (pb E) x y) as Hhb_pb_xy.
      exists z; auto.
    apply (hb_seq_pb_incl_ws_u_fr_seq_ab E X Hwf Hv x y Hhb_pb_xy).
    assert (rel_seq (rel_seq (ws X) (rf X)) (pb E) x y) as Hwsrf_pb_xy.
      exists z; auto.
    left; apply (wsrf_seq_pb_incl_ws_u_fr_seq_ab E X Hwf Hv x y Hwsrf_pb_xy).
    assert (rel_seq (rel_seq (fr E X) (rf X)) (pb E) x y) as Hfrrf_pb_xy.
      exists z; auto.
    left; apply (frrf_seq_pb_incl_ws_u_fr_seq_ab E X Hwf Hv x y Hfrrf_pb_xy).
Qed.

(** In a well-formed event structure with an execution valid on the alternative SC memory model, the transitive closure of the sequence of [hb'] and of the program order is included in the union of:

- the sequence of the union of write serialization and from-read, and of [ABTh]
- [ABTh] *)

Lemma hb'_seq_po_path_implies_ws_u_fr_seq_ab_path :
  forall E X x y,
  well_formed_event_structure E ->
  valid_execution E X ->
  (rel_incl (po_iico E) (pb E)) ->
  tc (rel_seq (hb' E X) (po_iico E)) x y ->
  tc (rel_union (rel_seq (rel_union (ws X) (fr E X)) (abc E X)) (abc E X)) x y.
Proof.
intros E X x y Hwf Hv Hincl Htc.
induction Htc.
  apply trc_step; apply (hb'_seq_po_incl_ws_u_fr_seq_ab E X Hwf Hv Hincl x y H).
  apply trc_ind with z; auto.
Qed.

(** In a well-formed event structure with an execution valid on the alternative SC memory model, the union of the happens-before relation and of the program order is acyclic *)

Lemma po_in_pb_implies_ac_hb_po : (*this is the real important lemma*)
  forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
  (rel_incl (po_iico E) (pb E)) ->
  acyclic (rel_union (hb E X) (po_iico E)).
Proof.
intros E X Hwf Hvalid Hincl.
unfold acyclic; unfold not; intros x Hx.
assert (write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X)) as Hs.
  destruct_valid Hvalid; split; split; auto.
generalize (hb_union_po_cycle_implies_hb'_seq_po_cycle Hwf Hs Hx); intro Hy.
destruct Hy as [y Hy].
generalize (hb'_seq_po_path_implies_ws_u_fr_seq_ab_path E X y y Hwf Hvalid Hincl Hy); intro Hp.
generalize (ws_u_fr_seq_ab_path_implies_ghb_path Hwf Hvalid Hp); intro Hc.
destruct_valid Hvalid.
unfold acyclic in Hvalid; apply (Hvalid y Hc).
Qed.

(** In a well-formed event structure with an execution valid on our alternative SC memory model, there exists a sequential execution on the event structure from which we can extract a read-from relation and a write serialization that are equal to the ones of the execution valid on the alternative SC memory model *)

Lemma barriers_provide_sc_exec :
  forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
  (rel_incl (po_iico E) (pb E)) ->
  (exists so, (seq_exec E so) /\ (so_rfm E so = rf X) /\ so_ws so = ws X).
Proof.
intros E X Hwf Hvalid Hpo_in_pb.
generalize (po_in_pb_implies_ac_hb_po E X Hwf Hvalid Hpo_in_pb); intro Hac.
  generalize (sc_carac E (rf X) (ws X) Hwf); intros [dir bak].
apply dir; exists X; split; [auto | unfold sc_check; split; auto].
rewrite (union_triv (po_iico E) (hb E X)); auto.
Qed.

End ABTh.

End Sc.
