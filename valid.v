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
Import OEEvt.
Set Implicit Arguments.

(** * Validity

The module [Valid] is very similar to the module [Sc]. 

In [SC], we defined the notion of sequential execution as a total order on the events of an event structure, and we extracted a SC execution witness from it. The notion of sequential execution was totally independent from any architecture.

In [Valid], we define the notion of partial execution, valid on a given architecture, as a partial order on the events of an event structure. We then show how to extract an execution witness valid on this architecture from the valid partial execution *)

Module Valid (A:Archi) (dp : Dp).

(** We suppose that for any event structure, the dependency relation is included in the preserved program order *)

Import dp.

Hypothesis dp_ppo :
  forall E, rel_incl (dp E) (A.ppo E).

(** ** Definitions *)

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

(** A partial order on the events of an event structure is a valid partial execution on the architecture A if the preserved program order and the per-location program order are both included in the linear extension of this partial order *)

Definition vexec (E:Event_struct) (so:Rln Event) : Prop :=
  partial_order so (events E) /\
  acyclic (rel_union (A.ppo E) (LE so)) /\
  acyclic (rel_union (pio_llh E) (LE so)).

(** ** Building a valid execution witness

We build an execution witness valid on [A] from a valid partial execution on the events of an event structure *)

(** *** read-from of a valid partial execution *)

(** Two events are related by the read-from relation extracted from the valid partial execution if:

- they are events from the domain or the range of the linear extension of the valid partial execution
- the first one is a write event and the second one is a read event
- they access the same location
- they read/write the same value
- the first event belongs to the maximal elements of the previous writes (w.r.t. to the valid partial execution) of the second event. Simply put, the first event
is the most recent write before the second event in the valid partial execution *)

Definition so_rfm (E:Event_struct) (so : Rln Event) :=
  fun ew => fun er =>
    (rfmaps (udr (LE so))) ew er /\
    (maximal_elements
       (previous_writes E (LE so) er) (LE so)) ew.

(** For any partial order on an event structure, for every read event in this structure, there is a write such that the read-from extracted from the valid partial execution relates the write event to the read event *)

Hypothesis so_rfm_init :
  forall E so,
  forall er, In _ (reads E) er ->
    exists ew, (In _ (events E) ew /\ so_rfm E so ew er)
      (*\/ (init E ew)*).

(** *** write serialization of sequential execution *)

(** Two events are related by the write serialization extracted from the valid partial execution if:

- They are related by the valid partial execution
- They are both writes to the same location *)

Definition so_ws (so:Rln Event) : (Rln Event) :=
    fun e1 => fun e2 =>
    LE so e1 e2 /\
    exists l, In _ (writes_to_same_loc_l (udr (LE so)) l) e1 /\
      In _ (writes_to_same_loc_l (udr (LE so)) l) e2.

(** ** Valid partial execution synchronisation

[so_sync] is the intersection between the valid partial execution and a relation [synchro] given as a parameter
*)

Definition so_sync (so:Rln Event) (synchro:Rln Event) : Rln Event :=
  fun e1 e2 => so e1 e2 /\ synchro e1 e2.

(** ** Definition of a valid execution witness

Given a valid partial execution on an event structure, we can build an execution witness valid on [A] by combining the read-from relation extracted using [so_rfm] and the write serialization extracted using [so_ws]
 *)

Definition vwitness (E:Event_struct) (so:Rln Event) : Execution_witness :=
  mkew (so_ws so) (so_rfm E so).

(** ** An A-compatible architecture

The definition of [AiSc] is exactly the same as the one of its module type [Archi], but it adds an extra hypothesis [ab_sc_compat]. The goal of this extra hypothesis is to ensure that the barrier relation will not enforce an ordering on events that would be incoherent with the architecture [A] *)

Module AiSc <: Archi.

(** The preserved program order is arbitrary but it respects the properties defined in [Archi] *)

Parameter ppo : Event_struct -> Rln Event.

Hypothesis ppo_valid : forall E, rel_incl (ppo E) (po_iico E).

Hypothesis ppo_fun :
  forall E s x y,
  ppo E x y /\ s x /\ s y <->
  ppo (mkes (Intersection Event (events E) s) (rrestrict (iico E) s)) x y.

(** The global read-from is arbitrary *)

Parameter inter : bool.
Parameter intra : bool.

(** The barrier relation is arbitrary but it respects the properties defined in [Archi] and the extra hypothesis [ab_sc_compat] *)

Parameter abc  : Event_struct -> Execution_witness -> Rln Event.

(** The barrier relation must be included in the sequence of:

- The reflexive closure of read-from
- The preserved program order of [A]
- The reflexive closure of read-from

This condition disallows the three following scenarios:

- An event [e1] must occur before an event [e2] according to the barrier, but [e2] must occur before [e1] according to the preserved program order.
- An event [e] must occur before a write [w] according to the barrier, and a read [r] that reads the value written by [w] must occur before [e] according to the preserved program order.
- An read [r] must occur before an event [e] according to the barrier and reads a value written by a write [w], but [w] must occur after [e] according to preserved program order.
*)

Parameter ab_sc_compat :
  forall E X, rel_incl (abc E X) (rel_seq (maybe (rf X)) (rel_seq (A.ppo E) (maybe (rf X)))).

Hypothesis ab_evts : forall (E:Event_struct) (X:Execution_witness),
  forall x y, well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  abc E X x y -> In _ (events E) x /\ In _ (events E) y.

Hypothesis ab_incl :
  forall E X, rel_incl (abc E X) (tc (rel_union (com E X) (po_iico E))).

Hypothesis ab_fun :
  forall E X s x y,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  (abc E X x y /\ s x /\ s y <->
  abc (mkes
   (Intersection Event (events E) s) (rrestrict (iico E) s))
    (mkew (rrestrict (ws X) s) (rrestrict (rf X) s)) x y).

Parameter stars : Event_struct -> set Event.

End AiSc.

Import AiSc.

(** ** Lemmas about the executions on A 

The module [ScAx] contains definitions of properties about the executions on A *)

Module ScAx.

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
Module ABasic := Basic A dp.
Import ABasic.
Module AWmm := Wmm A dp.
Import AWmm.
Import A.

(** [ahb] is another name for [mhb] *)

Definition ahb E X :=
  rel_union (rel_union (AWmm.mrf X) (fr E X)) (ws X).

(** We define the [sc_check] condition, which is the acyclicity of the preserved program order and the [ahb] relation. This union corresponds to [ghb] except for the barriers that are missing. 

But we assumed in [ab_sc_compat] that our barrier relation was included in the preserved program order, so the acyclicity of the preserved program order implies the acyclicity of the barrier relation.

Hence [sc_check] is equivalent to the global happens-before acyclicity check in the definition of a valid execution *)

Definition sc_check (E:Event_struct) (X:Execution_witness) : Prop :=
  acyclic (rel_union (A.ppo E) (ahb E X)).

(** *** Validity of an execution 

We show that an execution extracted from a valid partial execution for an architecture [A] is valid on the memory model based on architecture [A] *)

Section sc_valid.

(** The domain and the range of a write serialization extracted from a valid partial execution are included in the events of the event structure of this valid partial execution *)

Lemma so_ws_dom_ran_wf :
  forall E so l,
  vexec E so ->
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

(** The write serialization extracted from a valid partial execution is a well-formed write serialization *)

Lemma sc_ws_wf :
  forall E so,
  vexec E so ->
  write_serialization_well_formed (events E) (so_ws so).
Proof.
intros E so Hsc_ord; split.
(*lin*)
intro l;split.
  (*dom/ran*)
  eapply (so_ws_dom_ran_wf). apply Hsc_ord.
  destruct Hsc_ord as [Hpart Hincl].
  assert (Included _ (events E) (events E)) as Htriv.
    intros x Hx; auto.
    generalize (OE Htriv Hpart); intros [Hinc Hle].
  destruct_lin Hle.
  split.
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
  destruct Hsc_ord as [Hpart Hincl].
  assert (Included _ (events E) (events E)) as Htriv.
    intros y Hy; auto.
    generalize (OE Htriv Hpart); intros [Hinc Hle].
  destruct_lin Hle.
destruct Hws as [Hso [l [[Hex Hwx] [Hee Hwe]]]]; exists l; split;
  unfold In; unfold writes_to_same_loc_l.
  split; [apply Hdr; apply Hex |apply Hwx].
  split; [apply Hdr; apply Hee |apply Hwe].
Qed.

Ltac destruct_lin H :=
  destruct H as [Hdr [Htrans [Hac Htot]]].

(** The read-from relation extracted from a valid partial execution is a well-formed read-from relation *)

Lemma sc_rf_wf :
  forall E so,
  vexec E so ->
  rfmaps_well_formed E (events E) (so_rfm E so).
Proof.
intros E so Hsc_ord; unfold rfmaps_well_formed; split.
  destruct Hsc_ord as [Hpart Hincl].
  assert (Included _ (events E) (events E)) as Htriv.
    intros x Hx; auto.
    generalize (OE Htriv Hpart); intros [Hinc Hle].
  destruct_lin Hle.
  intros er Her; generalize (so_rfm_init E so er Her);
  intros [ew [Hew Hrf]]; exists ew.
 split; auto.
 split; [intros e1 e2 H12 | ].
destruct H12 as [Hso12 [Hrf12 Hno12]].
  destruct Hsc_ord as [Hpart Hincl].
  assert (Included _ (events E) (events E)) as Htriv.
    intros x Hx; auto.
    generalize (OE Htriv Hpart); intros [Hinc Hle].
  destruct_lin Hle.
unfold rfmaps.
destruct Hrf12 as [[Hevt1 Hw1] [Hso Heq]].
destruct Hso12 as [H1 [H2 Hl]].
split; [ | split; [|apply Hl]].
apply Hevt1.
apply Hdr; apply H2.
intros x w1 w2 [Hrf_w1x [Hpw_w1x Hmax_w1x]] [Hrf_w2x [Hpw_w2x Hmax_w2x]].
destruct (eqEv_dec w1 w2) as [Hy | Hn].
    apply Hy.
    assert (LE so w1 w2 \/ LE so w2 w1) as Hor.
  destruct Hsc_ord as [Hpart Hincl].
  assert (Included _ (events E) (events E)) as Htriv.
    intros y Hy; auto.
    generalize (OE Htriv Hpart); intros [Hinc Hle].
  destruct_lin Hle.
      apply (Htot w1 w2 Hn).
        destruct Hpw_w1x as [[Hew1 ?] ?]; apply Hew1.
        destruct Hpw_w2x as [[Hew2 ?] ?]; apply Hew2.
      inversion Hor as [H12 | H21].
        apply (Hmax_w1x w2); split; auto.
        apply sym_eq; apply (Hmax_w2x w1); split; auto.
Qed.

(** The communication relation extracted from a valid partial execution is included in the linear extension of the valid partial execution *)

Lemma com_in_so :
  forall E so,
  vexec E so ->
  rel_incl (com E (vwitness E so)) (LE so).
Proof.
unfold rel_incl; intros E so Hsc_ord x y Hhb.
inversion Hhb as [Hrf_fr | Hws]; unfold vwitness in *; simpl in *.
  inversion Hrf_fr as [Hrf | Hfr].
  (*in rf*)
    destruct Hrf as [Hrf [[? [Hso ?]] ?]]; apply Hso.
  (*in fr*)
    destruct Hfr as [Hx [Hy [wr [Hwrx Hwry]]]]; simpl in *.
  destruct Hsc_ord as [Hpart Hincl].
  assert (Included _ (events E) (events E)) as Htriv.
    intros e He; auto.
    generalize (OE Htriv Hpart); intros [Hinc Hle].
  destruct_lin Hle.
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
   apply Hdr; apply Hso_x.
  assert (In _ (events E) y) as He2.
    apply Hdr; apply Hevt_y.
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

(** For any given location, there are no conflicts between the communication relation extracted from a valid partial execution and the program order restricted to events reading from/writing to this location, and to pairs of events for which at least one of the events is a write.

This condition corresponds to the [uniproc] condition *)

Lemma sc_com_llh_wf :
  forall E so,
  vexec E so ->
  acyclic
  (rel_union (com E (vwitness E so)) (pio_llh E)).
Proof.
intros E so Hsc_ord.
generalize Hsc_ord; intros [Hpart [? Hincl]].
eapply ac_incl;
  [ |
    apply rel_incl_right; apply com_in_so;
      apply Hsc_ord].
rewrite union_triv; auto.
Qed.

(** The read-from relation extracted from a valid partial execution is included in the linear extension of the valid partial execution *)

Lemma sc_rf_in_so :
  forall E so,
  rel_incl (rf (vwitness E so)) (LE so).
Proof.
intros E so; unfold rel_incl; unfold vwitness; simpl; unfold so_rfm.
intros e1 e2 Hin; destruct Hin as [? [[? [Hso ?]] Hmax]]; exact Hso.
Qed.

(** The write serialization extracted from a valid partial execution is included in the linear extension of the valid partial execution *)

Lemma sc_ws_in_so :
  forall E so,
  rel_incl (ws (vwitness E so)) (LE so).
Proof.
intros E so; unfold vwitness; simpl; unfold so_ws.
intros e1 e2 Hin; destruct Hin as [Hso Hrest]; exact Hso.
Qed.

(** The from-read relation extracted from a valid partial execution is included in the linear extension of the valid partial execution *)

Lemma sc_fr_in_so :
  forall E so,
  vexec E so ->
  rel_incl (fr E (vwitness E so)) (LE so).
Proof.
intros E so Hsc_ord; unfold vwitness; unfold fr; unfold frmaps; simpl.
intros e1 e2 Hin.
destruct Hin as [Hevt1 [Hevt2 [wr [Hrf_wr1 Hws_wr2]]]];
  destruct Hsc_ord as [Hpart Hincl].
  assert (Included _ (events E) (events E)) as Htriv.
    intros x Hx; auto.
    generalize (OE Htriv Hpart); intros [Hinc Hle].
  destruct_lin Hle.
destruct Hrf_wr1 as [Hrf_wr1 [Hpw_wr1 Hmax_wr1]];
  destruct Hws_wr2 as [Hso_wr2 [l2 [Hw_wr Hw_e2]]].
  destruct Hrf_wr1 as [Hevt_wr [Hevt_e2 [l1 [Hww_wr Hr_e2]]]];
  destruct Hw_e2 as [Hevtb_e2 Hw_e2].
destruct (eqEv_dec e1 e2) as [Heq | Hdiff].
  rewrite Heq in Hr_e2.
  case_eq (action e2); unfold read_from in Hr_e2; unfold write_to in Hw_e2.
  intros d l v He2; rewrite He2 in Hr_e2; rewrite He2 in Hw_e2; case_eq d.
    intro Hr; rewrite Hr in Hw_e2; destruct Hw_e2 as [? Hw_e2]; inversion Hw_e2.
    intro Hw; rewrite Hw in Hr_e2; destruct Hr_e2 as [[? Hr_e2 ] ?]; inversion Hr_e2.
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

(** In any event structure, the preserved program order of [AWmm] is included in any linear extension of a valid partial execution over this event structure *)

Lemma sc_ppo_in_so :
  forall E so,
  well_formed_event_structure E ->
  vexec E so ->
  rel_incl (A.ppo E) (LE so).
Proof.
unfold rel_incl;
intros E so Hwf Hsc_ord e1 e2 Hin_c.
  destruct Hsc_ord as [Hlin [Hincl ?]].
    assert (LE so e1 e2 \/ LE so e2 e1) as Hor.
  assert (Included _ (events E) (events E)) as Htriv.
    intros y Hy; auto.
    generalize (OE Htriv Hlin); intros [Hinc Hle].
  destruct_lin Hle.
  assert (e1 <> e2) as Hd.
    destruct (eqEv_dec e1 e2) as [Hy | Hn]; auto.
    rewrite Hy in Hin_c; generalize (A.ppo_valid Hin_c); intro Hpo.
    generalize (po_ac Hwf Hpo); intro Ht; inversion Ht.
      apply (Htot e1 e2 Hd).
      apply po_iico_domain_in_events with e2; auto. apply A.ppo_valid; auto.
      apply po_iico_range_in_events with e1; auto. apply A.ppo_valid; auto.
  inversion Hor; auto.
  assert (tc (rel_union (ppo E) (LE so)) e1 e1) as Hc.
    apply trc_ind with e2; apply trc_step; [left | right]; auto.
  generalize (Hincl e1 Hc); intro Ht; inversion Ht.
Qed.

(** In any event structure, the sequence of:

- The reflexive closure of read-from
- The program order
- The reflexive closure of read-from

is included in the any linear extension of any valid partial execution over this event structure *)

Lemma rf_po_rf_in_so :
  forall E so x y,
  well_formed_event_structure E ->
  vexec E so ->
  rel_seq (maybe (rf (vwitness E so)))
        (rel_seq (A.ppo E) (maybe (rf (vwitness E so)))) x y ->
  LE so x y.
Proof.
intros E so x y Hwf Hse [z [Hxz [e [Hze Hey]]]].
  generalize Hse; intros [Hpart [Hincl ?]].
  assert (Included _ (events E) (events E)) as Htriv.
    intros a Ha; auto.
    generalize (OE Htriv Hpart); intros [Hinc Hle].
  destruct_lin Hle.
inversion Hxz as [Hrfxz | Heqxz]; inversion Hey as [Hrfey | Heqey].
  destruct Hrfxz as [? [[? [Hsoxz ?]] ?]] ; destruct Hrfey as [? [[? [Hsoey ?]] ?]].
  apply Htrans with z; split; auto. apply Htrans with e; split; auto.
  apply (sc_ppo_in_so E so Hwf Hse z e Hze).
  rewrite <- Heqey.
    destruct Hrfxz as [? [[? [Hsoxz ?]] ?]]; apply Htrans with z; split; auto.
  apply (sc_ppo_in_so E so Hwf Hse z e Hze).
  rewrite Heqxz.
    destruct Hrfey as [? [[? [Hsoey ?]] ?]]; apply Htrans with e; split; auto.
  apply (sc_ppo_in_so E so Hwf Hse z e Hze).
  rewrite Heqxz; rewrite <- Heqey; auto.
  apply (sc_ppo_in_so E so Hwf Hse z e Hze).
Qed.

(** For any event structure, the union of the barrier relation, write serialization, from-read relation, and preserved program order of the architecture [AWmm] is included in any linear extension of a valid partial execution over this structure *)

Lemma bot_ghb_in_so :
  forall E so,
  well_formed_event_structure E ->
  vexec E so ->
  rel_incl (rel_union (abc E (vwitness E so))
    (rel_union (rel_union (ws (vwitness E so)) (fr E (vwitness E so))) (ppo E))) (LE so).
Proof.
unfold rel_incl; intros E so Hwf Hsc_ord e1 e2 Hx.
  inversion Hx as [Hab | Hrest].
  (*ab*)
  generalize Hsc_ord; intro Hse.
  destruct Hsc_ord as [Hpart [Hincl ?]].
  assert (Included _ (events E) (events E)) as Htriv.
    intros e He; auto.
    generalize (OE Htriv Hpart); intros [Hinc Hle].
  destruct_lin Hle.
    generalize (AwkAiSc); intros [? [? [? Habi]]].
    generalize (ab_sc_compat E (vwitness E so) e1 e2 (Habi E (vwitness E so) e1 e2 Hab));
    intro Hin.  apply (rf_po_rf_in_so E so e1 e2 Hwf Hse Hin).
    inversion Hrest as [Hws_fr | Hppo].
      inversion Hws_fr as [Hws | Hfr].
    (*ws*)
    generalize Hws; apply sc_ws_in_so.
  (*fr*)
    generalize Hfr; apply sc_fr_in_so; apply Hsc_ord.
  (*ppo*)
  generalize Hsc_ord; intros [Hpart Hincl].
  assert (Included _ (events E) (events E)) as Htriv.
    intros e He; auto.
    generalize (OE Htriv Hpart); intros [Hinc Hle].
    generalize Hwf Hsc_ord e1 e2 Hppo; apply sc_ppo_in_so; split; auto.
Qed.

(** For any well-formed event structure, the global happens-before of the architecture [AWmm] is included in any linear extension of a valid partial execution over this structure *)

Lemma sc_ghb_in_so :
  forall E so,
  well_formed_event_structure E ->
  vexec E so ->
  rel_incl (ghb E (vwitness E so)) (LE so).
Proof.
unfold rel_incl; intros E so Hwf Hsc_ord e1 e2 Hx.
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
    generalize Hres; apply (bot_ghb_in_so); auto.
  (*true, false*)
  intros Hintra Hinter; rewrite Hintra in Hx; rewrite Hinter in Hx.
  inversion Hx as [Hrf_inter | Hrest].
  (*rf_inter*)
  destruct Hrf_inter as [Hrf Hprocs].
  generalize Hrf; apply sc_rf_in_so.
    generalize Hrest; apply (bot_ghb_in_so); auto.
  (*false, true*)
  intros Hintra Hinter; rewrite Hintra in Hx; rewrite Hinter in Hx.
  inversion Hx as [Hrf_intra | Hrest].
  (*rf_intra*)
  destruct Hrf_intra as [Hrf Hprocs].
  generalize Hrf; apply sc_rf_in_so.
    generalize Hrest; apply (bot_ghb_in_so); auto.
  (*false,false*)
  intros Hintra Hinter; rewrite Hintra in Hx; rewrite Hinter in Hx.
  generalize Hx; apply (bot_ghb_in_so); auto.
Qed.

(** For any event structure, the global happens-before extracted of any valid partial execution on the event structure is acyclic. *)

Lemma sc_exec_wf :
  forall E so,
  well_formed_event_structure E ->
  vexec E so ->
  acyclic (ghb E (vwitness E so)).
Proof.
intros E so Hwf Hsc_ord.
generalize Hsc_ord; intros [Hpart Hincl];
  assert (Included _ (events E) (events E)) as Htriv.
    intros e He; auto.
    generalize (OE Htriv Hpart); intros [Hinc Hle].
eapply incl_ac;
  [apply sc_ghb_in_so; auto |
    eapply lin_strict_ac; apply Hle].
Qed.

(** For any event structure, the execution witness extracted from any valid partial execution over the event structure respects the out-of-[thin]-air condition *)

Lemma sc_exec_thin :
  forall E so,
  well_formed_event_structure E ->
  vexec E so ->
  acyclic (rel_union (so_rfm E so) (dp E)).
Proof.
intros E so Hwf Hsc x Hx.
assert (rel_incl (rel_union (so_rfm E so) (dp E)) (LE so)) as Hi.
  intros e1 e2 H12.
    inversion H12 as [Hrf | Hdp].
      generalize (sc_rf_in_so E so); intros Hi.
        unfold vwitness in Hi; simpl in Hi; apply Hi; auto.
  generalize Hsc; intros [Hpart [Hincl ?]].
  assert (Included _ (events E) (events E)) as Htriv.
    intros e He; auto.
    generalize (OE Htriv Hpart); intros [Hinc Hle].
      generalize (dp_ppo Hdp).
      apply sc_ppo_in_so; auto.
assert (LE so x x) as Hc.
  destruct Hsc as [Hpart Hincl].
  assert (Included _ (events E) (events E)) as Htriv.
    intros e He; auto.
    generalize (OE Htriv Hpart); intros [Hinc Hle].
  rewrite <- (lso_is_tc Hle).
  generalize Hx; apply tc_incl; auto.
  destruct Hsc as [Hpart Hincl].
  assert (Included _ (events E) (events E)) as Htriv.
    intros e He; auto.
    generalize (OE Htriv Hpart); intros [Hinc Hle].
destruct_lin Hle.
apply (Hac x Hc).
Qed.

(** In a well-formed event structure, an execution witness extracted from any valid execution witness is a valid execution on [AWmm].

I.e. An execution extracted from a valid partial execution is valid on [A] *)

Lemma sc_witness_valid :
  forall E so,
  well_formed_event_structure E ->
  vexec E so ->
  valid_execution E (vwitness E so).
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
{ eapply sc_com_llh_wf; auto. }
split.
(* out-of-thin-air condition *)
{ eapply sc_exec_thin; auto. }
(* ghb is acyclic *)
{ apply sc_exec_wf; auto. }
Qed.


(** ** An SC execution witness SC checks *)

(** For any execution witness, the global-read from relation is always included in the read-from relation *)

Lemma mrf_in_rf :
  forall X x y,
  mrf X x y ->
  rf X x y.
Proof.
intros X x y Hxy; inversion Hxy as [Hi | He].
  unfold mrfi in Hi; case_eq intra; intro Heq; rewrite Heq in Hi;
  inversion Hi; auto.
  unfold mrfe in He; case_eq inter; intro Heq; rewrite Heq in He;
  inversion He; auto.
Qed.

(** For any event structure and any execution witness, the [ahb] relation is always included in the communication relation *)

Lemma ahb_in_com:
  forall E X x y,
  ahb E X x y ->
  com E X x y.
Proof.
intros E X x y Hxy; inversion Hxy as [Hrffr | Hws]; [left | right]; auto.
inversion Hrffr as [Hrf | Hfr]; [left | right]; auto.
  apply mrf_in_rf; auto.
Qed.

(** In a well-formed event structure, The union of the preserved program order and of the happens-before associated to the execution witness extracted from a valid partial execution is included in the linear extension of this valid partial execution *)

Lemma hb_po_in_so :
  forall E so,
  well_formed_event_structure E ->
  vexec E so ->
  rel_incl (rel_union (ppo E) (ahb E (vwitness E so))) (LE so).
Proof.
intros E so Hwf Hsc x y Hxy.
inversion Hxy.
  generalize Hsc; intros [Hpart [Hincl ?]].
  assert (Included _ (events E) (events E)) as Htriv.
    intros e He; auto.
    generalize (OE Htriv Hpart); intros [Hinc Hle].
  generalize H; apply sc_ppo_in_so; auto.
  assert (com E (vwitness E so) x y) as Hhb.
    apply ahb_in_com; auto.
  apply (com_in_so E so Hsc x y Hhb).
Qed.

(** In a well-formed event structure, any execution witness extracted from any valid partial execution on the event structure respects the [sc_check] property *)

Lemma sc_witness_sc :
  forall E so,
  well_formed_event_structure E ->
  vexec E so ->
  sc_check E (vwitness E so).
Proof.
intros E so Hwf Hsc; unfold sc_check.
eapply incl_ac.
  apply hb_po_in_so; auto.
  destruct Hsc as [Hpart Hincl].
  assert (Included _ (events E) (events E)) as Htriv.
    intros e He; auto.
    generalize (OE Htriv Hpart); intros [Hinc Hle].
  generalize Hle; intro Hl; destruct_lin Hle;
  unfold acyclic; rewrite (lso_is_tc Hl); auto.
Qed.

End sc_valid.

Section obs.

Ltac destruct_lin H :=
  destruct H as [Hdr [Htrans [Hac Htot]]].

(** In well-formed event structure with a well-formed execution witness and an arbitrary order [so] on the events of the event structure, if:

- The union of the preserved program order and of the communication relation is acyclic
- Any linear extension of [so] is a strict linear order
- The union of the preserved program order and of the communication relation is included in any linear extension of [so]

Then the write serialization of the execution witness is the same as the one extracted from [so] *)

Lemma ac_po_com_implies_same_ws:
  forall E X so,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  acyclic (rel_union (ppo E) (com E X))->
  linear_strict_order (LE so) (events E) ->
  rel_incl (rel_union (ppo E) (com E X)) (LE so) ->
  ws X = ws (vwitness E so).
Proof.
intros E X so Hwf Hs Hacy Hlin Hincl.
generalize Hs; intros [Hwswf Hrfwf].
assert (forall x y, (ws X) x y <-> (ws (vwitness E so)) x y) as Hext.
  split; intro Hin;
unfold vwitness; unfold so_ws; simpl.
  split.
  apply Hincl; right; unfold com;
  right; apply Hin.
  destruct_lin Hlin.
    generalize (ws_cands E X x y Hwswf Hin).
    intros [l [Hx Hy]]; exists l; split.
  split; destruct Hx as [Hudr Hwx]; auto.
  unfold udr; apply incl_union_left_in; exists y; apply Hincl; right; right; auto.

  split; destruct Hy as [Hudr Hwy]; auto.
  unfold udr; apply incl_union_right_in; exists x; apply Hincl; right; right; auto.

  unfold vwitness in Hin; simpl in Hin.
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
    assert (LE so y x) as Hin_ex.
      apply Hincl; unfold com;
        right; right; exact Hws_ex.
    assert (~(acyclic (LE so))) as Hcontrad.
      unfold acyclic; unfold not; intro Hcy; apply (Hcy x).
      eapply trc_ind with y; apply trc_step; [apply Hin | exact Hin_ex].
  generalize Hlin; intro Hli; destruct_lin Hlin; unfold acyclic in Hcontrad.
  generalize (lso_is_tc Hli); intro Heq; rewrite Heq in Hcontrad.
    contradiction.
apply (ext_rel (ws X) (ws (vwitness E so)) Hext).
Qed.

End obs.

(** ** Characterisation of a valid execution *)

Section sc_carac.

Ltac destruct_lin H :=
  destruct H as [Hdr [Htrans [Hac Htot]]].

(** In a well-formed event structure with a valid execution witness and an arbitrary order [so] on the events of the event structure, if:

- Any linear extension of [so] is a strict linear order
- The union of the preserved program order and of the communication relation is included in any linear extension of [so]

Then the read-from relation extracted from [so] is included in the read-from relation of the execution witness *)

Lemma sc_rf_ax :
  forall E X so x y,
  well_formed_event_structure E ->
  valid_execution E X ->
  linear_strict_order (LE so) (events E) ->
  rel_incl (rel_union (ppo E) (com E X)) (LE so) ->
  so_rfm E so x y ->
  rf X x y (*\/ init E x*).
Proof.
intros E X so x y Hwf Hv Hlin Hincl [Hrf [Hpw Hmax]].
generalize Hv; intro Hva.
assert (exists w, rf X w y (*\/ init E w*)) as Hrf_y.
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
      destruct Hrf as [? [? [ly [? Hry]]]]; destruct Hwx as [vx Hwx].
       unfold loc in Hl; rewrite Hwx in Hl; generalize Hry; intro Hy;
       destruct Hry as [[vy Hry] ?]; rewrite Hry in Hl; inversion Hl; auto.
       destruct Hy as [Hrry ?];
      apply (rf_implies_same_loc w Hv Hrf_wy Hrry).
    destruct_valid Hva; destruct_lin (Hws_tot l).
    generalize (Htot w x Hdiff Hmw Hmx); intro Horw.
    inversion Horw as [Hwswx | Hwsxw].
      destruct Hwswx; auto.
      destruct Hwsxw; auto.
  inversion Hor as [Hxw | Hwx].
  assert (LE so w y) as Hso_wy.
    apply Hincl; right; left; left; auto.
  assert (LE so x w) as Hso_xw.
    apply Hincl; right; right; auto.
  destruct_valid Hv.
  generalize (Hrf_cands w y Hrf_wy); intros [Hew [Hey [l [Hww Hry]]]].
  assert (exists e3 : Event, write_to e3 l /\ LE so x e3 /\ LE so e3 y) as Hcontrad.
    exists w; split; auto.
  assert (write_to x l) as Hwx.
    destruct Hrf as [? [? [l' [Hwx' [Hry' ?]]]]].
       destruct Hry as [Hrry ?];
    rewrite (read_from_implies_same_loc Hrry Hry'); auto.
    destruct Hcontrad as [e3 [[v3 Hwe3] [Hxe3 He3y]]].
    assert (x = e3) as Heq.
      apply (Hmax e3); split; auto.
      split; [unfold writes; split; [|exists l; exists v3; auto] |split; auto].
       destruct_lin Hlin; apply Hdr; apply incl_union_left_in; exists y; auto.
      destruct Hry as [[vy Hry] ?]; unfold loc; rewrite Hry; rewrite Hwe3; trivial.
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
      assert (LE so y x) as Hso_yx.
        apply Hincl; right; left; right; auto.
      destruct Hpw as [? [Hso_xy ?]].
  destruct_lin Hlin;
  assert (LE so y y) as Hso_yy.
    apply Htrans with x; auto.
  generalize (Hac y); intro Hc; contradiction.
Qed.

(** The read-from relation of a valid execution witness is always included in the communication relation of this execution *)

Lemma rf_in_com:
  forall E X x y,
  valid_execution E X ->
  rf X x y ->
  com E X x y.
Proof.
intros E X x y Hv Hrf.
left; left; auto.
Qed.

(** In a well-formed event structure, with a valid execution that verifies the [sc_check] property, and with an arbitrary order [so] on the events of the event structure, if:

- Any linear extension of [so] is a strict linear order
- The union of preserved program order and of the communication relation is included in any linear extension of [so]

Then the read-from relation extracted from [so] is the same as the read-from of the execution witness
*) 

Lemma so_rfm_po_com_is_rf:
  forall E X so,
  well_formed_event_structure E ->
  valid_execution E X ->
  sc_check E X ->
  linear_strict_order (LE so) (events E) ->
  rel_incl (rel_union (ppo E) (com E X)) (LE so) ->
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
    exists vx; unfold write_to in Hx; unfold write_to; rewrite Hx.
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
  assert (LE so y x') as Hso_y3.
    apply Hincl; right; left; right; auto.
  destruct_lin Hlin.
  assert (LE so x' y /\ LE so y x') as Ha.
    split; auto.
  generalize (Htrans x' y x' Ha); intro Hc.
  generalize (Hac x'); intro Hco; contradiction.
  assert (LE so x' x) as Hso_3x.
    apply Hincl; right; right; auto.
  assert (LE so x' x /\ LE so x x') as Ha.
    split; auto.
  destruct_lin Hlin.
  generalize (Htrans x' x x' Ha); intro Hc.
  generalize (Hac x'); intro Hco; contradiction.
Qed.

(** In a well-formed event structure, the domain and range of the preserved program order and of the communication relation of any valid execution witness are included int the set of events of the event structure *)

Lemma incl_udr_sc_check_in_events :
  forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
    Included _ (udr (rel_union (ppo E) (com E X))) (events E).
Proof.
intros E X Hwf Hv.
intros x Hx; inversion Hx as [x0 Hd | x0 Hr].
  destruct Hd as [y Hor]; inversion Hor as [Hppo | Hhb].
  apply po_iico_domain_in_events with y; auto.
  apply A.ppo_valid; auto.
  apply hb_domain_in_events with X y; auto.
    destruct_valid Hv; split; split; auto.
  destruct Hr as [y Hor]; inversion Hor as [Hppo | Hhb].
  apply po_iico_range_in_events with y; auto.
  apply A.ppo_valid; auto.
  apply hb_range_in_events with X y; auto.
    destruct_valid Hv; split; split; auto.
Qed.

(** In a well-formed event structure, if there is a valid partial execution on the event structure, then there exists a valid execution witness that verifies the [sc_check] condition anbd whose read-from relation and write serialization are the same as the one we can extract from the valid partial execution *)

Lemma sc_carac :
  forall E rfm wsn,
  well_formed_event_structure E ->
    (exists so, vexec E so /\ so_rfm E so = rfm /\ so_ws so = wsn) ->
  (exists X, valid_execution E X /\ sc_check E X /\ (rf X) = rfm /\ (ws X) = wsn).
Proof.
intros E rfm wsn Hwf; intros [so [Hseq [Hac Hrf]]].
exists (vwitness E so); split;
  [apply sc_witness_valid; auto |
     split; [apply sc_witness_sc; auto | unfold vwitness; simpl; auto]].
Qed.

End sc_carac.

End ScAx.

Module ScModel.
(*
Module ScArch <: Archi.

Definition ppo (E:Event_struct) := (po_iico E).

Lemma ppo_valid : forall E, rel_incl (ppo E) (po_iico E).
  unfold rel_incl; trivial.
Qed.

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

Definition inter := true.
Definition intra := true.

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

Definition dp (E:Event_struct) := fun e1:Event => fun e2:Event => False.

Lemma dp_valid : forall E, rel_incl (dp E) (po_iico E).
  unfold rel_incl; intros; inversion H.
Qed.

Import ScArch.
Module ScBasic := Basic ScArch dp.
Import ScBasic.
Module ScWmm := Wmm ScArch dp.
Import ScWmm. *)


Import ScAx.

(*
Lemma po_is_ppo_po :
  forall E e1 e2,
  po_iico E e1 e2 ->
  (ppo E) e1 e2.
Proof.
intros E e1 e2 Hpo;
apply Hpo.
Qed.
*)

Module ABasic := Basic A.

(** For any event structure and any execution witness, the union of the preserved program order and of the [ahb] relation is included in the global happesn-before relation *)

Lemma po_hb_in_ghb :
  forall E X,
  rel_incl (rel_union (A.ppo E) (ahb E X)) (AWmm.ghb E X).
Proof.
intros E X x y Hxy.
inversion Hxy.
apply ABasic.ppo_in_ghb; auto.
inversion H.
  inversion H0.
    apply ABasic.mrf_in_ghb; auto.
    apply ABasic.fr_in_ghb; auto.
    apply ABasic.ws_in_ghb; auto.
Qed.

(* In well-formed event structure, any valid execution verifies the [sc_check] condition *)

Lemma exec_sc_check :
  forall E X,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  sc_check E X.
Proof.
unfold sc_check;
intros E X Hwf Hvalid.
AWmm.destruct_valid Hvalid.
generalize (po_hb_in_ghb); intro Hincl.
apply (incl_ac (Hincl E X)); auto.
Qed.

(** This is just a special case of [sc_carac] *)

Lemma vexec_is_valid :
  forall E rfm wsn,
  well_formed_event_structure E ->
  ((exists so, vexec E so /\ so_rfm E so = rfm /\ so_ws so = wsn) ->
    (exists X, AWmm.valid_execution E X /\ (rf X) = rfm /\ (ws X) = wsn)).
Proof.
intros E rfm wsn Hwf; intro Hex.
destruct (sc_carac E rfm wsn Hwf Hex) as [X [Hval [Hsccheck [Hrfm Hwsn]]]].
exists X; auto.
Qed.

End ScModel.

End Valid.
