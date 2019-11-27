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

In this module, we define a sequentially consitent execution

TODO: This description of the module needs to be a little bit mor detailed *)

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

(** Two events are related by the read-from relation extracted from the SC execution if:

- They are events from the domain or the range of the SC execution
- The first one is a write event and the second one is a read event
- They access the same location
- They read/write the same value
- The first event belongs to the maximal elements of the previous writes (w.r.t. to the SC execution) of the second event. Simply put, the first event
is the most recent write before the second event in the SC execution *)

Definition so_rfm (E:Event_struct) (so : Rln Event) :=
  fun ew => fun er =>
    (rfmaps (udr so)) ew er /\
    (maximal_elements
       (previous_writes E so er) so) ew.

(** For any SC execution on a structure of event, for every read event in this structure, there is a write such that the read-from extracted from the SC execution relates the write event to the read event *)

Hypothesis so_rfm_init :
  forall E so,
  forall er, In _ (reads E) er ->
    exists ew, In _ (events E) ew /\ so_rfm E so ew er.

(** ** write serialization of SC execution *)

(** Two events are related by the write serialization extracted from the SC if:

- They are related by the SC execution
- They are both writes to the same location *)

Definition so_ws (so:Rln Event) : (Rln Event) :=
    fun e1 => fun e2 =>
    so e1 e2 /\
    exists l, In _ (writes_to_same_loc_l (udr so) l) e1 /\
      In _ (writes_to_same_loc_l (udr so) l) e2.

(** ** Definition of a SC witness

A SC witness associated to an event structure and a SC execution is composed of the read-from relation and write serialization extracted from the SC execution.
*)

Definition sc_witness (E:Event_struct) (so:Rln Event) : Execution_witness :=
  mkew (so_ws so) (so_rfm E so).

(** The definition of [AiSc] is exactly the same as the one of its module type [Archi], but it adds an extra hypothesis [ab_sc_compat] *)

Module AiSc <: Archi.

Parameter ppo : Event_struct -> Rln Event.

Hypothesis ppo_valid : forall E, rel_incl (ppo E) (po_iico E).

Hypothesis ppo_fun :
  forall E s x y,
  ppo E x y /\ s x /\ s y <->
  ppo (mkes (Intersection Event (events E) s) (rrestrict (iico E) s)) x y.

Parameter inter : bool.
Parameter intra : bool.

Parameter abc  : Event_struct -> Execution_witness -> Rln Event.

(** The barrier relation must be included in the sequence of:

- The reflexive closure of read-from
- The sequence of the program order and of the reflexive closure of read-from

That means that the ordering enforced by the barriers should not be in contradiction with the program order, and should avoid the two following inconsistencies :

- The barrier enforces an event [e] to occur before a write event [w], but there is a read event [r] occuring before [e] in program order and [r] reads the value written by [w]
- The barrier enforces an event [e] to occur after a read [r], but there is a write event [w] occuring after [e] in program order and [r] reads the value written by [w]
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

Module ScAx (A:Archi).

Definition bimpl (b1 b2:bool) : Prop:=
  if (negb b1) || b2 then True else False.

Definition rf_impl (rf1 rf2 : bool) :=
  bimpl rf1 rf2.

Definition ppo_incl (ppo1 ppo2 : Event_struct -> Rln Event) :=
  forall E, rel_incl (ppo1 E) (ppo2 E).

Definition ab_incl (ab1 ab2 : Event_struct -> Execution_witness -> Rln Event) :=
  forall E X, rel_incl (ab1 E X) (ab2 E X).

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

Definition sc_check (E:Event_struct) (X:Execution_witness) : Prop :=
  acyclic (rel_union (po_iico E) (hb E X)).

Section sc_valid.

(** * A SC witness is a valid one *)

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

Lemma sc_rf_wf :
  forall E so,
  rel_incl (ls E) (po_iico E) ->
  seq_exec E so ->
  rfmaps_well_formed E (events E) (so_rfm E so).
Proof.
intros E so Hdp Hsc_ord; unfold rfmaps_well_formed; split.
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

Lemma sc_rf_in_so :
  forall E so,
  rel_incl (rf (sc_witness E so)) so.
Proof.
intros E so; unfold rel_incl; unfold sc_witness; simpl; unfold so_rfm.
intros e1 e2 Hin; destruct Hin as [? [[? [Hso ?]] Hmax]]; exact Hso.
Qed.

Lemma sc_ws_in_so :
  forall E so,
  rel_incl (ws (sc_witness E so)) so.
Proof.
intros E so; unfold sc_witness; simpl; unfold so_ws.
intros e1 e2 Hin; destruct Hin as [Hso Hrest]; exact Hso.
Qed.

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

Lemma sc_exec_wf :
  forall E so,
  seq_exec E so ->
  acyclic (ghb E (sc_witness E so)).
Proof.
intros E so Hsc_ord.
eapply incl_ac;
  [apply sc_ghb_in_so; apply Hsc_ord |
    destruct Hsc_ord as [Hlin Hincl]; eapply lin_strict_ac; apply Hlin].
Qed.

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

Lemma sc_witness_valid :
  forall E so,
  well_formed_event_structure E ->
  seq_exec E so ->
  valid_execution E (sc_witness E so).
Proof.
intros E so Hwf Hsc_ord.
unfold valid_execution; unfold sc_witness; simpl.
 split;  [eapply sc_ws_wf; apply Hsc_ord |
  split; [apply sc_rf_wf; [ | apply Hsc_ord]  | ]].
intros x y [? [? ?]]; auto.

split; fold (sc_witness E so);
   [apply sc_hb_llh_wf; apply Hsc_ord |
    split; [|apply sc_exec_wf; apply Hsc_ord]].
apply sc_exec_thin; auto.
Qed.

(*An SC witness sc checks *)

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

Section obs.

Ltac destruct_lin H :=
  destruct H as [Hdr [Htrans [Hac Htot]]].

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

End obs.

Section sc_carac.

Ltac destruct_lin H :=
  destruct H as [Hdr [Htrans [Hac Htot]]].

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

Lemma rf_in_hb :
  forall E X x y,
  valid_execution E X ->
  rf X x y ->
  hb E X x y.
Proof.
intros E X x y Hv Hrf.
left; left; auto.
Qed.

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

Module ScModel.

Module ScArch <: Archi.
Definition dp (E:Event_struct) := fun e1:Event => fun e2:Event => False.
Lemma dp_valid : forall E, rel_incl (dp E) (po_iico E).
  unfold rel_incl; intros; inversion H.
Qed.
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

Import ScArch.
Module ScBasic := Basic ScArch dp.
Import ScBasic.
Module ScWmm := Wmm ScArch dp.
Import ScWmm.
Module ScAx := ScAx ScArch.
Import ScAx.

Lemma po_is_ppo_po :
  forall E e1 e2,
  po_iico E e1 e2 ->
  (ppo E) e1 e2.
Proof.
intros E e1 e2 Hpo;
apply Hpo.
Qed.

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

Module ABTh (A:Archi).
Module ABasic := Basic A dp.
Import ABasic.
Import A.
Module AWmm := Wmm A dp.
Import AWmm.

Inductive ABTh (E:Event_struct) (X:Execution_witness) : Event -> Event -> Prop :=
  | Base : forall e1 e2, (*events E e1 -> events E e2 ->*)
      (po_iico E) e1 e2 -> ABTh E X e1 e2
  | Right : forall e1 w2 r2, (*events E e1 -> events E w2 -> events E r2 ->*)
      po_iico E e1 w2 /\ (rf X) w2 r2 -> ABTh E X e1 r2
  | Left : forall w1 r1 e2, (*events E w1 -> events E r1 -> events E e2 ->*)
      (rf X) w1 r1 /\ po_iico E r1 e2 -> ABTh E X w1 e2.

Module SyncTh <: Archi.
Parameter dp : Event_struct -> Rln Event.
Hypothesis dp_valid : forall E, rel_incl (dp E) (po_iico E).
Parameter ppo : Event_struct -> Rln Event.
Hypothesis ppo_valid : forall E, rel_incl (ppo E) (po_iico E).
Hypothesis ppo_fun :
  forall E s x y,
  ppo E x y /\ s x /\ s y <->
  ppo (mkes (Intersection Event (events E) s) (rrestrict (iico E) s)) x y.
Parameter intra : bool.
Parameter inter : bool.
Definition abc := ABTh.
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
Hypothesis ab_fun :
  forall E X s x y,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  (abc E X x y /\ s x /\ s y <->
  abc (mkes
     (Intersection Event (events E) s) (rrestrict (iico E) s))
    (mkew (rrestrict (ws X) s) (rrestrict (rf X) s)) x y).
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

Import SyncTh.
Module SyncThBasic := Basic SyncTh dp.
Import SyncThBasic.
Module SyncThWmm := Wmm SyncTh dp.
Import SyncThWmm.
Module SyncThAx := ScAx SyncTh.
Import SyncThAx.
Import ScModel.

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
