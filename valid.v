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
Import OEEvt.
Set Implicit Arguments.

Module Valid (A:Archi) (dp : Dp).
Import dp.

Hypothesis dp_ppo :
  forall E, rel_incl (dp E) (A.ppo E).

(** ** Definition *)

Definition previous_writes (E:Event_struct) (r : Rln Event) (er:Event) :=
  fun ew => writes E ew /\ r ew er /\ loc ew = loc er.
Set Implicit Arguments.
Definition maximal_elements (A:Set) (xs:set A) (r:Rln A) : set A :=
  fun x => In _ xs x /\ forall x', In _ xs x'/\ r x x' -> (x = x').
Unset Implicit Arguments.

Definition vexec (E:Event_struct) (so:Rln Event) : Prop :=
  partial_order so (events E) /\
  acyclic (rel_union (A.ppo E) (LE so)) /\
  acyclic (rel_union (pio_llh E) (LE so)).

(** * Building a SC witness *)

(** ** sc rfmaps *)
Definition so_rfm (E:Event_struct) (so : Rln Event) :=
  fun ew => fun er =>
    (rfmaps (udr (LE so))) ew er /\
    (maximal_elements
       (previous_writes E (LE so) er) (LE so)) ew.
Hypothesis so_rfm_init :
  forall E so,
  forall er, In _ (reads E) er ->
    exists ew, (In _ (events E) ew /\ so_rfm E so ew er)
      (*\/ (init E ew)*).

(** ** sc ws *)

Definition so_ws (so:Rln Event) : (Rln Event) :=
    fun e1 => fun e2 =>
    LE so e1 e2 /\
    exists l, In _ (writes_to_same_loc_l (udr (LE so)) l) e1 /\
      In _ (writes_to_same_loc_l (udr (LE so)) l) e2.

(** ** sc sync *)

Definition so_sync (so:Rln Event) (synchro:Rln Event) : Rln Event :=
  fun e1 e2 => so e1 e2 /\ synchro e1 e2.

(** ** Definition of a witness *)

Definition vwitness (E:Event_struct) (so:Rln Event) : Execution_witness :=
  mkew (so_ws so) (so_rfm E so).

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
Parameter ab_sc_compat :
  forall E X, rel_incl (abc E X) (rel_seq (maybe (rf X)) (rel_seq (A.ppo E) (maybe (rf X)))).
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
End AiSc.

Import AiSc.
Module ScAx.
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
Definition ahb E X :=
  rel_union (rel_union (AWmm.mrf X) (fr E X)) (ws X).
Definition sc_check (E:Event_struct) (X:Execution_witness) : Prop :=
  acyclic (rel_union (A.ppo E) (ahb E X)).

Section sc_valid.

(** * A SC witness is a valid one *)

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

Lemma sc_rf_wf :
  forall E so,
  rel_incl (ls E) (po_iico E) ->
  vexec E so ->
  rfmaps_well_formed E (events E) (so_rfm E so).
Proof.
intros E so Hdp Hsc_ord; unfold rfmaps_well_formed; split.
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

Lemma hb_in_so :
  forall E so,
  vexec E so ->
  rel_incl (hb E (vwitness E so)) (LE so).
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

Lemma sc_hb_llh_wf :
  forall E so,
  vexec E so ->
  acyclic
  (rel_union (hb E (vwitness E so)) (pio_llh E)).
Proof.
intros E so Hsc_ord.
generalize Hsc_ord; intros [Hpart [? Hincl]].
eapply ac_incl;
  [ |
    apply rel_incl_right; apply hb_in_so;
      apply Hsc_ord].
rewrite union_triv; auto.
Qed.

Lemma sc_rf_in_so :
  forall E so,
  rel_incl (rf (vwitness E so)) (LE so).
Proof.
intros E so; unfold rel_incl; unfold vwitness; simpl; unfold so_rfm.
intros e1 e2 Hin; destruct Hin as [? [[? [Hso ?]] Hmax]]; exact Hso.
Qed.

Lemma sc_ws_in_so :
  forall E so,
  rel_incl (ws (vwitness E so)) (LE so).
Proof.
intros E so; unfold vwitness; simpl; unfold so_ws.
intros e1 e2 Hin; destruct Hin as [Hso Hrest]; exact Hso.
Qed.

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

Lemma sc_witness_valid :
  forall E so,
  well_formed_event_structure E ->
  vexec E so ->
  valid_execution E (vwitness E so).
Proof.
intros E so Hwf Hsc_ord.
unfold valid_execution; unfold vwitness; simpl.
 split;  [eapply sc_ws_wf; apply Hsc_ord |
  split; [apply sc_rf_wf; [ | apply Hsc_ord]  | ]].
intros x y [? [? ?]]; auto.
split; fold (vwitness E so);
   [apply sc_hb_llh_wf; apply Hsc_ord |
    split; [|apply sc_exec_wf; auto]].
apply sc_exec_thin; auto.
Qed.

(*An SC witness sc checks *)

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

Lemma ahb_in_hb :
  forall E X x y,
  ahb E X x y ->
  hb E X x y.
Proof.
intros E X x y Hxy; inversion Hxy as [Hrffr | Hws]; [left | right]; auto.
inversion Hrffr as [Hrf | Hfr]; [left | right]; auto.
  apply mrf_in_rf; auto.
Qed.

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
  assert (hb E (vwitness E so) x y) as Hhb.
    apply ahb_in_hb; auto.
  apply (hb_in_so E so Hsc x y Hhb).
Qed.

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

Lemma ac_po_hb_implies_same_ws :
  forall E X so,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  acyclic (rel_union (ppo E) (hb E X))->
  linear_strict_order (LE so) (events E) ->
  rel_incl (rel_union (ppo E) (hb E X)) (LE so) ->
  ws X = ws (vwitness E so).
Proof.
intros E X so Hwf Hs Hacy Hlin Hincl.
generalize Hs; intros [Hwswf Hrfwf].
assert (forall x y, (ws X) x y <-> (ws (vwitness E so)) x y) as Hext.
  split; intro Hin;
unfold vwitness; unfold so_ws; simpl.
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
      apply Hincl; unfold hb;
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

Section sc_carac.

Ltac destruct_lin H :=
  destruct H as [Hdr [Htrans [Hac Htot]]].

Lemma sc_rf_ax :
  forall E X so x y,
  well_formed_event_structure E ->
  valid_execution E X ->
  linear_strict_order (LE so) (events E) ->
  rel_incl (rel_union (ppo E) (hb E X)) (LE so) ->
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
  linear_strict_order (LE so) (events E) ->
  rel_incl (rel_union (ppo E) (hb E X)) (LE so) ->
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

Lemma incl_udr_sc_check_in_events :
  forall E X,
  well_formed_event_structure E ->
  valid_execution E X ->
    Included _ (udr (rel_union (ppo E) (hb E X))) (events E).
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
Import ScAx.

Lemma po_is_ppo_po :
  forall E e1 e2,
  po_iico E e1 e2 ->
  (ppo E) e1 e2.
Proof.
intros E e1 e2 Hpo;
apply Hpo.
Qed.

Module ABasic := Basic A.

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

Lemma exec_sc_check :
  forall E X,
  well_formed_event_structure E ->
  AWmm.valid_execution E X ->
  sc_check E X.
Proof.
unfold sc_check;
intros E X Hwf Hvalid.
destruct_valid Hvalid.
generalize (po_hb_in_ghb); intro Hincl.
apply (incl_ac (Hincl E X)); auto.
Qed.

Lemma vexec_is_valid :
  forall E rfm wsn,
  well_formed_event_structure E ->
  ((exists so, vexec E so /\ so_rfm E so = rfm /\ so_ws so = wsn) ->
    (exists X, AWmm.valid_execution E X /\ (rf X) = rfm /\ (ws X) = wsn)).
Proof.
intros E rfm wsn Hwf; intro Hex.
  destruct Hex as [so [Hseq [Hrf Hws]]].
  exists (vwitness E so); split.
  apply sc_witness_valid;
    [apply Hwf | apply Hseq].
  unfold vwitness; simpl; auto.
Qed.

End ScModel.

End Valid.
