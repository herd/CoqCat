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
Require Import Classical_Pred_Type.
Import OEEvt.
Set Implicit Arguments.

(** * DRF Guarantee 

The goal of this module is to prove the DRF guarantee, which states that:

If all the executions valid on the SC memory model have all their races covered by a synchronisation relation, then all the executions of the program behave according to the SC memory model *)

Module DataRaceFree (A1 A2: Archi) (dp:Dp).

(** We import facts about the hierarchical relation between A1 and A2, including the memory model associated to the two architectures *)

Module Wk := Weaker A1 A2 dp.
Import Wk.

(** We import facts about the validity of executions on the stronger architecture A2 *)

Module VA2 := Valid A2 dp.
Import VA2.
Import VA2.ScAx.

(** We import the abstract notion of covering relation that would preserve validity of executions from A1 to A2 *)

Module Covering := Covering A1 A2 dp.
Import Covering.

(** We import basic facts about the architecture [A2] *)

Module A2Basic := Basic A2 dp.

(** ** [happens_before] 

This module type defines the [happens_before] relation (which is different from the happens-before relation [hb], called the communication relation in (A Shared Memory Poetics, Jade Alglave, 2010)), which depends on a synchronisation relation.
*)

Module Type HappensBefore.

(** We have an arbitrary synchronisation relation on the events of an execution *)

Parameter sync : Event_struct -> Execution_witness -> Rln Event.

(** The [happens_before] relation is the transitive closure of the union of:

- The program order
- The synchronisation relation *)

Definition happens_before E X :=
  tc (rel_union (po_iico E) (sync E X)).

(** If an event [x] is related to [y] by the communication relation (the union of read-from, write serialisation and from-read), then the [happens_before] relation can't relate [y] to [x]. *)

Hypothesis happens_before_compat_com :
  forall E X x y, com E X x y -> ~(happens_before E X y x).

(** In a well-formed event structure with an execution valid on the weaker architecture, [happens_before] is irreflexive. Since it is a transitive closure, it is also a transitive relation, and thus, it is acyclic *)

Hypothesis happens_before_irr :
  forall E X x,
  well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  ~(happens_before E X x x).

(** Two events of an execution are competing if:

- They read from/write to the same memory location
- They are executed on different threads
- At least one of them is a write event *)

Definition competing E (X:Execution_witness) :=
  fun e1 => fun e2 => events E e1 /\ events E e2 /\
    loc e1 = loc e2 /\ proc_of e1 <> proc_of e2 /\
    (writes E e1 \/ writes E e2).

(** [cns] contains all the events of an execution that are competing and that are not ordered by [happens_before] in either direction *)

Definition cns E X :=
  fun e1 => fun e2 => competing E X e1 e2 /\
  ~ (happens_before E X e1 e2 \/ happens_before E X e2 e1).

(** In a well-formed event structure, with an execution valid on the weaker architecture [A1], if there are two events competing and not ordered by [happens_before] in either direction, then there exists another execution, valid on the stronger architecture [A2] (without barriers), on which the two events are still competing and not ordered by [happens_before] in either direction *)

Hypothesis hb_stable :
  forall E X x y,
  well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  competing E X x y ->
  ~ (happens_before E X x y \/ happens_before E X y x) ->
  (exists Y, A2nWmm.valid_execution E Y /\
  competing E Y x y /\ ~ (happens_before E Y x y \/ happens_before E Y y x)).

(** An execution is covered by a relation [r] if all the competing events of the execution are ordered by [r] in at least one direction *)

Definition covered E X r :=
  forall e1 e2, (competing E X e1 e2) -> (r E X e1 e2 \/ r E X e2 e1).




(** In a well-formed event structure, a relation [s] is _covering_ if, when it covers an execution valid on the weaker architecture [A1], the global happens-before relation of the execution on the stronger architecture [A2] is acyclic *)

Definition covering s :=
  forall E X, well_formed_event_structure E ->
    A1Wmm.valid_execution E X ->
    covered E X s -> acyclic (A2nWmm.ghb E X).

(*Hypothesis happens_before_fun :
  forall E X r,
  well_formed_event_structure E ->
  (exists s', covering s' /\
   (forall x y, happens_before E X x y /\ r x /\ r y -> s' E X x y) /\
   (forall E X init r x y,
    well_formed_event_structure E ->
    (s' E X x y /\ r x /\ r y <->
    s' (mkes init (Intersection Event (events E) r) (rrestrict (iico E) r))
    ((mkew (rrestrict (ws X) r) (rrestrict (rf X) r))) x y))).*)
End HappensBefore.

(** ** DRF Competing 

We define a module of type [Compete] with [happens_before] as a synchronisation relation. This makes the [Drf0] independant of the [sync] relation of the module of types [HappensBefore]. *)

Module Drf0 (HB:HappensBefore) <: Compete.

Definition competing := HB.competing.

(** In well-formed event structure, two competing events belong to the set of events of the event structure *)

Lemma compete_in_events :
  forall E X x y,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  competing E X x y ->
  events E x /\ events E y.
Proof.
intros E X x y Hwf Hrfwf [Hex [Hey ?]]; split; auto.
Qed.

(** Two events of an execution are related by [hbd] if they are related by the communication relation and if they are executed on different threads *)

Definition hbd E X :=
  fun e1 => fun e2 => com E X e1 e2 /\ proc_of e1 <> proc_of e2.

Definition cns := HB.cns.

Ltac destruct_valid H :=
  destruct H as [[Hws_tot Hws_cands] [[Hrf_init [Hrf_cands Hrf_uni]] [Hsp [Hth Hvalid]]]];
  unfold write_serialization_well_formed in Hws_tot(*; unfold uniproc in Hsp*).

(** The synchronisation relation of [Drf0] is [happens_before] *)

Definition s := HB.happens_before.

Definition covered := HB.covered.

(** In a well-formed event structure with a well-formed execution witness, if two events are related by the communication relation, at least one of them is a write *)

Lemma com_implies_write :
  forall E X x y,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  com E X x y ->
  writes E x \/ writes E y.
Proof.
intros E X x y Hwf [Hwswf Hrfwf] Hxy.
inversion Hxy as [Hrffr | Hws].
  inversion Hrffr as [Hrf | Hfr].
    destruct Hrfwf as [? [Hrfwf ?]].
    generalize (Hrfwf x y Hrf); intros [Hex [? [l [[v Hx] ?]]]].
    left; split; auto. exists l; exists v; auto.
    right; split.
      apply A2Basic.ran_fr_in_events with X x; auto.
      generalize (A2Basic.ran_fr_is_write Hwswf Hfr); intros [v [l Ha]];
      exists l; exists v; auto.
    right; split.
      apply A2Basic.ran_ws_in_events with X x; auto.
      generalize (A2Basic.ran_ws_is_write E X x y Hwswf Hws); intros [v [l Ha]];
      exists l; exists v; auto.
Qed.

(** In a well-formed event structure with a well-formed execution witness, if the union of the communication relation, and of the by-location program order is acyclic, then the happens-before relation is included in the union of [hbd] and of the program order *)

Lemma com_in_hbd_u_po :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  acyclic (rel_union (com E X) (pio_llh E)) ->
  rel_incl (com E X) (rel_union (hbd E X) (po_iico E)).
Proof.
intros E X Hwf Hs Huni x y Hhb.
inversion Hhb as [Hrffr | Hws].
  inversion Hrffr as [Hrf | Hfr].
    generalize (excluded_middle (proc_of x <> proc_of y)); intro Hor;
    inversion Hor as [Hdp | Hsp].
      left; split; auto.
      right; auto.
      assert (proc_of x = proc_of y) as Heq.
        apply NNPP; apply Hsp.
        assert (In _ (events E) x) as Hex.
          apply A2Basic.hb_domain_in_events with X y; auto.
        assert (In _ (events E) y) as Hey.
          apply A2Basic.hb_range_in_events with X x; auto.
        generalize (A2Basic.same_proc_implies_po x y Hwf Heq Hex Hey);
        intro Hpo; inversion Hpo as [Hxy | Hyx]; auto.
        assert (tc (rel_union (com E X) (pio_llh E)) x x) as Hcy.
          apply trc_ind with y; apply trc_step.
            left; auto. right; split; auto.
            apply sym_eq; apply A2Basic.com_implies_same_loc with E X; auto.
            split; auto.
            generalize Hs; intros [Hwswf [Hrfwf1 [Hrfwf2 Hrfwf3]]].
            generalize (A2Basic.dom_rf_is_write E X x y Hrfwf2 Hrf);
            intros [v [l Hwx]] [? [? [? [? Hrx]]]].
            rewrite Hwx in Hrx; inversion Hrx.
        assert False as Ht.
          unfold acyclic in Huni; apply (Huni x Hcy).
        inversion Ht.

    generalize (excluded_middle (proc_of x <> proc_of y)); intro Hor;
    inversion Hor as [Hdp | Hsp].
      left; split; auto.
      right; auto.
      assert (proc_of x = proc_of y) as Heq.
        apply NNPP; apply Hsp.
        assert (In _ (events E) x) as Hex.
          apply A2Basic.hb_domain_in_events with X y; auto.
        assert (In _ (events E) y) as Hey.
          apply A2Basic.hb_range_in_events with X x; auto.
        generalize (A2Basic.same_proc_implies_po x y Hwf Heq Hex Hey);
        intro Hpo; inversion Hpo as [Hxy | Hyx]; auto.
        assert (tc (rel_union (com E X) (pio_llh E)) x x) as Hcy.
          apply trc_ind with y; apply trc_step.
            left; auto. right; split; auto.
            apply sym_eq; apply A2Basic.com_implies_same_loc with E X; auto.
            split; auto.
            generalize Hs; intros [Hwswf Hrfwf].
            generalize (A2Basic.ran_fr_is_write Hwswf Hfr); intros [v [l Hwy]] [[? [? [? Hry]]]?].
            rewrite Hwy in Hry; inversion Hry.
        assert False as Ht.
          unfold acyclic in Huni; apply (Huni x Hcy).
        inversion Ht.

    generalize (excluded_middle (proc_of x <> proc_of y)); intro Hor;
    inversion Hor as [Hdp | Hsp].
      left; split; auto.
      right; auto.
      assert (proc_of x = proc_of y) as Heq.
        apply NNPP; apply Hsp.
        assert (In _ (events E) x) as Hex.
          apply A2Basic.hb_domain_in_events with X y; auto.
        assert (In _ (events E) y) as Hey.
          apply A2Basic.hb_range_in_events with X x; auto.
        generalize (A2Basic.same_proc_implies_po x y Hwf Heq Hex Hey);
        intro Hpo; inversion Hpo as [Hxy | Hyx]; auto.
        assert (tc (rel_union (com E X) (pio_llh E)) x x) as Hcy.
          apply trc_ind with y; apply trc_step.
            left; auto. right; split; auto.
            apply sym_eq; apply A2Basic.com_implies_same_loc with E X; auto.
            split; auto.
            generalize Hs; intros [Hwswf Hrfwf].
            generalize (A2Basic.ran_ws_is_write E X x y Hwswf Hws);
            intros [v [l Hwy]] [[? [? [? Hry]]]?].
            rewrite Hwy in Hry; inversion Hry.
        assert False as Ht.
          unfold acyclic in Huni; apply (Huni x Hcy).
        inversion Ht.
Qed.

(** In a well-formed event structure with a well-formed execution witness, if the union of the communication relation, and of the by-location program order is acyclic, then the [mhb] relation on the stronger architecture [A2] (without the barriers) is included in the union of [hbd] and of the program order *)

Lemma mhb2_in_hbd_po :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  acyclic (rel_union (com E X) (pio_llh E)) ->
  rel_incl (A2nWmm.mhb E X) (rel_union (hbd E X) (po_iico E)).
Proof.
intros E X Hwf Hs Hv x y Hmhb.
generalize (A2Basic.mhb_in_com E X x y Hmhb); intro Hhb.
apply com_in_hbd_u_po; auto.
Qed.

(** In a well-formed event structure with a well-formed execution witness, if the union of the communication relation, and of the by-location program order is acyclic, then the global happens-before relation on the stronger architecture [A2] (without the barriers) is included in the union of [hbd] and of the program order *)

Lemma ghb2_in_hbd_po :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  acyclic (rel_union (com E X) (pio_llh E)) ->
  rel_incl (A2nWmm.ghb E X) (rel_union (hbd E X) (po_iico E)).
Proof.
intros E X Hwf Hs Hv.
rewrite ghb2_is_mhb_ppo2.
intros x y Hxy; inversion Hxy as [Hmhb | Hppo].
apply mhb2_in_hbd_po; auto.
right; apply A2.ppo_valid; auto.
Qed.

(** In a well-formed event structure with a well-formed execution witness, if the union of the communication relation, and of the by-location program order is acyclic, then the transitive closure of the global happens-before relation on the stronger architecture [A2] (without the barriers) is included in the union of [hbd] and of the program order *)

Lemma tc_ghb2_in_tc_hbd_po :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  acyclic (rel_union (com E X) (pio_llh E)) ->
  rel_incl (tc (A2nWmm.ghb E X)) (tc (rel_union (hbd E X) (po_iico E))).
Proof.
intros E X Hwf Hs Hv; apply tc_incl; apply ghb2_in_hbd_po; auto.
Qed.

(** In a well-formed event structure with a well-formed execution witness, the [hbd] relation is included in the competing events relation *)

Lemma hbd_in_compete :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  rel_incl (hbd E X) (competing E X).
Proof.
intros E X Hwf Hs x y [Hhb Hdp]. split; [|split; [|split; [|split]]]; auto.
- change (events E x) with (In _ (events E) x);
  apply A2Basic.hb_dom_in_evts with X y; auto.
- change (events E y) with (In _ (events E) y);
  apply A2Basic.hb_ran_in_evts with X x; auto.
- apply A2Basic.com_implies_same_loc with E X; auto.
- apply com_implies_write with X; auto.
Qed.

(** In a well-formed event structure with a well-formed execution witness, if an execution is covered by the synchronisation relation, then the [hbd] relation is included in the [happens_before] relation *)

Lemma drf_hbd_in_sync :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  covered E X s ->
  rel_incl (hbd E X) (HB.happens_before E X).
Proof.
intros E X Hwf Hs Hdrf x y Hxy.
generalize (hbd_in_compete Hwf Hs Hxy); intro Hcomp.
generalize (Hdrf x y Hcomp); intro Hor; auto.
inversion Hor; auto.
destruct Hxy as [Hhb ?].
  generalize (HB.happens_before_compat_com Hhb); intro;
  contradiction.
Qed.

(** In a well-formed event structure with a well-formed execution witness, if an execution is covered by the synchronisation relation, then the transitive closure of the union of the [hbd] relation and of the program order is included in the [happens_before] relation *)

Lemma tc_drf_hbd_u_po_in_tc_sync_u_po :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
 (* wf_sync E X ->*) covered E X s ->
  rel_incl (tc (rel_union (hbd E X) (po_iico E)))
    (HB.happens_before E X).
Proof.
intros E X Hwf Hs (*Hwfs*) Hdrf.
  intros x y Hxy.
  induction Hxy as [x y Hst | x z y Htc].
    inversion Hst as [Hhbd | Hpo].
      generalize Hhbd; apply drf_hbd_in_sync; auto.
      unfold HB.happens_before; apply trc_step; left; auto.
      unfold HB.happens_before; apply trc_ind with y; auto.
Qed.

(** In a well-formed event structure with a well-formed execution witness, if:

- The union of the communication relation and of the by-location program order is acyclic
- The execution is covered by the synchronisation relation
- There is a cycle in the global happens-before relation of the execution on the stronger architecture [A2] (without the barriers)

Then there is a cycle in the union of [happens_before] and of the program order
*)

Lemma sync_thm :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  acyclic (rel_union (com E X) (pio_llh E)) ->
    (covered E X s -> (exists x, tc (A2nWmm.ghb E X) x x) ->
      exists y, tc (rel_union (HB.happens_before E X) (po_iico E)) y y).
Proof.
intros E X Hwf Hs Huni Hp [x Hx].
generalize (tc_ghb2_in_tc_hbd_po Hwf Hs Huni); intro Hincl.
generalize (Hincl x x Hx); intro Hu.
generalize (tc_drf_hbd_u_po_in_tc_sync_u_po Hwf Hs Hp Hu); intro Hhb.
exists x; apply trc_step; left; unfold s; auto.
Qed.

(** In any execution, the transitive closure of the union of [happens_before] and of the program order is included in [happens_before] *)

Lemma hb_u_po_is_hb :
  forall E X,
  rel_incl (tc (rel_union (HB.happens_before E X) (po_iico E))) (HB.happens_before E X).
Proof.
unfold HB.happens_before; intros E X x y Hxy;
induction Hxy.
  inversion H as [Hhb | Hpo]; auto.
    apply trc_step; left; auto.
    apply trc_ind with z; auto.
Qed.

(** In a well-formed event structure and in an execution valid on the weaker architecture [A1], there exists a relation such that:

- The union of this relation with the synchronisation relation is acyclic
- If the execution is covered and the global happens-before of the execution on the stronger architrecture [A2] (without the barriers) contains a cycle, then there is a cycle in the union of this relation and of the synchronisation relation *)

Lemma convoluted_covering_holds :
  forall E X, 
    well_formed_event_structure E ->
    A1Wmm.valid_execution E X ->
    exists r,
    (acyclic (rel_union (s E X) r)) /\
    (covered E X s -> (exists x, tc (A2nWmm.ghb E X) x x) ->
      exists y, tc (rel_union (s E X) r) y y).
Proof.
intros E X Hwf Hv1; exists (po_iico E); unfold s;
  split; [ | intro Hp].
    unfold acyclic; intros x Hx.
    generalize (hb_u_po_is_hb Hx); intro Hhb.
    apply (HB.happens_before_irr Hwf Hv1 Hhb).
  destruct_valid Hv1; apply sync_thm; auto.
  split; split; auto.
Qed.

Definition covering s :=
  forall E X, well_formed_event_structure E ->
    A1Wmm.valid_execution E X ->
    covered E X s -> acyclic (A2nWmm.ghb E X).

(** In a well-formed event structure and in an execution valid on the weaker architecture [A1] and covered by the synchronisation relation, the global happens-before relation of the execution on the stronger architecture [A2] (without the barriers) is acyclic *)

Lemma covering_s :
  forall E X, well_formed_event_structure E ->
    A1Wmm.valid_execution E X ->
    covered E X s -> acyclic (A2nWmm.ghb E X).
Proof.
intros E X Hwf Hv1 Hc x Hx.
generalize (convoluted_covering_holds Hwf Hv1); intros [r [Hacsr Himpl]].
assert (exists x, tc (A2nWmm.ghb E X) x x) as Hcx.
  exists x; auto.
generalize (Himpl Hc Hcx); intros [y Hy].
apply (Hacsr y Hy).
Qed.

(* In a well-formed event structure and in an execution valid on the weaker architecture [A1], an event cannot be competing with itself *)

Lemma competing_irr : forall E X,
  well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  ~ (exists z, competing E X z z).
Proof.
intros E X Hwf Hv [z [? [? [? [Hdp ?]]]]].
apply Hdp; trivial.
Qed.

(* In a well-formed event structure and in an execution valid on the weaker architecture [A1], an event cannot occur in the program order after an event he is competing with *)

Lemma competing_not_po :
  forall E X x y,
  well_formed_event_structure E ->
    A1Wmm.valid_execution E X ->
  competing E X x y -> ~ (po_iico E y x).
Proof.
intros E X x y Hwf Hv [? [? [? [Hdp ?]]]] Hpo.
assert (In _ (events E) x) as Hx.
  apply A2nBasic.po_iico_range_in_events with y; auto.
assert (In _ (events E) y) as Hy.
  apply A2nBasic.po_iico_domain_in_events with x; auto.
generalize (A2nBasic.po_implies_same_proc Hwf Hy Hx Hpo); intro Heq;
subst; auto.
Qed.

(*
Lemma competing_fun :
  forall E X r x y,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  (competing E X x y /\ r x /\ r y <->
  competing (mkes
  (fun w : Event =>
           (exists e : Event, rf X w e /\ r e /\ ~ r w) \/ wmm.init E w)
   (Intersection Event (events E) r) (rrestrict (iico E) r))
    ((mkew (rrestrict (ws X) r) (rrestrict (rf X) r))) x y).
(*  forall E X init r x y,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  (competing E X x y /\ r x /\ r y <->
  competing (mkes init (Intersection Event (events E) r) (rrestrict (iico E) r))
    ((mkew (rrestrict (ws X) r) (rrestrict (rf X) r))) x y).*)
Proof.
intros E X r x y Hwf Hrfwf; unfold competing; split; intro Hxy.
  destruct Hxy as [[Hex [Hey [Hl [Hp Hw]]]] [Hrx Hry]];
    split; [|split; [|split; [|split]]]; auto.
      split; auto. split; auto.
      inversion Hw as [Hwx | Hwy]; [destruct Hwx; left | destruct Hwy; right]; split; auto.
      split; auto. split; auto.

  destruct Hxy as [Hex [Hey [Hl [Hp Hw]]]];
    split; [split; [|split; [|split; [|split]]] |]; auto.
    destruct Hex; auto. destruct Hey; auto.
      inversion Hw as [Hwx | Hwy]; [destruct Hwx; left | destruct Hwy; right]; split; auto.
      destruct Hex; auto. destruct Hey; auto.
    destruct Hex; auto. destruct Hey; auto.
Qed.    *)

(*Lemma s_fun :
  forall E X r,
  well_formed_event_structure E ->
  (exists s', covering s' /\
   (forall x y, s E X x y /\ r x /\ r y -> s' E X x y) /\
   (forall E X init r x y,
    well_formed_event_structure E ->
    (s' E X x y /\ r x /\ r y <->
    s' (mkes init (Intersection Event (events E) r) (rrestrict (iico E) r))
    ((mkew (rrestrict (ws X) r) (rrestrict (rf X) r))) x y))).
Proof.
unfold s; intros E X r Hwf.
apply HB.happens_before_fun; auto.
Qed.*)

End Drf0.

(** ** DRF Guarantee *)

Module DrfGuarantee (HB:HappensBefore).
Module Drf := Drf0 HB.
Module Pres := Preservation Drf.
Import Pres.

(** In a well-formed event structure, with an execution valid on the weaker architecture [A1], if the execution is not covered by [happens_before], then there is another execution, valid on the stronger architecture [A2], which isn't covered either *)

Lemma a1_uncovered_implies_a2_uncovered:
  forall E X,
  well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  ~(HB.covered E X HB.happens_before) ->
  (exists Y, A2nWmm.valid_execution E Y /\
             ~(HB.covered E Y HB.happens_before)).
Proof.
intros E X Hwf Hval1 Huncov; unfold HB.covered in Huncov; unfold HB.covered.
apply not_all_ex_not in Huncov. destruct Huncov as [x Huncov].
apply not_all_ex_not in Huncov. destruct Huncov as [y Huncov].
apply imply_to_and in Huncov. destruct Huncov as [Hcomp Hhb].
destruct (HB.hb_stable Hwf Hval1 Hcomp Hhb) as [Y [Hval2 Hcomp2]].
exists Y; split; auto.
apply ex_not_not_all. exists x. apply ex_not_not_all. exists y.
intros H. destruct Hcomp2 as [Hcomp2 Hhb2]. apply H in Hcomp2.
auto.
Qed.

(** In a well-formed event structure, if all the executions valid on the stronger architecture [A2] (without the barriers) are covered by [happens_before], then all the executions valid on the weaker architecture are valid on the stronger architecture *)

Lemma drf_guarantee :
  (forall E X, A2nWmm.valid_execution E X -> Drf.covered E X Drf.s) ->
  (forall E X, well_formed_event_structure E ->
   (A1Wmm.valid_execution E X <-> A2nWmm.valid_execution E X)).
Proof.
intros Hcov E X Hwf; split; intros Hval.
- unfold A1Wmm.valid_execution in Hval; destruct Hval as [Hrf [Hws [Huproc [Hoota Hac]]]].
  unfold A2nWmm.valid_execution; repeat (try (split; auto)).
  apply Drf.covering_s; auto.
  unfold A1Wmm.valid_execution; repeat (try (split; auto)).
  destruct (classic (Drf.covered E X Drf.s)) as [Hcovd|Hcovd]; auto.
  assert (A1Wmm.valid_execution E X) as Hval1.
  { unfold A1Wmm.valid_execution; repeat (try (split;auto)). }
  destruct (a1_uncovered_implies_a2_uncovered Hwf Hval1 Hcovd) as [Y [Hval2 Huncov]].
  apply Hcov in Hval2. apply Huncov in Hval2. destruct Hval2.
- apply validity_decr; auto.
Qed.

End DrfGuarantee.

End DataRaceFree.
