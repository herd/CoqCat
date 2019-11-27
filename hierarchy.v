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
Set Implicit Arguments.

Axiom excluded_middle : forall (A:Prop), A \/ ~A.

Definition bimpl (b1 b2:bool) : Prop:=
  if (negb b1) || b2 then True else False.

(* Module Hierarchy. *)

(** * Memory models comparison

In this file, we define the notion of _comparison_ between memory models. In
particular, we define what it means for a model to be weaker than another model.

The module [Weaker] takes two architectures and a dependencies module as
parameters, and defines a predicate [weaker] that is true when the first
architecture is weaker than the second.

It then states different kind of variations of these architectures, and lemmas
about how they compare.
*)

Module Weaker (A1 A2 : Archi) (dp:Dp).

(** ** Definition of [weaker] *)

(** We define for both A1 and A2 a relation bot_ghb that corresponds to the
union of the write serialization, from-read and preserved program order
(according to A1 or A2 respectively). This relation corresponds to the
instanciation of [bot_ghb] for each architecture, if we consider the barrier
relation to be empty for both architectures *)

Definition bot_ghb1 (E:Event_struct) (X:Execution_witness) :=
         (rel_union (rel_union (ws X) (fr E X)) (A1.ppo E)).
Definition bot_ghb2 (E:Event_struct) (X:Execution_witness) :=
        (rel_union (rel_union (ws X) (fr E X)) (A2.ppo E)).

(* Definition rf_impl (rf1 rf2 : bool) :=
    bimpl rf1 rf2. *)

(** The preserved program order of a first architecture is included in the one
of a second architecture if for any event structure, the preserved program order
relation produced by the first architecture is included in the preserved program
order relation produced by the second architecture *)

Definition ppo_incl (ppo1 ppo2 : Event_struct -> Rln Event) :=
  forall E, rel_incl (ppo1 E) (ppo2 E).

(** A first architecture is weaker than a second one, if:

- The preserved program order of the first architecture is included in the
preserved program order of the second architecture
- Every subset of read-from considered non-global in the first architecture is
also considered non-global in the second architecture. In other words, the
global read-from of the first architecture is included in the global read-from
of the second architecture *)

Definition weaker :=
  ppo_incl (A1.ppo) (A2.ppo) /\
  bimpl (A1.intra) (A2.intra) /\
  bimpl (A1.inter) (A2.inter) .

Ltac destruct_wk H :=
  destruct H as [Hppoi [Hrfii Hrfei]].

Import A1. Import A2. Import dp.

(** We import the basic facts about these two architectures *)

Module A1Basic := Basic A1 dp.
Import A1Basic.
Module A2Basic := Basic A2 dp.
Import A2Basic.

(** We build the weak memory models corresponding to these two architectures *)

Module A1Wmm := Wmm A1 dp.
Import A1Wmm.
Module A2Wmm := Wmm A2 dp.
Import A2Wmm.

(** ** Architectures without barriers

A1n and A2n are two variants of respectively A1 and A2 where we consider that
there are no barriers on the architectures *)

Module A1n <: Archi.

(** The notion of preserved program order is identical to the one of A1 *)

Definition ppo := A1.ppo.

Lemma ppo_valid : forall E, rel_incl (ppo E) (po_iico E).
Proof.
  apply A1.ppo_valid.
Qed.

Lemma ppo_fun :
  forall E s x y,
  ppo E x y /\ s x /\ s y <->
  ppo (mkes (Intersection Event (events E) s) (rrestrict (iico E) s)) x y.
Proof.
apply A1.ppo_fun.
Qed.

(** The part of read-from that are global are the same than in A1 *)

Definition inter := A1.inter.
Definition intra := A1.intra.

(** There are no events related by the barrier relation *)

Definition abc (E:Event_struct) (X:Execution_witness) : Rln Event :=
  fun e1 => fun e2 => False.

(** The necessary property on the events related by the barrier relation is
trivial since no events are related by the relation  *)

Lemma ab_evts : forall (E:Event_struct) (X:Execution_witness),
  forall x y, well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  abc E X x y -> In _ (events E) x /\ In _ (events E) y.
Proof.
intros E X x y Hwf Hrf Hxy. inversion Hxy.
Qed.

(** Since the barrier relation is empty, it is trivially included in the
transitive closure of the union of happens-before and program order for any
event structure and any execution witness *)

Lemma ab_incl :
  forall E X, rel_incl (abc E X) (tc (rel_union (hb E X) (po_iico E))).
Proof.
intros E X x y Hxy. inversion Hxy.
Qed.

(* As in wmm, what this represents is not really clear, and it is used nowhere
so I comment it, but we should eventually clarify what it means *)

(*
Lemma ab_fun :
  forall E X s x y,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  (abc E X x y /\ s x /\ s y <->
  abc (mkes (Intersection Event (events E) s) (rrestrict (iico E) s))
    (mkew (rrestrict (ws X) s) (rrestrict (rf X) s)) x y).
Proof.
intros E X s x y ? ?; split.
 intros [Hxy ?]; inversion Hxy.
 intro Hxy; inversion Hxy.
Qed.
*)

Parameter stars : Event_struct -> set Event.
End A1n.

(** The A2n module is exactly the same as A1n, except A1 is replaced by A2 *)

Module A2n <: Archi.

(** The notion of preserved program order is identical to the one of A2 *)

Definition ppo := A2.ppo.

Lemma ppo_valid : forall E, rel_incl (ppo E) (po_iico E).
Proof.
  apply A2.ppo_valid.
Qed.

Lemma ppo_fun :
  forall E s x y,
  ppo E x y /\ s x /\ s y <->
  ppo (mkes (Intersection Event (events E) s) (rrestrict (iico E) s)) x y.
Proof.
  apply A2.ppo_fun.
Qed.

(** The part of read-from that are global are the same than in A2 *)

Definition inter := A2.inter.
Definition intra := A2.intra.

(** There are no events related by the barrier relation *)

Definition abc (E:Event_struct) (X:Execution_witness) : Rln Event :=
  fun e1 => fun e2 => False.

(** The necessary property on the events related by the barrier relation is
trivial since no events are related by the relation  *)

Lemma ab_evts : forall (E:Event_struct) (X:Execution_witness),
  forall x y, well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  abc E X x y -> In _ (events E) x /\ In _ (events E) y.
Proof.
intros E X x y Hwf Hrf Hxy. inversion Hxy.
Qed.

(** Since the barrier relation is empty, it is trivially included in the
transitive closure of the union of happens-before and program order for any
event structure and any execution witness *)

Lemma ab_incl :
  forall E X, rel_incl (abc E X) (tc (rel_union (hb E X) (po_iico E))).
Proof.
intros E X x y Hxy. inversion Hxy.
Qed.

(* As in wmm, what this represents is not really clear, and it is used nowhere
so I comment it, but we should eventually clarify what it means *)

(* Lemma ab_fun :
  forall E X s x y,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  (abc E X x y /\ s x /\ s y <->
  abc (mkes (Intersection Event (events E) s) (rrestrict (iico E) s))
    (mkew (rrestrict (ws X) s) (rrestrict (rf X) s)) x y).
Proof.
intros E X init s x y; split.
  intros [Hxy ?]; inversion Hxy.
  intro Hxy; inversion Hxy.
Qed.
*)

Parameter stars : Event_struct -> set Event.

End A2n.

Import A1n. Import A2n. Import dp.

(** We import basic facts about A1n and A2n *)

Module A1nBasic := Basic A1n dp.
Import A1nBasic.
Module A2nBasic := Basic A2n dp.
Import A2nBasic.

(** We build the memory models corresponding to A1n and A2n *)

Module A1nWmm := Wmm A1n dp.
Import A1nWmm.
Module A2nWmm := Wmm A2n dp.
Import A2nWmm.

(** ** Characterisation

We characterise how validity is preserved or not preserved between two memory
models based on two architectures, such that one is weaker than the other *)

Section Char.

(** We define [check] as the acyclicity of the union of the global read-from
of the memory model based on A2n, and of [bot_ghb2].

This union corresponds to the global happens-before ([ghb]) of the memory model
based on A2n (as stated later by [ghb2_eq])

Thus, this acyclicity condition corresponds to the third part of the conditions
of [valid_execution] (the two others being out-of-thin-air and uniproc
conditions.

NOTE: In this definition, [mrf] corresponds to [A2nWmm.mrf]
*)

Definition check (E:Event_struct) (X:Execution_witness) :=
  acyclic (rel_union (mrf X) (bot_ghb2 E X)).

(** If A1 is weaker than A2, [bot_ghb1] is included in [bot_ghb2]. *)

Lemma bot_ghb_incl :
  forall E X,
  weaker ->
  rel_incl (bot_ghb1 E X) (bot_ghb2 E X).
Proof.
unfold bot_ghb1; unfold bot_ghb2;
intros E X H12 x y Hxy;
destruct_wk H12.
    inversion Hxy as [Hws_fr | Hre].
      left; auto.
      right; apply (Hppoi E x y Hre).
Qed.

(**
The global happens-before of A2n is equal to the union of its [mhb] (its happens
before relation where only global read-froms are considered) and of its
preserved program order.

NOTE: In this lemma, [ghb] corresponds to [A2nWmm.ghb]
*)

Lemma ghb2_is_mhb_ppo2 :
  forall E X,
  ghb E X = rel_union (mhb E X) (A2.ppo E).
Proof.
case_eq inter; case_eq intra; intros Hinter Hintra;
unfold ghb; unfold mhb; rewrite Hinter; rewrite Hintra;
unfold abc; intros E X; apply ext_rel; split; intro Hxy; auto.

  inversion Hxy as [Hrfe | Hr].
    left; left; auto.
    inversion Hr as [Hrfi | Hre].
      left; right; left; auto.
      inversion Hre as [Ht | Hres].
        inversion Ht.
        inversion Hres as [Hws_fr | Hppo].
          left; right; right; auto.
            right; auto.

  inversion Hxy as [Hr | Hppo].
    inversion Hr as [Hrfe | Hre].
      left; auto.
      inversion Hre as [Hrfi | Hws_fr].
        right ; left; auto.
          right; right; right; left; auto.
          right; right; right; right; auto.

  inversion Hxy as [Hrfi | Hr].
      left; left; auto.
      inversion Hr as [Ht | Hre].
        inversion Ht.
        inversion Hre as [Hws_fr | Hppo].
          left; right; auto.
            right; auto.

  inversion Hxy as [Hr | Hppo].
    inversion Hr as [Hrfi | Hre].
      left; auto.
          right; right; left; auto.
          right; right; right; auto.

  inversion Hxy as [Hrfi | Hr].
      left; left; auto.
      inversion Hr as [Ht | Hre].
        inversion Ht.
        inversion Hre as [Hws_fr | Hppo].
          left; right; auto.
            right;auto.

  inversion Hxy as [Hr | Hppo].
    inversion Hr as [Hrfi | Hre].
      left; auto.
          right; right; left; auto.
          right; right; right; auto.

  inversion Hxy as [Ht | Hre].
        inversion Ht.
        inversion Hre as [Hws_fr | Hppo].
          left; auto.
            right; auto.

  inversion Hxy as [Hws_fr | Hppo].
          right; left; auto.
          right; right; auto.
Qed.

(**
The global happens-before of A2n corresponds to the union of its global
read-from and of [bot_ghb2].

NOTE: In this lemma, [mrf] corresponds to [A2nWmm.mrf]
*)

Lemma ghb2_eq :
  forall E X,
  ghb E X = rel_union (mrf X) (bot_ghb2 E X).
Proof.
case_eq inter; case_eq intra; intros Hinter Hintra;
unfold ghb; unfold mrf; unfold mrfe; unfold mrfi; rewrite Hinter; rewrite Hintra;
unfold bot_ghb2;
unfold abc; intros E X; apply ext_rel; split; intro Hxy; auto.

  inversion Hxy as [Hrfe | Hr].
    left; simpl; right; auto.
    inversion Hr as [Hrfi | Hre].
      left; simpl; left; auto.
      inversion Hre as [Ht | Hres].
        inversion Ht.
        right; auto.

  inversion Hxy as [Hrf | Hor].
    inversion Hrf as [Hrfi | Hrfe].
      right; simpl; left; auto.
      left; auto.
        right; right; right; auto.

  inversion Hxy as [Hrfi | Hor].
      left; right; auto.
          inversion Hor as [Ht | Hbghb].
            inversion Ht.
            right; auto.

  inversion Hxy as [Hrf | Hr].
    inversion Hrf as [Hrfi | Hrfe].
      inversion Hrfi.
      left; auto.
           right; right;auto.

  inversion Hxy as [Hrfi | Hor].
      left; left; auto.
          inversion Hor as [Ht | Hbghb].
            inversion Ht.
            right; auto.

  inversion Hxy as [Hrf | Hor].
    inversion Hrf as [Hrfi | Hrfe].
      left; auto.
      inversion Hrfe.
          right; right; auto.

  inversion Hxy as [Ht | Hre].
        inversion Ht.
            right; auto.

  inversion Hxy as [Hort | Hor].
    inversion Hort; inversion H.
       right; auto.
Qed.

(** If A1 is weaker than A2, the global happens-before of A1n is included in the
global happens-before of A2n. *)

Lemma ghb_incl :
  forall E X,
  weaker ->
  rel_incl (A1nWmm.ghb E X) (A2nWmm.ghb E X).
Proof.
intros E X; rewrite (ghb2_eq E X).
unfold A1nWmm.ghb; unfold A1n.ppo; unfold mrf; unfold mrfe; unfold mrfi;
intros H12 x y Hxy; case_eq inter; case_eq intra;
intros Hintra2 Hinter2; case_eq A1n.inter; case_eq A1n.intra;
intros Hintra1 Hinter1; rewrite Hintra1 in *; rewrite Hinter1 in *.
  (*A1 : true true ; A2 : true true*)
  inversion Hxy as [Hrfi | Hr].
    left; right; auto.
    inversion Hr as [Hrfi | Hre].
      left; left; auto.
      inversion Hre as [Ht | Hres].
        inversion Ht.
      right; fold (bot_ghb1 E X) in Hres.
      apply bot_ghb_incl; auto.
  (*A1 : false true ; A2 : true true*)
  inversion Hxy as [Hrfe | Hr].
    left; right; auto.
      inversion Hr as [Ht | Hres].
        inversion Ht.
      right; fold (bot_ghb2 E X); fold (bot_ghb1 E X) in Hr;
      apply bot_ghb_incl; auto.
  (*A1 : true false ; A2 : true true*)
  inversion Hxy as [Hrfi | Hr].
    left; left; auto.
      inversion Hr as [Ht | Hres].
        inversion Ht.
      right; fold (bot_ghb2 E X); fold (bot_ghb1 E X) in Hr;
      apply bot_ghb_incl; auto.
  (*A1 : false false ; A2 : true true*)
      inversion Hxy as [Ht | Hres].
        inversion Ht.
      right; fold (bot_ghb2 E X); fold (bot_ghb1 E X) in Hres;
      apply bot_ghb_incl; auto.
  (*A1 : true true ; A2 : false true*)
  destruct H12 as (*[?*) [? [Himpl ?]](*]*).
  unfold A1n.intra in Hintra1; unfold A2n.intra in Hintra2;
  rewrite Hintra1 in Himpl; rewrite Hintra2 in Himpl; inversion Himpl.
  (*A1 : false true ; A2 : false true*)
  inversion Hxy as [Hrfe | Hr].
    left; right; auto.
      inversion Hr as [Ht | Hres].
        inversion Ht.
      right; fold (bot_ghb2 E X); fold (bot_ghb1 E X) in Hres;
      apply bot_ghb_incl; auto.
  (*A1 : true false ; A2 : false true*)
  destruct H12 as (*[?*) [? [Himpl ?]] (*]*).
  unfold A1n.intra in Hintra1; unfold A2n.intra in Hintra2;
  rewrite Hintra1 in Himpl; rewrite Hintra2 in Himpl; inversion Himpl.
  (*A1 : false false ; A2 : false true*)
      inversion Hxy as [Ht | Hres].
        inversion Ht.
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
        inversion Ht.
      right; fold (bot_ghb2 E X); fold (bot_ghb1 E X) in Hres;
      apply bot_ghb_incl; auto.
  (*A1 : false false ; A2 : true false *)
      inversion Hxy as [Ht | Hres].
        inversion Ht.
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
  destruct H12 as (*[?*) [? [Himpl ?]](*]*).
  unfold A1n.intra in Hintra1; unfold A2n.intra in Hintra2;
  rewrite Hintra1 in Himpl; rewrite Hintra2 in Himpl; inversion Himpl.
  (*A1 : false false ; A2 : false false*)
      inversion Hxy as [Ht | Hres].
        inversion Ht.
      right; fold (bot_ghb2 E X); fold (bot_ghb1 E X) in Hres;
      apply bot_ghb_incl; auto.
Qed.

(** If A1 is weaker than A2, then a valid execution on A2n is also valid on
A1n *)

Lemma v2_implies_v1 :
  forall E X,
  weaker ->
  A2nWmm.valid_execution E X ->
  A1nWmm.valid_execution E X.
Proof.
intros E X H21 Hv1.
destruct_valid Hv1.
 split; auto; [ |split; auto; split; auto].
split; auto; split; auto.
split; auto.
eapply incl_ac; [apply ghb_incl; auto | apply Hvalid].
Qed.

(** If A1 is weaker than A2, then a valid execution on A2n is also valid on
A1n, and the execution verifies the [check] condition *)

Lemma A2_impl_A1_check :
  forall E X,
  weaker ->
  A2nWmm.valid_execution E X ->
  A1nWmm.valid_execution E X /\ check E X.
Proof.
intros E X Hincl Hv2.
  split; [apply v2_implies_v1; auto |].
    destruct_valid Hv2; unfold check.
rewrite (ghb2_eq E X) in Hvalid; auto.
Qed.

(** If A1 is weaker than A2, then a valid execution on A1n that verifies the
[check] condition, is valid on A2n *)

Lemma A1_check_impl_A2 :
  forall E X,
  weaker ->
  A1nWmm.valid_execution E X /\ check E X ->
  A2nWmm.valid_execution E X.
Proof.
intros E X Hincl [Hv1 Hc2].
  destruct_valid Hv1; split; auto; split; auto; split; auto.
    split.
    auto.
    rewrite (ghb2_eq E X); unfold check in Hc2; auto.
Qed.

(** If A1 is weaker than A2, being a valid execution on A1n and verifying the
[check] condition is equivalent to being a valid execution on A2n *)

Lemma charac :
  forall E X,
  weaker ->
  ((A1nWmm.valid_execution E X /\ check E X) <->
    (A2nWmm.valid_execution E X)).
Proof.
intros E X; split; [intros [Hv1 Hc2] | intro Hv2].
  apply A1_check_impl_A2; auto.
  apply A2_impl_A1_check; auto.
Qed.

End Char.

(** ** Barriered architecture 

We define a version of A1 where the barriers relation is left as a parameter of
the module
*)

Module A1b <: Archi.

(** The preserved program order is the same as the one of A1 *)

Definition ppo := A1.ppo.

Lemma ppo_valid : forall E, rel_incl (ppo E) (po_iico E).
  apply A1.ppo_valid.
Qed.

Lemma ppo_fun :
  forall E s x y,
  ppo E x y /\ s x /\ s y <->
  ppo (mkes (Intersection Event (events E) s) (rrestrict (iico E) s)) x y.
Proof.
  apply A1.ppo_fun.
Qed.

(** The part of read-from that are global are the same than in A1 *)

Definition inter := A1.inter.
Definition intra := A1.intra.

(** The barrier relation is left as a parameter *)

Parameter abc : Event_struct -> Execution_witness -> Rln Event.

(** In a well-formed event structure with a well-formed read-from relation, two
events related by the barrier relation must belong to the set of events of the
event structure *)

Hypothesis ab_evts : forall (E:Event_struct) (X:Execution_witness),
  forall x y, well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  abc E X x y -> In _ (events E) x /\ In _ (events E) y.

(** For every execution, the barrier relation must be included in the transtive
closure of the union of happens-before and program order *)

Hypothesis ab_incl :
  forall E X, rel_incl (abc E X) (tc (rel_union (hb E X) (po_iico E))).

(* As in wmm, what this represents is not really clear, and it is used nowhere
so I comment it, but we should eventually clarify what it means *)

(*
Hypothesis ab_fun :
  forall E X s x y,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  (abc E X x y /\ s x /\ s y <->
  abc (mkes (Intersection Event (events E) s) (rrestrict (iico E) s))
    (mkew (rrestrict (ws X) s) (rrestrict (rf X) s)) x y).
*)

Parameter stars : Event_struct -> set Event.

End A1b.

(** For a given event structure E, [ppo_sub E] is the part of the program order
of E that is preserved by A2 but not by A1 *)

Definition ppo_sub E :=
  rel_sub (A1.ppo E) (A2.ppo E).

(** We define the notion of intra-thread, inter-thread and global read-froms 
for A2 *)

Definition mrfi2 X :=
  mrel (A2.intra) (rf_intra X).
Definition mrfe2 X :=
  mrel (A2.inter) (rf_inter X).
Definition mrf2 X :=
  rel_union (mrfi2 X) (mrfe2 X).

(** We define the notion of intra-thread, inter-thread and global read-froms
for A1 *)

Definition mrfi1 X :=
  mrel (A1.intra) (rf_intra X).
Definition mrfe1 X :=
  mrel (A1.inter) (rf_inter X).
Definition mrf1 X :=
  rel_union (mrfi1 X) (mrfe1 X).

(** For a given execution, [rf_sub X] is the part of the read-froms that are
considered global on A2 but not on A1 *)

Definition rf_sub X :=
  rel_sub (mrf1 X) (mrf2 X).

Import A1b.

(** We import basic facts about A1b *)

Module A1bBasic := Basic A1b dp.
Import A1bBasic.

(** We build a memory model on A1b *)

Module A1bWmm := Wmm A1b dp.
Import A1bWmm.

Import A2n. Import A2nBasic. Import A2nWmm.

Section Barriers.

(** We say that an execution is fully barriered when all the events that:

- are ordered by A2 but not by A1
- are ordered by a sequence of read-from and preserver program order on A2 but
not on A1

are ordered by the barriers on A1 *)

Definition fully_barriered (E:Event_struct) (X:Execution_witness) :=
  rel_incl (rel_union (ppo_sub E) (rel_seq (rf_sub X) (A2.ppo E))) (A1b.abc E X).

(** The global happens-before of the memory model based on [A1b] is the union of
the write serialization, the from-read relation, the preserved program order of
A1, the global read-from of A1 and of the barrier relation of A1 *)

Lemma ghb1b_eq :
  forall E X,
  A1bWmm.ghb E X = rel_union (rel_union (ws X) (fr E X))
                                        (rel_union (rel_union (mrf1 X) (A1.ppo E))
                                            (A1b.abc E X)) .
Proof.
intros E X; unfold A1bWmm.ghb; unfold mrf1; unfold mrfi1; unfold mrfe1;
  unfold A1b.ppo; unfold A1b.inter; unfold A1b.intra;
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

(** If A1 is weaker than A2, in a well-formed event structure, the [mhb'] 
relation of A2n is the union of:

- the [mhb'] of A1b
- the read-froms that are global in A2 but not in A1
- the sequence of write serialization and the read-froms global in A2 but not in
A1
- the sequence of from-read and the read-froms global in A2 but not in A1 *)

Lemma mhb'2_is_mhb'1_u_rf_sub :
  forall E X,
  weaker ->
  well_formed_event_structure E ->
  (A2nWmm.mhb' E X) =
  rel_union (rel_union (A1bWmm.mhb' E X) (rf_sub X))
    (rel_union (rel_seq (ws X) (rf_sub X)) (rel_seq (fr E X) (rf_sub X))).
Proof.
case_eq A2.inter; case_eq A2.intra; intros Hinter2 Hintra2;
case_eq A1.inter; case_eq A1.intra; intros Hinter1 Hintra1;
unfold mhb'; unfold mhb; unfold rf_sub;
unfold A1bWmm.mhb'; unfold A1bWmm.mhb;
unfold A1bWmm.mrf; unfold mrf; unfold A1bWmm.mrfi; unfold mrfi;
unfold A1bWmm.mrfe; unfold mrfe; unfold inter; unfold intra;
unfold A1b.inter; unfold A1b.intra; unfold mrf1; unfold mrf2;
unfold mrfi1; unfold mrfi2; unfold mrfe1; unfold mrfe2;
rewrite Hinter1; rewrite Hintra1; rewrite Hinter2; rewrite Hintra2;
unfold abc; intros E X Hwk Hwf; apply ext_rel; split; intro Hxy; auto;
simpl in * |- *.

inversion Hxy as [Hr | Hsfr].
  inversion Hr as [Hre | Hsws].
  inversion Hre as [Hrfe | Hres].
  left; left; left; left; auto.
  inversion Hres as [Hrfi | Hws_rf].
    left; left; left; left; auto.
    left; left; left; left; right; auto.
  left; left; left; right; auto.
  left; left; right; auto.

inversion Hxy as [Hu | Hssub].
  inversion Hu as [Hr | Hsub].
    inversion Hr as [Hhbs | Hsfr].
    inversion Hhbs as [Hhb | Hsws].
    left; auto.
      left; right; auto.
      right; auto.
      destruct Hsub as [Hrf ?]; inversion Hrf as [Hrfi | Hrfe].
      left; left; right; left; auto.
      left; left; left; auto.
  inversion Hssub as [Hsws | Hsfr].
    destruct Hsws as [? [? Ht]]; destruct Ht; contradiction.
    destruct Hsfr as [? [? Ht]]; destruct Ht; contradiction.

inversion Hxy as [Hu | Hsfr].
    inversion Hu as [Hhb | Hsws].
      inversion Hhb as [Hrfe | Hr].
        left; left; left; left; left; auto.
        inversion Hr as [Hrfi | Hwsfr].
        left; right; split.
          left; auto.
          intro Hor; inversion Hor as [| Hrfe]; auto.
          destruct Hrfi; destruct Hrfe; contradiction.
        left; left; left; left; right; auto.

      destruct Hsws as [z [Hz Hurf]].
      inversion Hurf as [Hrfi | Hrfe].
      right; left.
      exists z; split; auto.
          split. left; auto.
          intro Hor; inversion Hor as [| Hrfe]; auto.
          destruct Hrfi; destruct Hrfe; contradiction.

      left; left; left; right.
      exists z; split; auto.
          right; auto.

      destruct Hsfr as [z [Hz Hurf]].
      inversion Hurf as [Hrfi | Hrfe].
      right; right.
      exists z; split; auto.
          split. left; auto.
          intro Hor; inversion Hor as [| Hrfe]; auto.
          destruct Hrfi; destruct Hrfe; contradiction.

      left; left; right.
      exists z; split; auto.
          right; auto.

inversion Hxy as [Hu | Hssub].
  inversion Hu as [Hr | Hsub].
    inversion Hr as [Hhbs | Hsfr].
    inversion Hhbs as [Hhb | Hsws].
      inversion Hhb as [Hrfe | Hwsfr].
        left; left; left; auto.
        left; left; right; right; auto.

      left; right; destruct Hsws as [z [Hxz Hzy]]; exists z; split; auto.
        inversion Hzy as [Ht | Hrfe].
          inversion Ht. right; auto.
     right; destruct Hsfr as [z [Hxz Hzy]]; exists z; split; auto.
        inversion Hzy as [Ht | Hrfe].
          inversion Ht. right; auto.

      destruct Hsub as [Hrf ?]; inversion Hrf as [Hrfi | Hrfe].
      left; left; right; left; auto.
      left; left; left; auto.
  inversion Hssub as [Hsws | Hsfr].
    destruct Hsws as [z [Hws [Hrf ?]]].
    left; right; exists z; split; auto.
    destruct Hsfr as [z [Hws [Hrf ?]]].
    right; exists z; split; auto.

inversion Hxy as [Hu | Hsfr].
    inversion Hu as [Hhb | Hsws].
      inversion Hhb as [Hrfe | Hr].
        left; right; split.
          right; auto.
          intro Hor; inversion Hor as [Hrfi | Ht].
            destruct Hrfi; destruct Hrfe; contradiction.
             inversion Ht.
        inversion Hr as [Hrfi | Hwsfr].
        left; left; left; left.
          left; auto.
        left; left; left; left; right; auto.

      destruct Hsws as [z [Hz Hurf]].
      inversion Hurf as [Hrfi | Hrfe].
      left; left; left; right.
      exists z; split; auto.
      left; auto.

      right; left; exists z; split; auto.
      split. right; auto.
      intro Hor; inversion Hor as [Hrfi | Ht].
        destruct Hrfe; destruct Hrfi; contradiction.
        inversion Ht; auto.

      destruct Hsfr as [z [Hz Hurf]].
      inversion Hurf as [Hrfi | Hrfe].
      left; left; right.
      exists z; split; auto.
          left; auto.

      right; right.
      exists z; split; auto.
          split. right; auto.
          intro Hor; inversion Hor as [Hrfi | Ht]; auto.
          destruct Hrfi; destruct Hrfe; contradiction.

inversion Hxy as [Hu | Hssub].
  inversion Hu as [Hr | Hsub].
    inversion Hr as [Hhbs | Hsfr].
    inversion Hhbs as [Hhb | Hsws].
      inversion Hhb as [Hrfe | Hwsfr].
        left; left; right; auto.
        left; left; right; right; auto.

      left; right; destruct Hsws as [z [Hxz Hzy]]; exists z; split; auto.
        inversion Hzy as [Hrfi | Ht].
          left; auto. inversion Ht; auto.
     right; destruct Hsfr as [z [Hxz Hzy]]; exists z; split; auto.
        inversion Hzy as [Hrfi | Ht].
          left; auto. inversion Ht.

      destruct Hsub as [Hrf ?]; inversion Hrf as [Hrfi | Hrfe].
      left; left; right; left; auto.
      left; left; left; auto.
  inversion Hssub as [Hsws | Hsfr].
    destruct Hsws as [z [Hws [Hrf ?]]].
    left; right; exists z; split; auto.
    destruct Hsfr as [z [Hws [Hrf ?]]].
    right; exists z; split; auto.

inversion Hxy as [Hu | Hsfr].
    inversion Hu as [Hhb | Hsws].
      inversion Hhb as [Hrfe | Hr].
        left; right; split.
          right; auto.
          intro Hor; inversion Hor as [Ht | Hrfi].
             inversion Ht.
            destruct Hrfi; destruct Hrfe; contradiction.
        inversion Hr as [Hrfi | Hwsfr].
        left; right.
          split.
          left; auto.
          intro Hor; inversion Hor; auto.
        left; left; left; left; auto.

      destruct Hsws as [z [Hz Hurf]].
        right; left.
      exists z; split; auto.
      split; auto.
      intro Hor; inversion Hor; auto.

      destruct Hsfr as [z [Hz Hurf]].
      right; right.
      exists z; split; auto.
      split; auto.
      intro Hor; inversion Hor; auto.

inversion Hxy as [Hu | Hssub].
  inversion Hu as [Hr | Hsub].
    inversion Hr as [Hhbs | Hsfr].
    inversion Hhbs as [Hwsfr | Hsws].
        left; left; right; right; auto.

      left; right; destruct Hsws as [z [Hxz Hzy]]; exists z; split; auto.
        inversion Hzy as [Ht1 | Ht2].
          inversion Ht1; auto. inversion Ht2; auto.
     right; destruct Hsfr as [z [Hxz Hzy]]; exists z; split; auto.
        inversion Hzy as [Ht1 | Ht2].
          inversion Ht1; auto. inversion Ht2; auto.

      destruct Hsub as [Hrf ?]; inversion Hrf as [Hrfi | Hrfe].
      left; left; right; left; auto.
      left; left; left; auto.
  inversion Hssub as [Hsws | Hsfr].
    destruct Hsws as [z [Hws [Hrf ?]]].
    left; right; exists z; split; auto.
    destruct Hsfr as [z [Hws [Hrf ?]]].
    right; exists z; split; auto.

inversion Hxy as [Hu | Hsfr].
    inversion Hu as [Hhb | Hsws].
      inversion Hhb as [Hrfe | Hr].
        left; left; left; left; left; auto.
        left; left; left; left; right; right; auto.

      destruct Hsws as [z [Hz Hurf]].
        left; left; left; right.
      exists z; split; auto.
      inversion Hurf; auto. inversion H; auto. right; auto.

      destruct Hsfr as [z [Hz Hurf]].
      left; left; right.
      exists z; split; auto.
      inversion Hurf; auto. inversion H; auto. right; auto.

destruct_wk Hwk; rewrite Hinter1 in Hrfii;
  rewrite Hinter2 in Hrfii; inversion Hrfii.
destruct_wk Hwk; rewrite Hinter1 in Hrfii;
  rewrite Hinter2 in Hrfii; inversion Hrfii.

inversion Hxy as [Hu | Hsfr].
  inversion Hu as [Hr | Hsws].
    inversion Hr as [Hrfe | Hwsfr].
        left; left; left; left; left; auto.
        left; left; left; left; right; auto.

      left; left; left; right; auto.
      left; left; right; auto.

inversion Hxy as [Hu | Hssub].
  inversion Hu as [Hr | Hsub].
    inversion Hr as [Hhbs | Hsfr].
    inversion Hhbs as [Huf | Hsws].
      inversion Huf as [Hrfe | Hwsfr].
        left; left; left; auto.
        left; left; right; auto.

      left; right; auto.
      right; auto.

      destruct Hsub as [Hrf ?]; inversion Hrf as [Ht | Hrfe].
      inversion Ht.
      left; left; left; auto.
  inversion Hssub as [Hsws | Hsfr].
    destruct Hsws as [z [Hws [Hrf ?]]].
    left; right; exists z; split; auto.
    destruct Hsfr as [z [Hws [Hrf ?]]].
    right; exists z; split; auto.

destruct_wk Hwk; rewrite Hinter1 in Hrfii;
  rewrite Hinter2 in Hrfii; inversion Hrfii.
destruct_wk Hwk; rewrite Hinter1 in Hrfii;
  rewrite Hinter2 in Hrfii; inversion Hrfii.

inversion Hxy as [Hu | Hsfr].
  inversion Hu as [Hr | Hsws].
    inversion Hr as [Hrfe | Hwsfr].
        left; right; split.
          right; auto.
          intro Hor; inversion Hor; auto.

      left; left; left; left; auto.
       right; left; destruct Hsws as [z [? Hor]]; exists z; split; auto.
         inversion Hor as [Ht | Hrfe].
           inversion Ht.
           split. right; auto.
             intro Hort; inversion Hort as [Ht1 | Ht2]; auto.
       right; right; destruct Hsfr as [z [? Hor]]; exists z; split; auto.
         inversion Hor as [Ht | Hrfe].
           inversion Ht.
           split. right; auto.
             intro Hort; inversion Hort as [Ht1 | Ht2]; auto.

inversion Hxy as [Hu | Hssub].
  inversion Hu as [Hr | Hsub].
    inversion Hr as [Hhbs | Hsfr].
    inversion Hhbs as [Hwsfr | Hsws].
        left; left; right; auto.

      destruct Hsws as [? [? Hor]]; inversion Hor as [t1 | t2].
        inversion t1; auto. inversion t2; auto.
      destruct Hsfr as [? [? Hor]]; inversion Hor as [t1 | t2].
        inversion t1; auto. inversion t2; auto.

      destruct Hsub as [Hrf ?]; inversion Hrf as [Ht | Hrfe].
      inversion Ht.
      left; left; left; auto.
  inversion Hssub as [Hsws | Hsfr].
    destruct Hsws as [z [Hws [Hrf ?]]].
    left; right; exists z; split; auto.
    destruct Hsfr as [z [Hws [Hrf ?]]].
    right; exists z; split; auto.

destruct_wk Hwk; rewrite Hintra1 in Hrfei;
  rewrite Hintra2 in Hrfei; inversion Hrfei.
destruct_wk Hwk; rewrite Hintra1 in Hrfei;
  rewrite Hintra2 in Hrfei; inversion Hrfei.

destruct_wk Hwk; rewrite Hintra1 in Hrfei;
  rewrite Hintra2 in Hrfei; inversion Hrfei.
destruct_wk Hwk; rewrite Hintra1 in Hrfei;
  rewrite Hintra2 in Hrfei; inversion Hrfei.

inversion Hxy as [Hu | Hsfr].
  inversion Hu as [Hr | Hsws].
    inversion Hr as [Hrfi | Hwsfr].
        left; left; left; left; left; auto.
        left; left; left; left; right; auto.

      left; left; left; auto.
      left; left; right; auto.

inversion Hxy as [Hu | Hssub].
  inversion Hu as [Hr | Hsub].
    inversion Hr as [Hhbs | Hsfr].
    inversion Hhbs as [Hwsfr | Hsws].
        left; auto.

      destruct Hsws as [z [? Hor]]; inversion Hor as [Hrfi | t2].
        left; right; exists z; split; auto. inversion t2; auto.
      destruct Hsfr as [z [? Hor]]; inversion Hor as [Hrfi | t2].
        right; exists z; split; auto. inversion t2; auto.

      destruct Hsub as [Hrf ?]; inversion Hrf as [Hrfi | Ht].
      left; left; left; auto.
      inversion Ht.
  inversion Hssub as [Hsws | Hsfr].
    destruct Hsws as [z [Hws [Hor ?]]].
    left; right; exists z; split; auto.
    destruct Hsfr as [z [Hws [Hrf ?]]].
    right; exists z; split; auto.

inversion Hxy as [Hu | Hsfr].
  inversion Hu as [Hr | Hsws].
    inversion Hr as [Hrfi | Hwsfr].
        left; right; split; auto.
          left; auto.
          intro Hor; inversion Hor; auto.

      left; left; left; left; auto.
      right; left; destruct Hsws as [z [? Hor]]; exists z; split; auto.
      split; auto. intro Hort; inversion Hort; auto.
      right; right; destruct Hsfr as [z [? Hor]]; exists z; split; auto.
      split; auto. intro Hort; inversion Hort; auto.

inversion Hxy as [Hu | Hssub].
  inversion Hu as [Hr | Hsub].
    inversion Hr as [Hhbs | Hsfr].
    inversion Hhbs as [Hwsfr | Hsws].
        left; left; right; auto.

      destruct Hsws as [z [? Hor]]; inversion Hor as [t1 | t2].
        inversion t1; auto. inversion t2; auto.
      destruct Hsfr as [z [? Hor]]; inversion Hor as [t1 | t2].
        inversion t1; auto. inversion t2; auto.

      destruct Hsub as [Hrf ?]; inversion Hrf as [Hrfi | Ht].
      left; left; left; auto.
      inversion Ht.
  inversion Hssub as [Hsws | Hsfr].
    destruct Hsws as [z [Hws [Hor ?]]].
    left; right; exists z; split; auto.
    destruct Hsfr as [z [Hws [Hrf ?]]].
    right; exists z; split; auto.

destruct_wk Hwk; rewrite Hintra1 in Hrfei;
  rewrite Hintra2 in Hrfei; inversion Hrfei.
destruct_wk Hwk; rewrite Hintra1 in Hrfei;
  rewrite Hintra2 in Hrfei; inversion Hrfei.

destruct_wk Hwk; rewrite Hintra1 in Hrfei;
  rewrite Hintra2 in Hrfei; inversion Hrfei.
destruct_wk Hwk; rewrite Hintra1 in Hrfei;
  rewrite Hintra2 in Hrfei; inversion Hrfei.

destruct_wk Hwk; rewrite Hinter1 in Hrfii;
  rewrite Hinter2 in Hrfii; inversion Hrfii.
destruct_wk Hwk; rewrite Hinter1 in Hrfii;
  rewrite Hinter2 in Hrfii; inversion Hrfii.

inversion Hxy as [Hu | Hsfr].
  inversion Hu as [Hwsfr | Hsws].
        left; left; left; left; auto.

    destruct Hsws as [? [? Hor]]; inversion Hor as [Ht1 | Ht2].
    inversion Ht1; auto. inversion Ht2; auto.
    destruct Hsfr as [? [? Hor]]; inversion Hor as [Ht1 | Ht2].
    inversion Ht1; auto. inversion Ht2; auto.

inversion Hxy as [Hu | Hssub].
  inversion Hu as [Hr | Hsub].
    inversion Hr as [Hhbs | Hsfr].
    inversion Hhbs as [Hwsfr | Hsws].
        left; left; auto.
        left; right; auto.

      right; auto.

      destruct Hsub as [Hrf ?]; inversion Hrf as [Ht1 | Ht2].
      inversion Ht1.
      inversion Ht2.
  inversion Hssub as [Hsws | Hsfr].
    destruct Hsws as [z [Hws [Ht ?]]].
    inversion Ht as [t1 | t2]. inversion t1; auto. inversion t2; auto.
    destruct Hsfr as [z [Hws [Ht ?]]].
    inversion Ht as [t1 | t2]. inversion t1; auto. inversion t2; auto.
Qed.

(** If A1 is weaker than A2 and in a well-formed event structure, if:

Two events are related by the transitive closure of the sequence of the [mhb']
of A2n and of the transitive closure of the preserved program order of A2n 

Then:

The two events are related by the transitive of the sequence of:

- The union of the [mhb'] of A1b, the read-froms global in A2n and not in A1b,
the sequence of write serialization and the read-froms global in A2n but not in
A1b and the sequence of from-read and the read-froms global in A2n but not in
A1b
- The transitive closure of the preserved program order of A2n
*)

Lemma mhb'_ppo2_is_u_seq_int :
  forall E X x y,
  weaker ->
  well_formed_event_structure E ->
  tc (rel_seq (A2nWmm.mhb' E X) (tc (ppo E))) x y ->
  tc (rel_seq (rel_union (rel_union (A1bWmm.mhb' E X) (rf_sub X))
    (rel_union (rel_seq (ws X) (rf_sub X)) (rel_seq (fr E X) (rf_sub X)))) (tc (ppo E))) x y.
Proof.
intros E X x y Hwk Hwf Hxy.
rewrite (mhb'2_is_mhb'1_u_rf_sub X Hwk Hwf) in Hxy; auto.
Qed.

(** If A1 is weaker than A2 and in a well-formed event structure, if:

Two events are related by the transitive closure of the sequence of the 
reflexive closure of the [mhb'] of A2n and of the transitive closure of the 
preserved program order of A2n 

Then:

The two events are related by the transitive closure of the sequence of:

- The reflexive closure of the union of the [mhb'] of A1b, the read-froms global
in A2n and not in A1b, the sequence of write serialization and the read-froms
global in A2n but not in A1b and the sequence of from-read and the read-froms
global in A2n but not in A1b
- The transitive closure of the preserved program order of A2n
*)

Lemma mhb'_ppo2_is_u_seq :
  forall E X x y,
  weaker ->
  well_formed_event_structure E ->
  tc (rel_seq (maybe (A2nWmm.mhb' E X)) (tc (ppo E))) x y ->
  tc (rel_seq (maybe (rel_union (rel_union (A1bWmm.mhb' E X) (rf_sub X))
    (rel_union (rel_seq (ws X) (rf_sub X)) (rel_seq (fr E X) (rf_sub X))))) (tc (ppo E))) x y.
Proof.
intros E X x y Hwk Hwf Hxy.
rewrite (mhb'2_is_mhb'1_u_rf_sub X Hwk Hwf) in Hxy; auto.
Qed.

(** If two events are related by the [mhb] of A1b, then they are related by
they transitive closure of the union of :

- write serialization
- from-read
- the global read-froms of A1
- the preserved program order of A1
- the barrier relation of A1b *)

Lemma mhb1_eq :
  forall E X x y,
  A1bWmm.mhb E X x y ->
  tc
  (rel_union (rel_union (ws X) (fr E X))
     (rel_union (rel_union (mrf1 X) (A1.ppo E))
     (A1b.abc E X) )) x y.
Proof.
unfold A1bWmm.mhb; case_eq A1.inter; case_eq A1.intra; intros Hintra Hinter;
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

(** If two events are related by the [mhb'] of A1b, then they are related by the
transitive closure of the union of:

- write serialization
- from-read
- the global read-froms of A1
- the preserved program order of A1
- the barrier relation of A1 *)

Lemma mhb'1_eq :
  forall E X x y,
  A1bWmm.mhb' E X x y ->
  tc
  (rel_union (rel_union (ws X) (fr E X))
     (rel_union (rel_union (mrf1 X) (A1.ppo E))
     (A1b.abc E X) )) x y.
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

(** If an execution is [fully_barriered], two events related by the preserved
program order of the strong architecture, are related by the global
happens-before of the weaker architecture *)

Lemma ppo2_in_ghb1 :
  forall E X x y,
  fully_barriered E X ->
  ppo E x y ->
  A1bWmm.ghb E X x y.
Proof.
intros E X x y Hfb Hxy.
  generalize (excluded_middle (A1b.ppo E x y)); intro Hor.
  inversion Hor as [Hppo1 | Hnppo1].
   apply A1bBasic.ppo_in_ghb; auto.
   assert (ppo_sub E x y) as Hppos.
     split; auto.

   apply A1bBasic.ab_in_ghb; apply Hfb;
 left; auto.
Qed.

(** If an execution is [fully_barriered], if we have a first event related to
a second event by a read-from relation in the strong architecture but not in the
weak architecture, and if the second event is related to a third event by the
preserved program order of the strong architecture, then the barrier relation
of the weak architecture orders the first and the third events *)

Lemma rf_sub_seq_ppo2_in_ab1 :
  forall E X x z y,
  fully_barriered E X ->
  rf_sub X x z ->
  ppo E z y ->
  A1b.abc E X x y.
Proof.
intros E X x z y Hfb Hxz Hzy; apply Hfb.
right.
exists z; split; auto.
Qed.

(** If A1 is weaker than A2, in a well-formed event structure with a fully
barriered execution, if two events are related by the transitive closure of the
sequence of:

- The union of the [mhb'] of A1b, the read-froms global in A2n and not in A1b,
the sequence of write serialization and the read-froms global in A2n but not in
A1b and the sequence of from-read and the read-froms global in A2n but not in 
A1b

- The transitive closure of the preserved program order of A2n

Then they are related by the transitive closure of the global happens-before of
A1b.
*)

Lemma seq_implies_ghb1_int :
  forall E X x y,
  weaker ->
  well_formed_event_structure E ->
 fully_barriered E X ->
  tc (rel_seq (rel_union (rel_union (A1bWmm.mhb' E X) (rf_sub X))
   (rel_union (rel_seq (ws X) (rf_sub X)) (rel_seq (fr E X) (rf_sub X)))) (tc (ppo E))) x y ->
  tc (A1bWmm.ghb E X) x y.
Proof.
intros E X x y Hwk Hwf Hfb Hxy.

induction Hxy.
  destruct H as [z [Hxz Hzy]].
    inversion Hxz as [Hu | Hs].
    inversion Hu as [Hmhb'1 | Hrf_sub].
      apply trc_ind with z.
        rewrite (ghb1b_eq E X).
        apply (mhb'1_eq Hmhb'1).
        assert (rel_incl (ppo E) (A1bWmm.ghb E X)) as Hincl.
          intros e1 e2 H12; apply ppo2_in_ghb1; auto.
        apply (tc_incl Hincl Hzy).

        generalize (tc_dec Hzy); intros [z' [Hzz' Hor]].
        inversion Hor as [Htc | Heq].
          apply trc_ind with z'.
        rewrite (ghb1b_eq E X).
      apply trc_step; right; right.
       apply (rf_sub_seq_ppo2_in_ab1 Hfb Hrf_sub Hzz').
        assert (rel_incl (ppo E) (A1bWmm.ghb E X)) as Hincl.
          intros e1 e2 H12; apply ppo2_in_ghb1; auto.
        apply (tc_incl Hincl Htc).
         subst;        rewrite (ghb1b_eq E X).
      apply trc_step; right; right.
       apply (rf_sub_seq_ppo2_in_ab1 Hfb Hrf_sub Hzz').

  inversion Hs as [Hsws | Hsfr].
    destruct Hsws as [e [Hxe Hez]].
        generalize (tc_dec Hzy); intros [z' [Hzz' Hor]].
        inversion Hor as [Htc | Heq].
          apply trc_ind with z'.
    apply trc_ind with e; apply trc_step.
        rewrite (ghb1b_eq E X).
      left; left; auto.
        rewrite (ghb1b_eq E X).
      right; right. apply rf_sub_seq_ppo2_in_ab1 with z; auto.
        assert (rel_incl (ppo E) (A1bWmm.ghb E X)) as Hincl.
          intros e1 e2 H12; apply ppo2_in_ghb1; auto.
        apply (tc_incl Hincl Htc).

  subst;     apply trc_ind with e; apply trc_step.
        rewrite (ghb1b_eq E X).
      left; left; auto.
        rewrite (ghb1b_eq E X).
      right; right. apply rf_sub_seq_ppo2_in_ab1 with z; auto.

    destruct Hsfr as [e [Hxe Hez]].

        generalize (tc_dec Hzy); intros [z' [Hzz' Hor]].
        inversion Hor as [Htc | Heq].
          apply trc_ind with z'.
    apply trc_ind with e; apply trc_step.
        rewrite (ghb1b_eq E X).
      left; right; auto.
        rewrite (ghb1b_eq E X).
      right; right;  apply rf_sub_seq_ppo2_in_ab1 with z; auto.
        assert (rel_incl (ppo E) (A1bWmm.ghb E X)) as Hincl.
          intros e1 e2 H12; apply ppo2_in_ghb1; auto.
        apply (tc_incl Hincl Htc).

  subst;     apply trc_ind with e; apply trc_step.
        rewrite (ghb1b_eq E X).
      left; right; auto.
        rewrite (ghb1b_eq E X).
      right; right;  apply rf_sub_seq_ppo2_in_ab1 with z; auto.

apply trc_ind with z; auto.
Qed.

(** If A1 is weaker than A2, in a well-formed event structure with a fully
barriered execution, if two events are related by the transitive closure of the
sequence of:

- The reflexive closure of the union of the [mhb'] of A1b, the read-froms global 
in A2n and not in A1b, the sequence of write serialization and the read-froms 
global in A2n but not in A1b and the sequence of from-read and the read-froms 
global in A2n but not in A1b

- The transitive closure of the preserved program order of A2n

Then they are related by the transitive closure of the global happens-before of
A1b.
*)

Lemma seq_implies_ghb1 :
  forall E X x y,
  weaker ->
  well_formed_event_structure E ->
 fully_barriered E X ->
  tc (rel_seq (maybe (rel_union (rel_union (A1bWmm.mhb' E X) (rf_sub X))
   (rel_union (rel_seq (ws X) (rf_sub X)) (rel_seq (fr E X) (rf_sub X))))) (tc (ppo E))) x y ->
  tc (A1bWmm.ghb E X) x y.
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

(** The preserved program order of A2n is irreflexive *)

Lemma ppo_ac :
  forall E,
  well_formed_event_structure E ->
  ~(exists x, (ppo E) x x).
Proof.
unfold not;
intros E Hwf [x Hppo].
unfold well_formed_event_structure in Hwf.
generalize (ppo_valid Hppo); intro Hpo_iico.
apply (po_ac Hwf Hpo_iico).
Qed.

(** With a well-formed execution witness, the [mhb] (happens-before with only 
global read-froms) of A2n is irreflexive *)

Lemma mhb_ac :
  forall E X,
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  ~(exists x, mhb E X x x).
Proof.
unfold not;
intros E X Hs [x Hx].
generalize (mhb_in_hb E X x x Hx); intro Hhb.
apply (hb_ac Hs Hhb).
Qed.

(** If A1 is weaker than A2, in a well-formed event structure with a well-formed
executtion witness, and a fully-barriered execution, the existence of a cycle in
the global happens-before of A2n implies the existence of a cycle in the global
happens-before of A1b. *)

Lemma ghb2_cycle_implies_ghb1_cycle :
  forall E X x,
  weaker ->
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  fully_barriered E X ->
  tc (A2nWmm.ghb E X) x x ->
  exists y, tc (A1bWmm.ghb E X) y y.
Proof.
intros E X x Hwk Hwf Hs Hfb Hx.
rewrite (ghb2_is_mhb_ppo2 E X) in Hx.
assert (exists y, tc (rel_seq (maybe (mhb' E X)) (tc (A2.ppo E))) y y) as Hc.
eapply (mhb_union_ppo_cycle_implies_mhb'_seq_ppo_cycle2 X Hwf Hs Hx); auto; apply Hx.
destruct Hc as [y Hc].
generalize (mhb'_ppo2_is_u_seq Hwk Hwf Hc); intro Hcy.
exists y; apply (seq_implies_ghb1 Hwk Hwf Hfb Hcy).
Qed.

(** If A1 is weaker than A2, in a well-formed event structure, a fully barriered
execution valid on A1b is valid on A2b *)

Lemma fb_implies_valid :
  forall E X,
  weaker ->
  well_formed_event_structure E ->
  fully_barriered E X ->
  A1bWmm.valid_execution E X ->
  A2nWmm.valid_execution E X.
Proof.
intros E X Hincl Hwf Hfb Hva1.
  destruct_valid Hva1; split; auto; split; auto.
   split; auto; split; auto.
   split; auto.
   split.
    auto.
  unfold acyclic; unfold not; intros x Hx.
  assert (exists x, tc (ghb E X) x x) as Hc.
    exists x; auto.
  assert (write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X)) as Hs.
    split; auto; split; auto.
  generalize (ghb2_cycle_implies_ghb1_cycle Hincl Hwf Hs Hfb Hx); intros [y Hcy].
  apply (Hvalid y Hcy).
Qed.

(** AB constructs a barrier relation from two relations [fenb] and [fenc].

Two events are related by [AB fenb fenc] if:

- [fenb] relates the two events
- There exists a third event such that the first and third events are related
by a read-from global in the strong architecture but non-global in the weak
architecture, and if the third and second events are related by [fenc].

The point of this function is to build a barrier relation from the description
of the pairs of events that need to be ordered in the weaker architecture 
(encoded as [fenb] and [fenc])
*)

Inductive AB (E:Event_struct) (X:Execution_witness) 
             (fenb fenc:Rln Event) : Event -> Event -> Prop :=
  | Base : forall e1 e2,
      fenb e1 e2 -> AB E X fenb fenc e1 e2
  | Acumul : forall w1 r1 e2,
      (rf_sub X) w1 r1 /\ fenc r1 e2 -> AB E X fenb fenc w1 e2.

(** If A1 is weaker than A2, in a well-formed event structure, if the barrier
relation of A1 is [AB] called with parameters :

- [fenb] : relation ordering events not ordered by the preserved program order
of A1 according to the preserved program order of A2
- [fenc] : preserved program order of A2 

Then, an execution valid on A1b is also valid on A2n.

NOTE: calling [AB] with these particular parameters is equivalent to making the
barrier relation respect the [fully_barriered] condition.
*)

Lemma barriers_placement :
  forall E X,
  weaker ->
  well_formed_event_structure E ->
  A1b.abc E X = AB E X (ppo_sub E) (A2n.ppo E) ->
  A1bWmm.valid_execution E X ->
  A2nWmm.valid_execution E X.
Proof.
intros E X Hwk Hwf Hab; apply fb_implies_valid; auto;
unfold fully_barriered; rewrite Hab.
intros x y Hxy; inversion Hxy as [Hb | Hc].
  apply Base; auto.
  destruct Hc as [z [Hrf Hppo]]; apply Acumul with z; auto.
Qed.

(** If A1 is weaker than A2, the event structure is well-formed and the barrier 
relation of A1b is AB called with the same arguments as above (lemma 
[barriers_placement]), which is equivalent to say the the execution is fully 
barriered, then, if two events are related by the transitive closure of the
union of:

- write serialization
- from-read
- read-froms global in A1b
- preserved program order of A1
- barrier relation of A1b

Then these two events are related by the global happens-before of A2n
*)

Lemma ghb1b_incl_ghb2 :
  forall E X x y,
  weaker ->
  A1b.abc E X = AB E X (ppo_sub E) (A2n.ppo E) ->
  tc (rel_union (rel_union (ws X) (fr E X))
     (rel_union (rel_union (mrf1 X) (A1.ppo E)) (A1b.abc E X))) x y ->
  tc (ghb E X) x y.
Proof.
intros E X x y Hwk Hfb Hxy.
induction Hxy as [x y Hs |].
  inversion Hs as [Hwsfr | Hu].
    inversion Hwsfr as [Hws | Hfr]; apply trc_step.
      apply ws_in_ghb; auto. apply fr_in_ghb; auto.
    inversion Hu as [Hrfppo1 | Hab].
      inversion Hrfppo1 as [Hrf1 | Hppo1]; apply trc_step;
        apply ghb_incl; auto.
        apply A1nBasic.mrf_in_ghb; auto.
        apply A1nBasic.ppo_in_ghb; auto.
      rewrite Hfb in Hab; induction Hab as [x y Hppo | x y z Hrfs].
        apply trc_step; destruct Hppo; apply ppo_in_ghb; auto.
        destruct Hrfs as [[Hrf ?] Hppo]; apply trc_ind with y; apply trc_step.
        apply mrf_in_ghb; auto. apply ppo_in_ghb; auto.
  apply trc_ind with z; auto.
Qed.

(** If A1 is weaker than [A2], the event structure is well-formed and the barrier 
relation of [A1b] is [AB] called with the same arguments as above (lemma 
[barriers_placement]), which is equivalent to say the the execution is fully 
barriered, then an execution is valid on [A1b] _if and only if_ it is valid on 
[A2n] *)

Lemma exact_barriers_placement :
  forall E X,
  weaker ->
  well_formed_event_structure E ->
  A1b.abc E X = AB E X (ppo_sub E) (A2n.ppo E) ->
  (A2nWmm.valid_execution E X <-> A1bWmm.valid_execution E X).
Proof.
intros E X Hwk Hwf Hfb; split; [intro Hva2 | intro Hv1].
generalize Hva2; intro Hv2; destruct_valid Hv2;
split; [|split; [|split; [|split]]]; auto.
split; auto. split; auto.
rewrite ghb1b_eq; unfold acyclic in Hvalid; intros x Hx;
  apply (Hvalid x).
apply ghb1b_incl_ghb2; auto.
apply barriers_placement; auto.
Qed.

(** ** Weak-formed barrier

We define a notion of weak-formedness for barrier relations, and we show some
of their properties *)

(** A barrier relation is well-formed for a given execution if all the elements
ordered by the preserved program order of the strong architecture, but not by
the preserved program order of the weaker architecture are ordered by the
barrier relation *)

Definition wfb E X := rel_incl (ppo_sub E) (A1b.abc E X).

(** If two events are related by the global read-from relation of [A2n], then
they are either related by an intra-thread read-from, if intra-thread read-froms
are considered global, or by an inter-thread read-from, if inter-thread 
read-froms are considered global *)

Lemma mrf_or :
  forall X x y,
  mrf2 X x y -> mrfe2 X x y \/ mrfi2 X x y.
Proof.
intros X x y Hxy.
inversion Hxy; [right; auto | left; auto].
Qed.

(** If two events are related by the intra-thread read-from of [A2n], then they
must be executed on the same thread *)

Lemma mrfi2_implies_same_proc :
  forall X x y, mrfi2 X x y -> proc_of x = proc_of y.
Proof.
intros X x y Hxy; unfold mrfi2 in Hxy;
case_eq A2.intra; intro Hi; rewrite Hi in Hxy; simpl in Hxy.
destruct Hxy; auto.
inversion Hxy.
Qed.

(** If two events are related by the inter-thread read-from of [A2n], then they
must be executed on different threads *)

Lemma mrfe1_implies_diff_proc :
  forall X x y, mrfe1 X x y -> proc_of x <> proc_of y.
Proof.
intros X x y Hxy; unfold mrfe1 in Hxy;
case_eq A1.inter; intro Hi; rewrite Hi in Hxy; simpl in Hxy.
destruct Hxy; auto.
inversion Hxy.
Qed.

(** If A1 is weaker than A2, the event structure is well-formed, and the inter
threads read-from relation is the same on [A1] and [A2], then the part of the
read-from relation of A2 that is not in the read-from relation of A1 is the
difference between the intra-threads read-from of [A1], and the intra-threads
read-froms of A2 *)

Lemma same_rfe_implies_rf_sub_is_rfi_sub :
  forall E X,
  weaker ->
  well_formed_event_structure E ->
  mrfe1 = mrfe2 ->
  rf_sub X = rel_sub (mrfi1 X) (mrfi2 X).
Proof.
intros E X Hwk Hwf Hmrf; apply (ext_rel (rf_sub X) (rel_sub (mrfi1 X) (mrfi2 X))); split; intro Hxy.
  destruct Hxy as [H2 H1].
  generalize (mrf_or H2); intro Hor.
  inversion Hor as [He | Hi].
    rewrite <- Hmrf in He.
    assert (mrf1 X x y) as Hc.
      right; auto.
    contradiction.
    split; auto.
      intro Hc; apply H1; left; auto.
  destruct Hxy as [H2 H1]; split.
    left; auto.
    intro Hc; apply H1.
    inversion Hc as [Hi | He]; auto.
    generalize (mrfi2_implies_same_proc X x y H2); intro Heq.
    generalize (mrfe1_implies_diff_proc X x y He); intro Hdiff.
  contradiction.
Qed.

(** If a barrier is weak-formed, any two events ordered by the preserved program
order of [A1], but not by the preserved program order of [A1], are ordered by 
the barrier relation *)

Lemma wfb_ppo_sub_in_ab1 :
  forall E X x y,
  wfb E X ->
  ppo_sub E x y ->
  A1b.abc E X x y.
Proof.
intros E X x y Hfb Hxy; apply Hfb.
auto.
Qed.

(** If:

- [A1] is weaker than [A2]
- The barrier relation is weak-formed
- the inter-threads read-froms of [A1] and [A2] are equal
- the intra-threads read-froms of [A1] and [A2] are equal, OR, the intra-threads
read-from of [A2n] is included in the preserved program order of [A2n]

Then, if two events are related by the [mhb] of [A2n], then they are also
related by the transitive closure of the union of write serialization, from-read
global read-from of [A1], preserved program order of [A1] and barrier relation.
*)

Lemma mhb_incl :
  forall E X x y,
  weaker ->
  wfb E X -> mrfe1 = mrfe2 ->
  (mrfi1 = mrfi2 \/ rel_incl (mrfi X) (ppo E)) ->
  mhb E X x y ->
  tc
    (rel_union (rel_union (ws X) (fr E X))
       (rel_union (rel_union (mrf1 X) (A1.ppo E))
          (A1b.abc E X) )) x y.
Proof.
case_eq A2.inter; case_eq A2.intra; intros Hintra2 Hinter2;
case_eq A1.inter; case_eq A1.intra; intros Hintra1 Hinter1;
unfold mhb; unfold mrf1; unfold mrfi1; unfold mrfe1;
unfold inter; unfold intra;
rewrite Hintra2; rewrite Hinter2; rewrite Hintra1; rewrite Hinter1; simpl;
intros E X x y Hwk Hwfb HmrfX Hrfi_or Hxy.

  apply trc_step; inversion Hxy as [Hrfe | Hr].
    right; left; left; right; auto.
    inversion Hr as [Hrfi | Hre].
      right; left; left; left; auto.
      left; auto.

  apply trc_step; inversion Hxy as [Hrfe | Hr].
    right; left; left; right; auto.
    inversion Hr as [Hrfi | Hre].
      assert (mrfi2 X x y) as Hmrfi.
        unfold mrfi2; unfold intra; rewrite Hintra2; simpl; auto.
      inversion Hrfi_or as [mrfi_eq | mrfi_in_ppo].
        rewrite <- mrfi_eq in Hmrfi; inversion Hmrfi.

      generalize (mrfi_in_ppo x y Hmrfi); intro Hppo.
      generalize (excluded_middle (A1.ppo E x y)); intro Hor.
      inversion Hor as [H1 | Hn1].
        right; left; right; auto.
        right; right; apply Hwfb; split; auto.
      left; auto.

  assert ( (fun  (_ _ : Event) => False) = mrfe2 X) as Hmrf.
    rewrite <- HmrfX; trivial.
  unfold mrfe2 in Hmrf; rewrite Hinter2 in Hmrf; simpl in Hmrf.
  apply trc_step; inversion Hxy as [Hrfe | Hr].
    rewrite <- Hmrf in Hrfe; inversion Hrfe.
    inversion Hr as [Hrfi | Hre].
      right; left; left; left; auto.
      left; auto.

  assert ( (fun  (_ _ : Event) => False) = mrfe2 X) as Hmrf.
    rewrite <- HmrfX; trivial.
  unfold mrfe2 in Hmrf; rewrite Hinter2 in Hmrf; simpl in Hmrf.
  apply trc_step; inversion Hxy as [Hrfe | Hr].
    rewrite <- Hmrf in Hrfe; inversion Hrfe.
    inversion Hr as [Hrfi | Hre].
      assert (mrfi2 X x y) as Hmrfi.
        unfold mrfi2; unfold intra; rewrite Hintra2; simpl; auto.
     inversion Hrfi_or as [mrfi_eq | mrfi_in_ppo].
        rewrite <- mrfi_eq in Hmrfi; inversion Hmrfi.

      generalize (mrfi_in_ppo x y Hmrfi); intro Hppo.
      generalize (excluded_middle (A1.ppo E x y)); intro Hor.
      inversion Hor as [H1 | Hn1].
        right; left; right; auto.
        right; right; apply Hwfb; split; auto.
      left; auto.

 destruct_wk Hwk;
 rewrite Hintra1 in Hrfii;
  rewrite Hintra2 in Hrfii; inversion Hrfii.

  apply trc_step; inversion Hxy as [Hrfe | Hr].
    right; left; left; right; auto.
      left; auto.

 destruct_wk Hwk;
 rewrite Hintra1 in Hrfii;
  rewrite Hintra2 in Hrfii; inversion Hrfii.

  assert ( (fun  (_ _ : Event) => False) = mrfe2 X) as Hmrf.
    rewrite <- HmrfX; trivial.
  unfold mrfe2 in Hmrf; rewrite Hinter2 in Hmrf; simpl in Hmrf.
  apply trc_step; inversion Hxy as [Hrfe | Hr].
    rewrite <- Hmrf in Hrfe; inversion Hrfe.
      left; auto.

 destruct_wk Hwk;
 rewrite Hinter1 in Hrfei;
  rewrite Hinter2 in Hrfei; inversion Hrfei.

 destruct_wk Hwk;
 rewrite Hinter1 in Hrfei;
  rewrite Hinter2 in Hrfei; inversion Hrfei.

    apply trc_step; inversion Hxy as [Hrfi | Hre].
      right; left; left; left; auto.
      left; auto.

    apply trc_step; inversion Hxy as [Hrfi | Hre].
      assert (mrfi2 X x y) as Hmrfi.
        unfold mrfi2; unfold intra; rewrite Hintra2; simpl; auto.
     inversion Hrfi_or as [mrfi_eq | mrfi_in_ppo].
        rewrite <- mrfi_eq in Hmrfi; inversion Hmrfi.
      generalize (mrfi_in_ppo x y Hmrfi); intro Hppo.
      generalize (excluded_middle (A1.ppo E x y)); intro Hor.
      inversion Hor as [H1 | Hn1].
        right; left; right; auto.
        right; right; apply Hwfb; split; auto.
      left; auto.

 destruct_wk Hwk;
 rewrite Hinter1 in Hrfei;
  rewrite Hinter2 in Hrfei; inversion Hrfei.

 destruct_wk Hwk;
 rewrite Hinter1 in Hrfei;
  rewrite Hinter2 in Hrfei; inversion Hrfei.

 destruct_wk Hwk;
 rewrite Hintra1 in Hrfii;
  rewrite Hintra2 in Hrfii; inversion Hrfii.

  apply trc_step; left; auto.
Qed.

(** If the barrier relation is weak-formed, two events related by the preserved
program order of [A2n] are also related by the global-happens-before of [A1b] *)

Lemma ppo2_in_ghb1' :
  forall E X x y,
  wfb E X ->
  ppo E x y ->
  A1bWmm.ghb E X x y.
Proof.
intros E X x y Hfb Hxy.
  generalize (excluded_middle (A1b.ppo E x y)); intro Hor.
  inversion Hor as [Hppo1 | Hnppo1].
   apply A1bBasic.ppo_in_ghb; auto.
   assert (ppo_sub E x y) as Hppos.
     split; auto.

   apply A1bBasic.ab_in_ghb; apply Hfb; auto.
Qed.

(** If:

- [A1] is weaker than [A2]
- The barrier relation is weak-formed
- the inter-threads read-froms of [A1] and [A2] are equal
- the intra-threads read-froms of [A1] and [A2] are equal, OR, the intra-threads
read-from of [A2n] is included in the preserved program order of [A2n]

Then, if two events are related by the transitive closure of the sequence of the
[mhb'] of [A2n] and of the transitive closure of the preserved program order of
[A2n], then they are also related by the transitive closure of the  global 
happens-before of [A1b]
*)

Lemma wfb_seq_implies_ghb1' :
  forall E X x y,
  weaker ->
  well_formed_event_structure E ->
  wfb E X -> mrfe1 = mrfe2 ->
  (mrfi1 = mrfi2 \/ rel_incl (mrfi X) (ppo E)) ->
  tc (rel_seq (A2nWmm.mhb' E X) (tc (A2n.ppo E))) x y ->
  tc (A1bWmm.ghb E X) x y.
Proof.
intros E X x y Hwk Hwf Hfb Hmrf Hrfi_or Hxy.
rewrite (ghb1b_eq E X).
induction Hxy.
  destruct H as [z [Hxz Hzy]].
    inversion Hxz as [Hu | Hs].
    inversion Hu as [Hmhb | Hrf_sub].

     generalize (tc_dec Hzy); intros [z' [Hzz' Horz'y]].
     inversion Horz'y as [Hz'y | Heq].
      apply trc_ind with z'.

      apply trc_ind with z.
      apply (mhb_incl x z Hwk Hfb Hmrf Hrfi_or Hmhb).
        apply trc_step; right.
        generalize (excluded_middle (A1b.ppo E z z')); intro Hor.
        inversion Hor as [H1 | Hn1].
          left; right; auto.
          right; apply wfb_ppo_sub_in_ab1; unfold ppo_sub; unfold rel_sub; auto.

        rewrite <- (ghb1b_eq E X).
        assert (rel_incl (ppo E) (A1bWmm.ghb E X)) as Hincl.
          intros e1 e2 H12; apply ppo2_in_ghb1'; auto.
        apply (tc_incl Hincl Hz'y).

   subst; apply trc_ind with z.
      apply (mhb_incl x z Hwk Hfb Hmrf Hrfi_or Hmhb).

        rewrite <- (ghb1b_eq E X).
        assert (rel_incl (ppo E) (A1bWmm.ghb E X)) as Hincl.
          intros e1 e2 H12; apply ppo2_in_ghb1'; auto.
        apply (tc_incl Hincl Hzy).

     generalize (tc_dec Hzy); intros [z' [Hzz' Horz'y]].
     inversion Horz'y as [Hz'y | Heq].
      apply trc_ind with z'.

      destruct Hrf_sub as [e [Hws Hrf]].
      apply trc_ind with e.
      apply trc_step; left; left; auto.
        generalize (excluded_middle (mrf1 X e z)); intro Hor.
        inversion Hor as [H1 | Hn1].
          apply trc_ind with z.
          apply trc_step; right; left; left; auto.
        generalize (excluded_middle (A1b.ppo E z z')); intro Horp.
        inversion Horp as [H1p | Hn1p].
          apply trc_step; right; left; right; auto.
          apply trc_step; right; right; apply Hfb; unfold ppo_sub; unfold rel_sub; auto.
        assert (rf_sub X e z) as Hrf_sub.
          unfold rf_sub; unfold rel_sub; split; auto.
          apply trc_ind with z; apply trc_step.
        assert (mrfi2 X e z) as Hmrfi.
          rewrite (same_rfe_implies_rf_sub_is_rfi_sub X Hwk Hwf) in Hrf_sub.
          destruct Hrf_sub; auto. apply Hmrf.

          inversion Hrfi_or as [mrfi_eq | mrfi_in_ppo].

          rewrite <- mrfi_eq in Hmrfi; assert False as Ht.
            apply Hn1; left; auto. inversion Ht.

        generalize (mrfi_in_ppo e z Hmrfi); intro Hppo2.
        generalize (excluded_middle (A1b.ppo E e z)); intro Horp.
        inversion Horp as [H1p | Hn1p].
           right; left; right; auto.
            right; right; apply Hfb; split; auto.

        generalize (excluded_middle (A1b.ppo E z z')); intro Horp.
        inversion Horp as [H1p | Hn1p].
            right; left; right; auto.
            right; right; apply Hfb; unfold ppo_sub; unfold rel_sub; auto.

        rewrite <- (ghb1b_eq E X).
        assert (rel_incl (ppo E) (A1bWmm.ghb E X)) as Hincl.
          intros e1 e2 H12; apply ppo2_in_ghb1'; auto.
        apply (tc_incl Hincl Hz'y).

  subst;
      destruct Hrf_sub as [e [Hws Hrf]].
      apply trc_ind with e.
      apply trc_step; left; left; auto.
        generalize (excluded_middle (mrf1 X e z)); intro Hor.
        inversion Hor as [H1 | Hn1].
          apply trc_ind with z.
          apply trc_step; right; left; left; auto.
        generalize (excluded_middle (A1b.ppo E z y)); intro Horp.
        inversion Horp as [H1p | Hn1p].
          apply trc_step; right; left; right; auto.
          apply trc_step; right; right; apply Hfb; unfold ppo_sub; unfold rel_sub; auto.
        assert (rf_sub X e z) as Hrf_sub.
          unfold rf_sub; unfold rel_sub; split; auto.
          apply trc_ind with z; apply trc_step.
        assert (mrfi2 X e z) as Hmrfi.
          rewrite (same_rfe_implies_rf_sub_is_rfi_sub X Hwk Hwf) in Hrf_sub.
          destruct Hrf_sub; auto. apply Hmrf.

          inversion Hrfi_or as [mrfi_eq | mrfi_in_ppo].

          rewrite <- mrfi_eq in Hmrfi; assert False as Ht.
            apply Hn1; left; auto. inversion Ht.

        generalize (mrfi_in_ppo e z Hmrfi); intro Hppo2.
        generalize (excluded_middle (A1b.ppo E e z)); intro Horp.
        inversion Horp as [H1p | Hn1p].
           right; left; right; auto.
            right; right; apply Hfb; split; auto.

        generalize (excluded_middle (A1b.ppo E z y)); intro Horp.
        inversion Horp as [H1p | Hn1p].
            right; left; right; auto.
            right; right; apply Hfb; unfold ppo_sub; unfold rel_sub; auto.

     generalize (tc_dec Hzy); intros [z' [Hzz' Horz'y]].
     inversion Horz'y as [Hz'y | Heq].
      apply trc_ind with z'.

    destruct Hs as [e [Hxe Hez]].
    apply trc_ind with e.
      apply trc_step; left; right; auto.
        generalize (excluded_middle (mrf1 X e z)); intro Hor.
        inversion Hor as [H1 | Hn1].
          apply trc_ind with z.
            apply trc_step; right; left; left; auto.
        generalize (excluded_middle (A1b.ppo E z z')); intro Horp.
        inversion Horp as [H1p | Hn1p].
          apply trc_step; right; left; right; auto.
          apply trc_step; right; right; apply Hfb; unfold ppo_sub; unfold rel_sub; auto.
        assert (rf_sub X e z) as Hrf_sub.
          unfold rf_sub; unfold rel_sub; split; auto.
            rewrite (same_rfe_implies_rf_sub_is_rfi_sub X Hwk Hwf) in Hrf_sub.
          apply trc_ind with z.
          destruct Hrf_sub as [H2 ?].
        generalize (excluded_middle (A1b.ppo E e z)); intro Horp.
        inversion Horp as [H1p | Hn1p].
          apply trc_step; right; left; right; auto.
          apply trc_step; right; right; apply Hfb.
            split; auto.

          inversion Hrfi_or as [mrfi_eq | mrfi_in_ppo].

          rewrite <- mrfi_eq in H2; assert False as Ht.
            apply H; auto. inversion Ht.

        apply (mrfi_in_ppo e z); auto.
        generalize (excluded_middle (A1b.ppo E z z')); intro Horp.
        inversion Horp as [H1p | Hn1p].
          apply trc_step; right; left; right; auto.
          apply trc_step; right; right; apply Hfb; unfold ppo_sub; unfold rel_sub; auto.
      apply Hmrf.

        rewrite <- (ghb1b_eq E X).
        assert (rel_incl (ppo E) (A1bWmm.ghb E X)) as Hincl.
          intros e1 e2 H12; apply ppo2_in_ghb1'; auto.
        apply (tc_incl Hincl Hz'y).

 subst;    destruct Hs as [e [Hxe Hez]].
    apply trc_ind with e.
      apply trc_step; left; right; auto.
        generalize (excluded_middle (mrf1 X e z)); intro Hor.
        inversion Hor as [H1 | Hn1].
          apply trc_ind with z.
            apply trc_step; right; left; left; auto.
        generalize (excluded_middle (A1b.ppo E z y)); intro Horp.
        inversion Horp as [H1p | Hn1p].
          apply trc_step; right; left; right; auto.
          apply trc_step; right; right; apply Hfb; unfold ppo_sub; unfold rel_sub; auto.
        assert (rf_sub X e z) as Hrf_sub.
          unfold rf_sub; unfold rel_sub; split; auto.
            rewrite (same_rfe_implies_rf_sub_is_rfi_sub X Hwk Hwf) in Hrf_sub.
          apply trc_ind with z.
          destruct Hrf_sub as [H2 ?].
        generalize (excluded_middle (A1b.ppo E e z)); intro Horp.
        inversion Horp as [H1p | Hn1p].
          apply trc_step; right; left; right; auto.
          apply trc_step; right; right; apply Hfb.
            split; auto.

          inversion Hrfi_or as [mrfi_eq | mrfi_in_ppo].

          rewrite <- mrfi_eq in H2; assert False as Ht.
            apply H; auto. inversion Ht.

        apply (mrfi_in_ppo e z); auto.
        generalize (excluded_middle (A1b.ppo E z y)); intro Horp.
        inversion Horp as [H1p | Hn1p].
          apply trc_step; right; left; right; auto.
          apply trc_step; right; right; apply Hfb; unfold ppo_sub; unfold rel_sub; auto.
      apply Hmrf.

apply trc_ind with z; auto.
Qed.

(** If:

- [A1] is weaker than [A2]
- The barrier relation is weak-formed
- the inter-threads read-froms of [A1] and [A2] are equal
- the intra-threads read-froms of [A1] and [A2] are equal, OR, the intra-threads
read-from of [A2n] is included in the preserved program order of [A2n]

Then, if two events are related by the transitive closure of the sequence of
the reflexive closure of the [mhb'] of [A2n] and of the transitive closure of
the preserved program order of [A2n], then they are also related by the 
transitive closure of the global happens-before of [A1b].
*)

Lemma wfb_seq_implies_ghb1 :
  forall E X x y,
  weaker ->
  well_formed_event_structure E ->
  wfb E X -> mrfe1 = mrfe2 ->
  (mrfi1 = mrfi2 \/ rel_incl (mrfi X) (ppo E)) ->
  tc (rel_seq (maybe (A2nWmm.mhb' E X)) (tc (A2n.ppo E))) x y ->
  tc (A1bWmm.ghb E X) x y.
Proof.
intros E X x y Hwk Hwf Hfb Hmrf Hrfi_or Hxy.
induction Hxy.
  destruct H as [e [Hor Hey]].
  inversion Hor.
    apply wfb_seq_implies_ghb1'; auto.
      apply trc_step; exists e; auto.
  subst;
        assert (rel_incl (ppo E) (A1bWmm.ghb E X)) as Hincl.
          intros e1 e2 H12; apply ppo2_in_ghb1'; auto.
        apply (tc_incl Hincl Hey).
apply trc_ind with z; auto.
Qed.

(** If:

- [A1] is weaker than [A2]
- The barrier relation is weak-formed
- the inter-threads read-froms of [A1] and [A2] are equal
- the intra-threads read-froms of [A1] and [A2] are equal, OR, the intra-threads
read-from of [A2n] is included in the preserved program order of [A2n]

Then, if there is a cycle in the global happens-before of [A2n], there is a 
cycle in the global happens-before of [A1b].
*)

Lemma wfb_ghb2_cycle_implies_ghb1_cycle :
  forall E X x,
  weaker ->
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  wfb E X -> mrfe1 = mrfe2 ->
  (mrfi1 = mrfi2 \/ rel_incl (mrfi X) (ppo E)) ->
  tc (A2nWmm.ghb E X) x x ->
  exists y, tc (A1bWmm.ghb E X) y y.
Proof.
intros E X x Hwk Hwf Hs Hfb Hmrf Hrfi_or Hx.
rewrite (ghb2_is_mhb_ppo2 E X) in Hx.
assert (exists y, tc (rel_seq (maybe (mhb' E X)) (tc (ppo E))) y y) as Hc.
eapply (mhb_union_ppo_cycle_implies_mhb'_seq_ppo_cycle2 X Hwf Hs Hx); auto; apply Hx.
destruct Hc as [y Hc].
exists y; eapply (wfb_seq_implies_ghb1 Hwk Hwf Hfb Hmrf Hrfi_or Hc).
Qed.

(** If:

- [A1] is weaker than [A2]
- The barrier relation is weak-formed
- the inter-threads read-froms of [A1] and [A2] are equal
- the intra-threads read-froms of [A1] and [A2] are equal, OR, the intra-threads
read-from of [A2n] is included in the preserved program order of [A2n]

Then, if an execution is valid on [A1b], it also valid on [A2n].

*)

Lemma wfb_and_same_rfe_implies_valid :
  forall E X,
  weaker ->
  well_formed_event_structure E ->
  wfb E X -> mrfe1 = mrfe2 ->
  (mrfi1 = mrfi2 \/ rel_incl (mrfi X) (ppo E)) ->
  A1bWmm.valid_execution E X ->
  A2nWmm.valid_execution E X.
Proof.
intros E X Hwk Hwf Hwfb Hmrf Hrfi_or Hv1.
  destruct_valid Hv1; split; auto; split; auto; split; auto.
  split.
    auto.
 unfold acyclic; unfold not; intros x Hx.
  assert (exists x, tc (ghb E X) x x) as Hc.
    exists x; auto.
  assert (write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X)) as Hs.
    split; auto; split; auto.
  generalize (wfb_ghb2_cycle_implies_ghb1_cycle Hwk Hwf Hs Hwfb Hmrf Hrfi_or Hx); intros [y Hcy].
  apply (Hvalid y Hcy).
Qed.

(** [wAB] builds a barrier relation from a relation [fenced] on events.

Two events are ordered by the barrier obtained from [wAB fenced] if the two
events are related by [fenced]
*)

Inductive wAB (E:Event_struct) (X:Execution_witness) (fenced:Rln Event) : Event -> Event -> Prop :=
  | wBase : forall e1 e2,
      fenced e1 e2 -> wAB E X fenced e1 e2.

(** If:

- [A1] is weaker than [A2]
- the inter-threads read-froms of [A1] and [A2] are equal
- the intra-threads read-froms of [A1] and [A2] are equal, OR, the intra-threads
read-from of [A2n] is included in the preserved program order of [A2n]
- the event structure is well-formed
- the barrier relation of [A1b] is the result of calling [wAB] with the part of
the program order preserved by [A2] but not by [A1].

Then, if an execution is valid on [A1b], it is valid on [A2n].

NOTE: calling [wAB] with this specific argument is equivalent to saying that
the barrier relation of [A1b] is weak-formed. Hence, we can use the lemmas we
developed just above, in particular [wfb_and_same_rfe_implies_valid] to prove
this lemma.

*)

Lemma wbarriers_placement : (* weaker barriers guarantee *)
  forall E X,
  weaker -> mrfe1 = mrfe2 ->
  (mrfi1 = mrfi2 \/ rel_incl (mrfi X) (ppo E)) ->
  well_formed_event_structure E ->
  A1b.abc E X = wAB E X (ppo_sub E) ->
  A1bWmm.valid_execution E X ->
  A2nWmm.valid_execution E X.
Proof.
intros E X Hwk Hmrf Hrfi_or Hwf Hab; apply wfb_and_same_rfe_implies_valid; auto;
unfold wfb; rewrite Hab.
intros x y Hxy.
  apply wBase; auto.
Qed.

End Barriers.

End Weaker.

(* End Hierarchy. *)
