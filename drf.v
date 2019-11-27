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

Module DataRaceFree (A1 A2: Archi) (dp:Dp).
Module Wk := (* Hierarchy.*)Weaker A1 A2 dp.
Import Wk.
Module VA2 := Valid A2 dp.
Import VA2.
Import VA2.ScAx.
Module Covering := Covering A1 A2 dp.
Import Covering.
Module A2Basic := Basic A2 dp.

About Valid.

(* Suppositions dans cette théorie

- On a deux architectures A1 et A2
- A1 ≤ A2
*)
Module Type HappensBefore.

Parameter sync : Event_struct -> Execution_witness -> Rln Event.

About po_iico.

Definition happens_before E X :=
  tc (rel_union (po_iico E) (sync E X)).

(* hb is the name of com *)
Hypothesis happens_before_compat_com :
  forall E X x y, hb E X x y -> ~(happens_before E X y x).

Hypothesis happens_before_irr :
  forall E X x,
  well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  ~(happens_before E X x x).

Definition competing E (X:Execution_witness) :=
  fun e1 => fun e2 => events E e1 /\ events E e2 /\
    loc e1 = loc e2 /\ proc_of e1 <> proc_of e2 /\
    (writes E e1 \/ writes E e2).

Definition cns E X :=
  fun e1 => fun e2 => competing E X e1 e2 /\
  ~ (happens_before E X e1 e2 \/ happens_before E X e2 e1).

Hypothesis hb_stable :
  forall E X x y,
  well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  competing E X x y ->
  ~ (happens_before E X x y \/ happens_before E X y x) ->
  (exists Y, A2nWmm.valid_execution E Y /\
  competing E Y x y /\ ~ (happens_before E Y x y \/ happens_before E Y y x)).

Definition covered E X r :=
  forall e1 e2, (competing E X e1 e2) -> (r E X e1 e2 \/ r E X e2 e1).

(* covering : (Event_struct -> Execution_witness -> Event -> Event -> Prop) -> Prop *)
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

Module Drf0 (HB:HappensBefore) <: Compete.

Definition competing E (X:Execution_witness) :=
  fun e1 => fun e2 => events E e1 /\ events E e2 /\
    loc e1 = loc e2 /\ proc_of e1 <> proc_of e2 /\
    (writes E e1 \/ writes E e2).

(* Two competing accesses are events *)
Lemma compete_in_events :
  forall E X x y,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  competing E X x y ->
  events E x /\ events E y.
Proof.
intros E X x y Hwf Hrfwf [Hex [Hey ?]]; split; auto.
Qed.

Definition hbd E X :=
  fun e1 => fun e2 => hb E X e1 e2 /\ proc_of e1 <> proc_of e2.

Definition cns E X :=
  fun e1 => fun e2 => competing E X e1 e2 /\
    ~ (HB.happens_before E X e1 e2 \/ HB.happens_before E X e2 e1).

Ltac destruct_valid H :=
  destruct H as [[Hws_tot Hws_cands] [[Hrf_init [Hrf_cands Hrf_uni]] [Hsp [Hth Hvalid]]]];
  unfold write_serialization_well_formed in Hws_tot(*; unfold uniproc in Hsp*).

Definition s E := HB.happens_before E.

Definition covered E X r :=
  forall e1 e2, (competing E X e1 e2) -> (r E X e1 e2 \/ r E X e2 e1).

Lemma hb_implies_write :
  forall E X x y,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  hb E X x y ->
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

Lemma hb_in_hbd_u_po :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  acyclic (rel_union (hb E X) (pio_llh E)) ->
  rel_incl (hb E X) (rel_union (hbd E X) (po_iico E)).
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
        assert (tc (rel_union (hb E X) (pio_llh E)) x x) as Hcy.
          apply trc_ind with y; apply trc_step.
            left; auto. right; split; auto.
            apply sym_eq; apply A2Basic.hb_implies_same_loc with E X; auto.
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
        assert (tc (rel_union (hb E X) (pio_llh E)) x x) as Hcy.
          apply trc_ind with y; apply trc_step.
            left; auto. right; split; auto.
            apply sym_eq; apply A2Basic.hb_implies_same_loc with E X; auto.
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
        assert (tc (rel_union (hb E X) (pio_llh E)) x x) as Hcy.
          apply trc_ind with y; apply trc_step.
            left; auto. right; split; auto.
            apply sym_eq; apply A2Basic.hb_implies_same_loc with E X; auto.
            split; auto.
            generalize Hs; intros [Hwswf Hrfwf].
            generalize (A2Basic.ran_ws_is_write E X x y Hwswf Hws);
            intros [v [l Hwy]] [[? [? [? Hry]]]?].
            rewrite Hwy in Hry; inversion Hry.
        assert False as Ht.
          unfold acyclic in Huni; apply (Huni x Hcy).
        inversion Ht.
Qed.

Lemma mhb2_in_hbd_po :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  acyclic (rel_union (hb E X) (pio_llh E)) ->
  rel_incl (A2nWmm.mhb E X) (rel_union (hbd E X) (po_iico E)).
Proof.
intros E X Hwf Hs Hv x y Hmhb.
generalize (A2Basic.mhb_in_hb E X x y Hmhb); intro Hhb.
apply hb_in_hbd_u_po; auto.
Qed.

Lemma ghb2_in_hbd_po :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  acyclic (rel_union (hb E X) (pio_llh E)) ->
  rel_incl (A2nWmm.ghb E X) (rel_union (hbd E X) (po_iico E)).
Proof.
intros E X Hwf Hs Hv.
rewrite ghb2_is_mhb_ppo2.
intros x y Hxy; inversion Hxy as [Hmhb | Hppo].
apply mhb2_in_hbd_po; auto.
right; apply A2.ppo_valid; auto.
Qed.

Lemma tc_ghb2_in_tc_hbd_po :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  acyclic (rel_union (hb E X) (pio_llh E)) ->
  rel_incl (tc (A2nWmm.ghb E X)) (tc (rel_union (hbd E X) (po_iico E))).
Proof.
intros E X Hwf Hs Hv; apply tc_incl; apply ghb2_in_hbd_po; auto.
Qed.

Lemma hbd_in_compete :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  rel_incl (hbd E X) (competing E X).
Proof.
intros E X Hwf Hs x y [Hhb Hdp]; split; [|split; [|split; [|split]]]; auto.
  change (events E x) with (In _ (events E) x);
    apply A2Basic.hb_dom_in_evts with X y; auto.
  change (events E y) with (In _ (events E) y);
    apply A2Basic.hb_ran_in_evts with X x; auto.
  apply A2Basic.hb_implies_same_loc with E X; auto.
  apply hb_implies_write with X; auto.
Qed.

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

Lemma sync_thm :
  forall E X,
  well_formed_event_structure E ->
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) ->
  acyclic (rel_union (hb E X) (pio_llh E)) ->
    (covered E X s -> (exists x, tc (A2nWmm.ghb E X) x x) ->
      exists y, tc (rel_union (HB.happens_before E X) (po_iico E)) y y).
Proof.
intros E X Hwf Hs Huni Hp [x Hx].
generalize (tc_ghb2_in_tc_hbd_po Hwf Hs Huni); intro Hincl.
generalize (Hincl x x Hx); intro Hu.
generalize (tc_drf_hbd_u_po_in_tc_sync_u_po Hwf Hs Hp Hu); intro Hhb.
exists x; apply trc_step; left; unfold s; auto.
Qed.

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

Lemma convoluted_covering_holds :
  forall E X, well_formed_event_structure E ->
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

Definition covering s :=
  forall E X, well_formed_event_structure E ->
    A1Wmm.valid_execution E X ->
    covered E X s -> acyclic (A2nWmm.ghb E X).

Lemma covering_s :
  forall E X, well_formed_event_structure E ->
    A1Wmm.valid_execution E X ->
    covered E X s -> acyclic (A2nWmm.ghb E X).
Proof.
apply covering_implied_by_convoluted_covering.
unfold convoluted_covering; apply convoluted_covering_holds.
Qed.

(* This was commented, but turns out to work *)
(* s is the s_drf from the article *)
Lemma wf:
forall E X x y,
  well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  competing E X x y ->
  ~ (s E X x y \/ s E X y x) ->
  (exists Y, A2nWmm.valid_execution E Y /\
  competing E Y x y /\ ~ (s E Y x y \/ s E Y y x)).
Proof.
intros E X x y Hwf Hv1 Hcxy Hnsxy.
apply HB.hb_stable with X; auto.
Qed.

About HB.hb_stable.

(* A memory event cannot be competing with itself *)
Lemma competing_irr : forall E X,
  well_formed_event_structure E ->
  A1Wmm.valid_execution E X ->
  ~ (exists z, competing E X z z).
Proof.
intros E X Hwf Hv [z [? [? [? [Hdp ?]]]]].
apply Hdp; trivial.
Qed.


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

(*
Module DrfGuarantee (HB:HappensBefore).
Module Drf := Drf0 HB.
Module Pres := Preservation Drf.
Import Pres.

Lemma drf_guarantee :
  (forall E X, A2nWmm.valid_execution E X -> Drf.covered E X Drf.s) ->
  (forall E X, well_formed_event_structure E ->
   (A1Wmm.valid_execution E X <-> A2nWmm.valid_execution E X)).
Proof.
apply stab_dir.
Qed.
End DrfGuarantee.*)

End DataRaceFree.
