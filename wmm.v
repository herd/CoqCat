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

Require Import ZArith.
Require Import Ensembles.
From CoqCat Require Import util.

Set Implicit Arguments.

Ltac decide_equality := decide equality; auto with equality arith.

(** * Basic types *)

(** ** Words

We abstract from word-size and alignment issues for now,
modelling both memory addresses and the values that may be
stored in them by natural numbers. *)

Definition Word := nat.

(** *** Addresses *)

Definition Address := Word.

(** *** Values *)

Definition Value := Word.

(** ** Processors

Processors are indexed by natural numbers. *)

Definition Proc := nat.

Parameter eqProc_dec : forall (x y: Proc), {x=y} + {x <> y}.
Hint Resolve eqProc_dec : equality.

(** The model is expressed in terms of allowable orderings on events: individual
    reads and writes to memory.  Each instance of an instruction in a program
    execution may give rise to multiple events, as described by the instruction
    semantics.  We abstract from the details of instructions, but we record in
    each event the instruction instance id (an iiid) that gave rise to it, so
    that we can refer to the program order over the instruction instances. *)

(** ** Index in program order *)

Definition program_order_index := nat.
Lemma eqPoi_dec : forall (x y: program_order_index), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Hint Resolve eqPoi_dec : equality.

(** ** Iiid: instruction identifier

An instruction instance id specifies the processor
on which the instruction was executed together with the index of
the program-order point at which it was executed (represented by
a natural number). *)

Record Iiid  : Set := mkiiid {
  proc : Proc;
  poi: program_order_index }.
Lemma eqIiid_dec : forall (x y: Iiid), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Hint Resolve eqIiid_dec : equality.

(** ** Eiid: a unique identifier associated to each event *)

Definition Eiid := nat.
Lemma eqEiid_dec : forall (x y: Eiid), {x=y} + {x<>y}.
Proof.
decide_equality.
Defined.
Hint Resolve eqEiid_dec : equality.

(** ** Directions: an memory event is either a read or a write *)

Inductive Dirn : Set :=
  | R : Dirn
  | W : Dirn.
Lemma eqDirn_dec : forall (x y: Dirn), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Hint Resolve eqDirn_dec.

(** ** Location:

A memory location is specified by an address *)

Definition Location := Address.

Lemma eqLoc_dec : forall (x y: Location), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Hint Resolve eqLoc_dec : equality.

(** ** Action:

An access specified by a direction, a location and a value *)

Inductive Action : Set :=
  | Access : Dirn -> Location -> Value -> Action.
Lemma eqAction_dec : forall (x y: Action), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Hint Resolve eqAction_dec : equality.

(** ** Event:

- an unique identifier;
- the associated index in program order and the proc;
- the associated action *)

Record Event : Set := mkev {
  eiid : Eiid;
  iiid : Iiid;
  action : Action}.

Lemma eqEv_dec : forall (x y: Event), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Hint Resolve eqEv_dec : equality.

Lemma eqEvc_dec : forall (x y: Event*Event), {x=y} + {x <> y}.
Proof.
decide_equality.
Defined.
Hint Resolve eqEvc_dec : equality.

(** ** Order Extension of events relation

We admit that we can extend any partial order on events to a total order.
This extension is called a linear extension. The module [OEEvt] specifies
the properties of linear extension of events, and satisfies the general
module type [OrdExt].
*)

Module OEEvt <: OrdExt.

Definition Elt := Event.

(** This extension is called a linear extension (LE) *)

Parameter LE : Rln Event -> Rln Event.

(** A relation is included in its linear extension and this extension is
a strict linear order (i.e. it is total) *)

Parameter OE : forall (s S:set Event) (r:Rln Event),
  Included _ s S ->
  partial_order r s ->
  rel_incl r (LE r) /\
  linear_strict_order (LE r) S.

(** The linear extension of a strict linear order on events is itself *)

Parameter le_lso : forall (s:set Event) (r:Rln Event),
  linear_strict_order r s -> LE r = r.
End OEEvt.

Import OEEvt.

(** ** Synchronization

We have a type for syncronisations.

NOTE: this doesn't seem to be used anywhere, so it might be better to just
remove it.
*)

Parameter Synchronization : Set.
Hypothesis eqSynchronization_dec : forall (x y: Synchronization), {x=y} + {x<>y}.
Hint Resolve eqSynchronization_dec : equality.

(** ** Event structure:

Finally, an event structure collects the events of a candidate execution.

An event structure is composed of:
- a set of events;
- the intra causality relation between events from a same instruction
*)

(* Note that we have to work in Type if we use Ensemble. *)
Record Event_struct : Type := mkes {
  events : set Event;
  iico : Rln Event}.

(** * Program order

We define program order as a relation over two events e1 and e2,
w.r.t. to an event structure es; two events are in program order if:

- both e1 and e2 are in the events of es;
- both events have same processor;
- the program order index of e1 is less than the program order index of e2.

We define two po relations, one as a set of pairs of events, and one as a
predicate of type [Rln] [Evt]. *)

Definition po (es: Event_struct) : set (Event*Event) :=
  fun c => match c with (e1,e2) =>
   (* both events have same processor *)
  (e1.(iiid).(proc) = e2.(iiid).(proc)) /\
  (* the program order index of e1 is less than the program order index of e2 *)
  (le e1.(iiid).(poi) e2.(iiid).(poi)) /\
  (* both e1 and e2 are in the events of e *)
  (In _ es.(events) e1) /\
  (In _ es.(events) e2)
  end.

Definition po_strict (es: Event_struct) : Rln Event :=
  fun e1 => fun e2 =>
   (* both events have same processor *)
  (e1.(iiid).(proc) = e2.(iiid).(proc)) /\
  (* the program order index of e1 is less than the program order index of e2 *)
  (lt e1.(iiid).(poi) e2.(iiid).(poi)) /\
  (* both e1 and e2 are in the events of e *)
  (In _ es.(events) e1) /\
  (In _ es.(events) e2).

(** Our final notion of program order will be the union of the program order
    relation as defined above, and of the intra-instruction order. Indeed,
    events might share the same iiid if they are the result of the same
    instruction, we need to take iico into account.
*)

Definition po_iico (E:Event_struct) : Rln Event :=
  fun e1 => fun e2 =>
    (po_strict E) e1 e2 \/ (iico E) e1 e2.

(** ** State constraints *)

Definition State_constraint := Location -> Value.

(** * Basic operations on data types *)

(** Extract the location of an event *)

 Definition loc (e:Event) : (*option*) Location :=
  match e.(action) with
  | Access _ l _ => (*Some*) l
  end.

(** Extract the value read or written during an event *)

Definition value_of (e:Event) : option Value :=
  match e.(action) with
  | Access _ _ v => Some v
  end.

(** ** Processors *)

(** *** Extract the processor on which the event is occuring *)

Definition proc_of (e:Event) : Proc := e.(iiid).(proc).

(** *** Extract the set of processors on which the events from an event
structure are occuring *)

Definition procs (es: Event_struct) : set Proc :=
   fun p => exists e,
     In _ es.(events) e /\
     p = proc_of e.

(** ** Particular events of an event structure *)
(* I comment this, because it is used nowhere and this definition really
   disturbes me. [exists l, exists a, l = a] is always true for me. And so is
   [loc e = l] *)

(*
Definition to_shared (s:set Event) : set (Event) :=
  fun e => In _ s e /\ exists l, exists a, l = a /\ loc e = l.
*)

(** *** Reads

Extract the set of read events *)

Definition reads (es:Event_struct) : set Event :=
  fun e => (In _ es.(events) e) /\
           (exists l, exists v, e.(action) = Access R l v).

(** *** Writes

Extract the set of write events *)

Definition writes (es:Event_struct) : set Event :=
  fun e => (In _ es.(events) e) /\
           (exists l, exists v, e.(action) = Access W l v).

(** * Processor issue order *)

(** Restrict the program order to events reading from or writing to a same
    location *)

Definition pio (E:Event_struct) : Rln Event :=
  fun e1 => fun e2 =>
    loc e1 = loc e2 /\ po_iico E e1 e2.

(** Restrict the processor issue order to pairs of events for which at least one
    of the two events is a write *)

Definition pio_llh (E:Event_struct) : Rln Event :=
  fun e1 => fun e2 =>
    loc e1 = loc e2 /\ po_iico E e1 e2 /\
    ~(reads E e1 /\ reads E e2).


(** * Well-formedness of an event structure

An event structure is well-formed if:

- Two events ordered by the program ordered are executed on the same processor;
- If two events of the event structure have the same event id and the same
  instruction id, they are the same event;
- The domain of intra-instruction order is included in the set of events of the
  event structure;
- The range of intra-instruction order is included in the set of events of the
  event structure;
- The intra-instruction order is acyclic;
- If two events of the event structure have the same iiid, they are related by
  the intra-instruction order;
- Conversely, two events ordered by the intra-instruction order must have the
  same iiid;
- The intra-instruction order is a transitive relation
*)

Definition well_formed_event_structure (E:Event_struct) : Prop :=
  (forall x y, po_iico E x y -> proc_of x = proc_of y) /\
  (forall e1 e2, In _ E.(events) e1 -> In _ E.(events) e2 ->
   (e1.(eiid) = e2.(eiid)) /\ (e1.(iiid) = e2.(iiid)) -> (e1 = e2)) /\
   Included _ (dom (iico E)) E.(events) /\
   Included _ (ran (iico E)) E.(events) /\
   acyclic (iico E) /\ (forall x y, events E x /\ events E y /\
   poi (iiid x) = poi (iiid y) -> iico E x y) /\
   (forall e1 e2, (iico E) e1 e2 -> (e1.(iiid) = e2.(iiid))) /\
   trans (iico E).

(** * Write serializations

Write Serialization (also called coherence order (co)) orders all pairs of
writes to a same location *)

Definition Write_serialization := Rln Event.

(** Takes an event and a location as parameters, and is true if
    the event is a write to that location *)

Definition write_to (e:Event) (l:Location) : Prop :=
  exists v, action e = Access W l v.

(** Takes a set of events and a location as parameters, and is true if all the
    events are writes to that location *)
Definition writes_to_same_loc_l (s:set Event) (l:Location) : set Event :=
  fun e => In _ s e /\ write_to e l.

(** Write serialization relation is well formed if:

- For each location, the relation is a total order on the writes to this
  relation;
- The relation relates pairs of writes to a same location *)

Definition write_serialization_well_formed (s:set Event) (ws:Write_serialization) : Prop :=
  (forall l, linear_strict_order
     (rrestrict ws (writes_to_same_loc_l s l))
       (writes_to_same_loc_l s l)) (* Hws_tot *) /\
  (forall x e, ws x e ->
   (exists l : Location,
    In _ (writes_to_same_loc_l s l) x /\
    In _ (writes_to_same_loc_l s l) e)) (* Hws_cands *).

Ltac destruct_ws H :=
  destruct H as [Hws_tot Hws_cands].

(** * Read-from

The read-from (rf) relation orders a write event to the read events that
read the value written by the write event *)

Definition Rfmap := Rln Event.

(** Takes an event and location as parameters, and is true if the event is a read
    event *)

Definition read_from (e:Event) (l:Location) : Prop :=
  exists v, action e = Access R l v.

(** Takes a set of events as a parameter, and returns a relation that relates any
    write to the reads to the same location reading the value written by the
   write event *)

Definition rfmaps (s:set Event) : Rln Event :=
  fun e1 => fun e2 =>
  In _ s e1 /\ In _ s e2 /\
  exists l, write_to e1 l /\ read_from e2 l /\
    value_of e1 = value_of e2.

(* I comment this, because it is used nowhere and this definition disturbes me *)
(*
Definition no_intervening_write (e1 e2:Event) (s:Rln Event): Prop :=
  s e1 e2 /\
  forall l, write_to e1 l ->
    ~(exists e3, write_to e3 l /\ s e1 e3 /\ s e3 e2).
*)

(** Takes an event structure as a parameter and returns a relation that relates
    any read from a given location to the writes following it in program
    order affecting the same location
*)

Definition ls (E:Event_struct) : Rln Event :=
  fun e1 => fun e2 =>
    In _ (reads E) e1 /\ In _ (writes E) e2 /\ (po_iico E) e1 e2.

(** A read-from relation produced by [rfmaps] is well-formed if:

- For any read event, there is a write event such that the write event is
  related to the read event by the read-from relation
- If two write events are related to a same read event, the two writes are the
  the same write event.
*)

Definition rfmaps_well_formed (E:Event_struct) (s:set Event) (rf:Rfmap) : Prop :=
  (forall er, In _ (reads E) er -> exists ew,
     ((In _ s ew) /\ rf ew er)) /\ (*Hrf_init*)
  (forall e1 e2, rf e1 e2 -> (rfmaps s) e1 e2) /\ (*Hrf_cands*)
   (forall x w1 w2, rf w1 x -> rf w2 x ->
    w1 = w2).  (*Hrf_uni*)

Ltac destruct_rf H :=
  destruct H as [Hrf_init [Hrf_cands Hrf_uni]].

(** * From-read

The from-read (fr) relation orders a read event to all the write events that
occur after (w.r.t. the write serialization order) the write that the read-from
relation relates to the read we consider.
*)

Definition Frmap := Rln Event.

(** Takes a set of events, a read-from relation and a write serialization, and
compute the corresponding from-read relation *)

Definition frmaps (s:set Event) (rf:Rfmap) (ws:Write_serialization) : Frmap :=
  fun er => fun ew =>
    In _ s er /\ In _ s ew /\
    exists wr, rf wr er /\ ws wr ew.

(** * AB orderings

AB is a relation on events, that encodes the execution order constraints issued
by barries in our program *)

Definition AB := Rln Event.

(** An order AB is well-formed on a set of events if it relates only events of
this set, and it never imposes an order between two events that are identical *)

Definition ab_well_formed (s:set Event) (abc : AB) :=
  (forall x y, abc x y -> In _ s x /\ In _ s y /\ x<>y).

(** * Execution Witness

An execution witness characterizes an execution and is composed of:

- a write seralization order
- a read-from relation
*)

Record Execution_witness : Type := mkew {
  ws : Write_serialization;
  rf : Rfmap }.

(** Extracts a from-read relation from an event structure and an execution
    witness *)

Definition fr (E:Event_struct) (X:Execution_witness) : Frmap :=
  frmaps (events E) (rf X) (ws X).

(** Extracts the subset of a read-from relation where the write and the read
    are executed on different processors *)

Definition rf_intra (X:Execution_witness) : Rfmap :=
  fun ew => fun er => (rf X) ew er /\ proc_of ew = proc_of er.

(** Extracts the subset of a read-from relation where the write and the read
    are executed on the same processor *)

Definition rf_inter (X:Execution_witness) : Rfmap :=
  fun ew => fun er => (rf X) ew er /\ proc_of ew <> proc_of er.

(*Definition sync_ws X :=
  acyclic (rel_union (sync X) (ws X)).
Definition sync_fr E X :=
  acyclic (rel_union (sync X) (fr E X)).
(*Definition sync_po E X :=
  acyclic (rel_union (po_iico E) (sync X)).
  (*rel_incl (*(A2.ppo E)*) (ppo_sub E) (sync X).*)
Definition sync_rf(*sub*) X :=
  acyclic (rel_union (sync X) (rf(*_sub*) X)).*)
Definition sync_ac X :=
  acyclic (sync X).
Definition sync_trans X :=
  trans (sync X).

Definition wf_sync E X :=
  sync_ws X /\ sync_fr E X /\ (*sync_rf X /\ sync_po E X /\*)
  sync_ac X /\ sync_trans X.*)

(*
Axiom init_rf :
  forall E X s w r,
  init E w -> rf X w r ->
    rf (mkew (rrestrict (ws X) s) (rrestrict (rf X) s)) w r.
Axiom init_ws :
  forall E X s w w',
  init E w -> ws X w w' ->
    ws (mkew (rrestrict (ws X) s) (rrestrict (rf X) s)) w w'.
Axiom init_po :
  forall E i,
  init E i ->
  (forall e, events E e -> proc_of e = proc_of i -> po_iico E i e).
Axiom final_po :
  forall E f,
  final E f ->
  forall e, events E e -> proc_of e = proc_of f -> po_iico E e f.
*)

Ltac destruct_wfs H :=
   destruct H as [Hsws [Hsfr (*[Hsrf [Hspo*) [Hsac Hstrans]]](*]]*).

(* (** ** Initial and final states *) *)

(*Definition init (X:Execution_witness) : set Event :=
  fun x => exists wx, (rf X) wx x /\ ~(exists ew, (ws X) ew wx).

Definition final (X:Execution_witness) : set Event :=
  fun x => ~(exists e, (ws X) x e).*)

(** * Valid execution *)

(** ** Happens Before

The happens-before relation is the union of the read-from, from-read and write
serialization relations. It is called communication relation in (A Shared Memory
Poetics, 2010, Jade Alglave)
 *)

Definition hb (E:Event_struct) (X:Execution_witness) : Rln Event :=
  rel_union (rel_union (rf X) (fr E X)) (ws X).

(** An execution is valid in the sequentially consistent memory model if the
union of its program order and of its happens-before relation is acyclic *)

Definition sc_check (E:Event_struct) (X:Execution_witness) : Prop :=
  acyclic (rel_union (po_iico E) (hb E X)).

(** Two events from an event structure are competing if:

- They are executed on different processors;
- They affect the same location;
- At least one of them is a write event *)

Definition compete E : Rln Event :=
  fun e1 => fun e2 =>
  (events E) e1 /\ (events E) e2 /\
  loc e1 = loc e2 /\ proc_of e1 <> proc_of e2 /\
  (writes E e1 \/ writes E e2).

(** * Dependencies

This type describes the properties that a module describing the dependencies
between the instructions must respect
*)

Module Type Dp.

(** We have a function that takes an event structure as a parameter and returns
a relation that orders events according to the dependencies between them *)

Parameter dp : Event_struct -> Rln Event.

(** A dependency relation is valid only if:

- It is included in the program order
- It is a transitive relation
- It only relates read events to other events *)

Parameter dp_valid : forall (E:Event_struct),
  rel_incl (dp E) (po_iico E) /\ trans (dp E) /\
  forall x y, dp E x y -> reads E x.

(** Given an event structure and a subset of its events, we can restrict the
dependency relation to the elements of this event structure that belong to this
subset *)

Hypothesis dp_fun :
  forall E s x y,
  dp E x y /\ s x /\ s y <->
  dp (mkes (Intersection Event (events E) s) (rrestrict (iico E) s)) x y.
End Dp.

(** * Architecture

An architecture is represented by three things:

- Its preserved program order : the part of the program order that the
architecture guarantees will be respected in the execution
- Its global read-from: depending on the architecture, some writes might no be
directly available to all threads immediatly after they are executed, and thus
some parts of the read-from relation might not be visible globally.
- Its barriers : each architecture has its own barriers, and we must encode how
they affect the execution order of events
*)

Module Type Archi.

(** Associates to an event structure, an order on its events *)

Parameter ppo : Event_struct -> Rln Event.

(** This order is a subset of the program order. Thus, it represents the part of
the program order that the architecture guarantees to respect *)

Hypothesis ppo_valid : forall (E:Event_struct),
  rel_incl (ppo E) (po_iico E).

(** Given an event structure and a subset of its events, we can restrict the
preserved program order to the elements of the event structure that belong to
this subset *)

Hypothesis ppo_fun :
  forall E s x y,
  ppo E x y /\ s x /\ s y <->
  ppo (mkes (Intersection Event (events E) s) (rrestrict (iico E) s)) x y.

(** If [intra] is true, the subset of read-from defined by [rf_intra], i.e. the
subset of read-from where the write and the read are executed on the same
thread, is visible globally *)

Parameter intra : bool.

(** If [inter] is true, the subset of read-from defined by [rf_inter], i.e. the
subset of read-from where the write and the read are executed on different
threads, is visible globally *)

Parameter inter : bool.

(** The barrier relation associates to an event structure and an execution
witness a relation on its events *)

Parameter abc : Event_struct -> Execution_witness -> Rln Event.

(** If the event structure is well-formed and if the read-from relation of the
execution witness is well-formed, then events related by the barrier relation
are events from the event structure *)

Hypothesis ab_evts : forall (E:Event_struct) (X:Execution_witness),
  forall x y, well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  abc E X x y -> In _ (events E) x /\ In _ (events E) y.

(** Our barriers can't contradict the program order (event structure) or the
happens-before relation (execution witness). *)

Hypothesis ab_incl :
  forall E X, rel_incl (abc E X) (tc (rel_union (hb E X) (po_iico E))).

(** It is not exactly clear what this represents, and it seems to be left as
a parameter everywhere. Needs further documentation *)

(* Hypothesis ab_fun :
  forall E X init final s x y,
  well_formed_event_structure E ->
  rfmaps_well_formed E (events E) (rf X) ->
  (abc E X x y /\ s x /\ s y <->
  abc (mkes init (Intersection Event (events E) s) (rrestrict (iico E) s) final)
    (mkew (rrestrict (ws X) s) (rrestrict (rf X) s)) x y). *)

Parameter stars : Event_struct -> set Event.
End Archi.

(** * Memory Model

A memory model defines the notion of validity of an execution, based on an
architecture module and a dependencies module
*)

Module Wmm (A : Archi) (dp : Dp).
Import A.
Import dp.

(** ** Global Happens Before

The global happens-before relation is the union of:

- The subsets of read-from that are global on the architecture
- The barriers relation
- The write serialization relation
- The from-read relation
- The preserved program order *)

Definition ghb (E:Event_struct) (X:Execution_witness) :
  Rln Event :=
  match inter,intra with
  | true,true =>
    rel_union (rf_inter X) (rel_union (rf_intra X) (rel_union (abc E X)
      (rel_union (rel_union (ws X) (fr E X)) (ppo E))))
  | true,false =>
    rel_union (rf_inter X) (rel_union (abc E X) (rel_union (rel_union (ws X) (fr E X))
      (ppo E)))
  | false,true =>
    rel_union (rf_intra X) (rel_union (abc E X) (rel_union (rel_union (ws X) (fr E X))
      (ppo E)))
  | false,false =>
    rel_union (abc E X) (rel_union (rel_union (ws X) (fr E X))
      (ppo E))
  end.

(** ** Uniprocessor

The uniprocessor condition on executions states that the happens-before relation
must be compatible with processor issue order restricted to pairs of event where
at least one of the events is the write.

Concretely, this means that :

- If two writes are ordered by the write serialization order, they must occur
in this order;
- If a read reads the value written by a specific write, the write event must
occur before the read event;
- If a read reads the value written by a first write preceding a second write,
this read event must occur before the second event
 *)

Definition uniproc E X :=
  (*if llh then*) acyclic (rel_union (hb E X) (pio_llh E))
  (*else acyclic (rel_union (hb E X) (pio E))*).

(** ** Out of thin air

The out of thin air condition on executions states that the read-from relation
must be compatible with the dependency relation.

Concretely, this means that a write cannot depend on a read that read its value
from this same write *)

Definition thin E X :=
  acyclic (rel_union (rf X) (dp E)).

(** ** Execution validity

An execution (i.e. an event structure and an execution witness) is valid when:

- The read-from and write serialization relations are well-formed
- The execution respects the uniprocessor condition (see [uniproc])
- The execution respects the out of thin air condition (see [thin])
- The global happens-before relation is acyclic *)

Definition valid_execution (E:Event_struct) (X:Execution_witness) : Prop :=
  write_serialization_well_formed (events E) (ws X) /\
  rfmaps_well_formed E (events E) (rf X) /\
  acyclic (rel_union (hb E X) (pio_llh E)) /\ (* uniproc: per location coherence *)
  acyclic (rel_union (rf X) (dp E)) /\ (* out-of-thin-air condition *)
  acyclic (ghb E X).

(** Corresponds to [rf_intra] when [intra] is true, and to the empty relation
otherwise *)

Definition mrfi X :=
  mrel intra (rf_intra X).

(** Corresponds to [rf_inter] when [inter] is true, and to the empty relation
otherwise *)

Definition mrfe X :=
  mrel inter (rf_inter X).

(** Union of [mrfi] and of [mrfe] *)

Definition mrf X :=
  rel_union (mrfi X) (mrfe X).

(** Happens-before relation where we consider only the global read-from relation

NOTE:
This looks a little bit more complicated than it should ? What is the difference
between [mhb] and [mhb'] ? They both end up containing [ws], [fr] and [grf].

In the end couldn't we just write:

<<
Definition mhb (E:Event_struct) (X:Execution_witness) : Rln_Event :=
  rel_union (mrf X) (rel_union (ws X) (fr E X)).
>>
*)

Definition mhb (E:Event_struct) (X:Execution_witness) :
  Rln Event :=
  match inter,intra with
  | true,true =>
    rel_union (rf_inter X) (rel_union (rf_intra X) (rel_union (ws X) (fr E X)))
  | true,false =>
    rel_union (rf_inter X) (rel_union (ws X) (fr E X))
  | false,true =>
    rel_union (rf_intra X) (rel_union (ws X) (fr E X))
  | false,false =>
    (rel_union (ws X) (fr E X))
  end.

(** [mhb'] is the union of:

- The [mhb] relation
- The sequence of write serialization and global read-from. This relation is, in
some sense, the opposite of from-read. From-read relates reads with the writes
that occured after the write of the value that the read event reads. The
sequence of write serialization and read-from relates a write to a read such
that the write occured _before_ the write of the value that the read reads.
- The sequence of from-read and global read-from. This relation relates to read
events that read from the same location, but values written by two different
read events.

NOTE: This relation corresponds to the [hb'] relation in which we consider only
the global parts of read-from.
*)

Definition mhb' (E:Event_struct) (X:Execution_witness) : Rln Event :=
  fun e1 => fun e2 =>
    (rel_union (rel_union (mhb E X) (rel_seq (ws X) (mrf X))) (rel_seq (fr E X) (mrf X))) e1 e2.

Ltac destruct_valid H :=
  destruct H as [[Hws_tot Hws_cands]
                 [[Hrf_init [Hrf_cands Hrf_uni]] (*[Hwfs*)
                  [Hsp [Hth Hvalid]]]](*]*);
  unfold write_serialization_well_formed in Hws_tot(*; unfold uniproc in Hsp*).

(*
Goal forall E X, valid_execution E X -> True.
intros E X Hvalid.
destruct_valid Hvalid.
*)

End Wmm.
