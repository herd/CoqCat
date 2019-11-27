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
Require List.
Definition set := Ensemble.
Set Implicit Arguments.

(** * Utilities

A bunch of lemmas on sets, relations and logic that are useful in the
rest of this development

We can link some of the lemmas present in this file with lemmas presented
in the chapter 2 of "A Shared Memory Poetics", Jade Alglave, 2010:

- Section 2.2, Axiom 1 and 2 corresponds to the hypothesis [util.OE]
- Section 2.3, Lemma 1 corresponds to [union_cycle_implies_seq_cycle_final]
- Section 2.3.1, Lemma 2 corresponds to [hx_trans]
- Section 2.3.1, Lemma 3 corresponds to [union_implies_hx_path]
- Section 2.3.1, Lemma 4 corresponds to [hexa_r]
*)

(* ** Classical logic *)
Section Class.

Lemma contraposee : forall (A B:Prop),
  (A -> B) -> (~B -> ~A).
Proof.
intros A B Himpl Hnot_b.
unfold not; unfold not in Hnot_b; intro HA; apply Hnot_b.
apply (Himpl HA).
Qed.

End Class.

Hint Resolve contraposee : util.

(** ** Empty set lemmas *)

Section EmptySet.

(** A set is empty if there are no elements contained in it *)

Lemma empty_set_is_empty (A:Set) (s:set A):
  ~(exists e, In _ s e) <-> Same_set _ (Empty_set _) s.
Proof.
split.
(*->*)
- intros Hnon; unfold Same_set.
  unfold not in Hnon; unfold In in Hnon;
  unfold Included.
  split; intros x Hin_empty.
  + elim Hnon; exists x; inversion Hin_empty.
  + destruct Hnon; exists x; apply Hin_empty.
(*<-*)
- intros Hsame; unfold not; unfold In.
  intros Hexists.
  unfold Same_set in Hsame.
  unfold Included in Hsame.
  destruct Hsame as [Hemp_s Hs_emp].
  destruct Hexists as [e Hse].
  assert (In _ (Empty_set _) e).
  + apply (Hs_emp e Hse).
  + inversion H.
Qed.

Lemma same_set_sym (A:Set) (s1 s2: set A):
  Same_set _ s1 s2 <-> Same_set _ s2 s1.
Proof.
  split; intros H;
  unfold Same_set; unfold Same_set in H; split; destruct H; auto.
Qed.

Lemma empty_set_is_empty_dir (A:Set) (s:set A):
  ~(exists e, In _ s e) -> Same_set _ s (Empty_set _).
Proof.
intros Hnot.
apply empty_set_is_empty in Hnot.
apply same_set_sym. auto.
Qed.

Lemma empty_set_is_empty_back (A:Set) (s:set A):
  Same_set _ s (Empty_set _) ->  ~(exists e, In _ s e).
Proof.
intros H. apply same_set_sym in H.
apply empty_set_is_empty in H. auto.
Qed.

(** If there is an element in a set, it can't be empty *)

Lemma non_empty_set_is_non_empty_dir (A:Set) (s:set A):
  (exists e, In _ s e) -> ~(Same_set _ s (Empty_set _)).
Proof.
intros H1 H2.
apply empty_set_is_empty_back in H2. auto.
Qed.

(** Being included in an empty set is equivalent to being an empty set *)

Lemma incl_is_enough_for_empty (A:Set) (s:set A):
  Included _ s (Empty_set _) -> Same_set _ s (Empty_set _).
Proof.
unfold Same_set; unfold Included; unfold In.
intros Hemp.
split; [exact Hemp|].
intros x Habs.
inversion Habs.
Qed.

Lemma incl_is_enough_for_empty_back (A:Set) (s:set A):
  Same_set _ s (Empty_set _) -> Included _ s (Empty_set _).
Proof.
unfold Same_set; unfold Included; unfold In.
intros Hemp.
destruct Hemp as [Hemp].
exact Hemp.
Qed.

End EmptySet.

(** ** Set inclusion lemmas *)

Section Inclusion.

(** If two sets are included in a third set, their union is also included
in this third set *)

Lemma incl_union (A:Set) (s1 s2 s:set A) :
  Included _ s1 s -> Included _ s2 s -> Included _ (Union _ s1 s2) s.
Proof.
unfold Included; intros.
inversion H1.
(*s1 x*)
apply H.
apply H2.
(*s2 x*)
apply H0.
apply H2.
Qed.

Lemma incl_union_in (A:Set) (s1 s2 s:set A) :
  Included _ s1 s -> Included _ s2 s ->
  (forall x, In _ (Union _ s1 s2) x -> In _ s x).
Proof.
apply incl_union.
Qed.

(** An in a set, is also in the union of this set with any other set *)

Lemma incl_union_left_in (A:Set) (s1 s2 : set A) :
  forall x, In _ s1 x -> In _ (Union _ s1 s2) x.
Proof.
unfold In; intros.
apply Union_introl.
exact H.
Qed.

Lemma incl_union_right_in (A:Set) (s1 s2 : set A) :
  forall x, In _ s2 x -> In _ (Union _ s1 s2) x.
Proof.
unfold In; intros.
apply Union_intror.
exact H.
Qed.

(** If the union of two sets is included in a third set, each of these two
    sets is included in the third set *)

Lemma incl_union_back (A:Set) (s1 s2 s: set A) :
  Included _ (Union _ s1 s2) s -> Included _ s1 s /\ Included _ s2 s.
Proof.
unfold Included; intros.
split.
intros.
apply (H x).
apply incl_union_left_in; exact H0.
intros.
apply (H x).
apply incl_union_right_in; exact H0.
Qed.

Lemma incl_union_back_in (A:Set) (s1 s2 s: set A) :
  Included _ (Union _ s1 s2) s ->
  (forall x, In _ (Union _ s1 s2) x -> In _ s x).
Proof.
unfold Included; intros.
apply H.
exact H0.
Qed.

(** Set inclusion is transitive *)

Lemma incl_trans (A:Set) (s1 s2 s3:set A) :
  Included _ s1 s2 -> Included _ s2 s3 -> Included _ s1 s3.
Proof.
unfold Included; unfold In; intros.
apply (H0 x (H x H1)).
Qed.

End Inclusion.

(** ** Set equality lemmas *)

Section SameSet.

(** Set (non-)equality is transitive *)

Lemma same_trans (A:Set) (s1 s2 s3:set A) :
  Same_set _ s1 s2 -> Same_set _ s2 s3 -> Same_set _ s1 s3.
Proof.
unfold Same_set; unfold Included; unfold In.
intros H12 H23.
destruct H12 as [H12 H21];
destruct H23 as [H23 H32].
split; intros x; [intro H1 | intro H3].
apply H23; apply H12; exact H1.
apply H21; apply H32; exact H3.
Qed.

Lemma not_same_trans (A:Set) (s1 s2 s3:set A) :
  Same_set _ s1 s2 -> ~(Same_set _ s1 s3) -> ~(Same_set _ s2 s3).
Proof.
unfold not; intros H12 Hnot13 H23.
assert (Same_set A s1 s3) as H13.
eapply same_trans; [apply H12 | apply H23].
apply (Hnot13 H13).
Qed.

(** Set (non-)equality is reflexive *)

Lemma same_refl (A:Set) (s1 s2:set A) :
  Same_set _ s1 s2 -> Same_set _ s2 s1.
Proof.
unfold Same_set; unfold Included; unfold In.
intros H12.
destruct H12 as [H12 H21].
split; [exact H21 | exact H12].
Qed.

Lemma not_same_refl (A:Set) (s1 s2:set A) :
  ~(Same_set _ s1 s2) -> ~(Same_set _ s2 s1).
Proof.
unfold not; intros H12 H21.
apply H12.
apply same_refl; exact H21.
Qed.

(** A set is included in itself *)

Lemma same_impl_incl (A:Set) (s1 s2:set A) :
  Same_set _ s1 s2 -> Included _ s1 s2.
Proof.
unfold Same_set; unfold Included; unfold In.
intros Hsame.
destruct Hsame as [H12 H21].
exact H12.
Qed.

End SameSet.

(** ** Linear Orders

A relation with domain B and range A is represented as a pair of
pairs (A * B)
*)

Section LinOrder.

(** *** Relations as set of pairs *)

(** Characterisation of domain and range of a relation *)

Definition domain (A B:Set) (e:set (A*B)) : set B :=
  fun y => exists x, In _ e (x,y).

Definition range (A B:Set) (e:set (A*B)) : set A :=
  fun x => exists y, In _ e (x,y).

Lemma range_is_range (A B:Set) (e:set (A*B)) (x:A) :
  (exists y, In _ e (x,y)) -> In _ (range e) x.
Proof.
unfold range; unfold In; trivial.
Qed.

Lemma domain_is_domain (A B:Set) (e:set (A*B)) (y:B) :
  (exists x, In _ e (x,y)) -> In _ (domain e) y.
Proof.
unfold domain; unfold In; trivial.
Qed.

(** A linear order is a transitive, antisymmetric and linear relation
    from a A to A *)

Definition linear_order (A:Set) (r:set (A*A)) (xs:set A) : Prop :=
  Included _ (Union _ (domain r) (range r)) xs /\
  (*transitivity*)
  (forall x1 x2 x3, (In _ r (x1,x2)) /\ (In _ r (x2,x3)) -> (In _ r (x1,x3))) /\
  (*antisymetry*)
  (forall x1 x2, (In _ r (x1,x2)) /\ (In _ r (x2,x1)) -> x1=x2) /\
  (*connex on xs*)
  (forall x1 x2, (In _ xs x1) -> (In _ xs x2) -> ((In _ r (x1,x2)) \/ (In _ r (x2,x1)))).

(** A linear order is a reflexive relation *)

Lemma linear_prop_cart (A:Set) (so:set (A*A)) (s:set A) (x:A) :
  (linear_order so s) -> In _ s x -> In _ so (x,x).
Proof.
unfold linear_order; unfold In; intros.
destruct H as [Hincl H].
destruct H as [Htrans H].
destruct H as [Hrefl Hlin].
assert (so (x,x) \/ so (x,x)).
apply (Hlin x x H0 H0).
inversion H.
exact H1.
exact H1.
Qed.

(** A linear order is transitive *)

Lemma linear_order_trans (A:Set) (so:set (A*A)) (x1 x2 x3:A) :
  (exists s, (linear_order so s)) ->
  In _ so (x1,x2) -> In _ so (x2,x3) -> In _ so (x1,x3).
Proof.
intros Hexists H12 H23.
unfold linear_order in Hexists.
destruct Hexists as [s He].
destruct He as [Hincl He].
destruct He as [Htrans He].
eapply Htrans.
split; [apply H12 | apply H23].
Qed.

(** Elements ordered by a linear order on A are in A *)

Lemma incl_lin_order_range (A:Set) (so: set (A*A)) (s:set A) (x1 x2:A) :
  linear_order so s -> In _ so (x1,x2) -> In _ s x1.
Proof.
unfold linear_order; unfold In; intros.
assert (In _ (range so) x1).
apply range_is_range.
exists x2; apply H0.
assert (In _ (Union A (domain so) (range so)) x1).
apply incl_union_right_in; exact H1.
repeat (destruct H).
unfold Included in H; apply H; exact H2.
Qed.

Lemma incl_lin_order_domain (A:Set) (so: set (A*A)) (s:set A) (x1 x2:A) :
  linear_order so s -> In _ so (x1,x2) -> In _ s x2.
Proof.
unfold linear_order; unfold In; intros.
assert (In _ (domain so) x2).
apply domain_is_domain.
exists x1; apply H0.
assert (In _ (Union A (domain so) (range so)) x2).
apply incl_union_left_in; exact H1.
repeat (destruct H).
unfold Included in H; apply H; exact H2.
Qed.

(** If a relation R is included in a relation R', the union of the domain
    and range of R is included in the union of the domain and range of R'
*)

Lemma incl_dom_ran (A:Set) (so sor:set (A*A)):
  Included (A * A) sor so ->
  Included A (Union A (domain sor) (range sor))
  (Union A (domain so) (range so)).
Proof.
unfold Included;
intros Hincl x Hsor.
inversion Hsor as [y Hdom | y Hran].
(*dom*)
- unfold In in Hdom; unfold domain in Hdom.
  apply incl_union_left_in; unfold In; unfold domain.
  destruct Hdom as [x0 Hin]; exists x0; apply (Hincl (x0,x) Hin).
(*ran*)
- unfold In in Hran; unfold range in Hran.
  apply incl_union_right_in; unfold In; unfold range.
  destruct Hran as [x0 Hin]; exists x0; apply (Hincl (x,x0) Hin).
Qed.

End LinOrder.

(* Section LinStrictOrder. *)

(** *** Relations as predicate *)

(** A relation from A to A is a predicate that takes to values of type A *)

Definition Rln (A:Type) := A -> A -> Prop.

(** Characterisation of domain and range of a relation *)

Definition dom (A:Type) (r:Rln A) : set A :=
  fun x => exists y, r x y.
Definition ran (A:Type) (r:Rln A) : set A :=
  fun y => exists x, r x y.

(** Union of domain and range of a relation *)

Definition udr (A:Type) (so: Rln A) : set A :=
  Union _ (dom so) (ran so).

(** A relation is included in another if all the elements related by the first
    relation are also related by the second one *)

Definition rel_incl (A:Type) (r1 r2 : Rln A) : Prop :=
  forall x y, r1 x y -> r2 x y.

(** A relation is a strict partial order if it is transitive and irreflexive *)

Definition partial_order (A:Type) (r:Rln A) (xs:set A) : Prop :=
  Included _(Union _ (dom r) (ran r)) xs /\
  (*transitivity*)
  (forall x1 x2 x3, (r x1 x2) /\ (r x2 x3) -> (r x1 x3)) /\
  (*irreflexivity*)
  (forall x, ~(r x x)).

(** A relation is a strict total order if it is a linear partial order *)

Definition linear_strict_order (A:Type) (r:Rln A) (xs:set A) : Prop :=
  Included _(Union _ (dom r) (ran r)) xs /\
  (*transitivity*)
  (forall x1 x2 x3, (r x1 x2) /\ (r x2 x3) -> (r x1 x3)) /\
  (*irreflexivity*)
  (forall x, ~(r x x)) /\
  (*linear on xs*)
  (forall x1 x2, (x1 <> x2) -> (In _ xs x1) -> (In _ xs x2) ->
    (r x1 x2) \/ (r x2 x1)).

Ltac destruct_lin H :=
  destruct H as [Hdr [Htrans [Hac Htot]]].

(** A strict linear order is a transitive relation *)

Lemma linear_strict_order_trans (A:Set) (so:Rln A) (x1 x2 x3:A) :
  (exists s, (linear_strict_order so s)) ->
  so x1 x2 -> so x2 x3 -> so x1 x3.
Proof.
unfold linear_strict_order; unfold In; intros.
destruct H as [s [Hdr [Htrans [Hac Htot]]]].
apply (Htrans x1 x2 x3).
split.
exact H0.
exact H1.
Qed.

(** A strict linear order is a linear relation *)

Lemma linear_strict_order_lin (A:Set) (s:set A) (so:Rln A) (x1 x2:A) :
  (linear_strict_order so s) ->
  (x1 <> x2) -> (In _ s x1) -> (In _ s x2) ->
  so x1 x2 \/ so x2 x1.
Proof.
intros Hlin Hdiff H1 H2.
destruct Hlin as [Hdom [Htrans [Hacycl Hlin]]].
apply (Hlin x1 x2 Hdiff H1 H2).
Qed.

(** Two elements related by a strict total order are included in the set
   over which this order is defined *)

Lemma incl_lin_strict_order_dom (A:Set) (so: Rln A) (s:set A) (x1 x2:A) :
  linear_strict_order so s -> so x1 x2 -> In _ s x1.
Proof.
unfold linear_strict_order; unfold In; intros.
assert (In _ (dom so) x1).
exists x2; apply H0.
assert (In _ (Union A (dom so) (ran so)) x1).
apply incl_union_left_in; exact H1.
destruct H as [Hdr [Htrans [Hac Htot]]].
 unfold Included in Hdr; apply Hdr.
exact H2.
Qed.

Lemma incl_lin_strict_order_ran (A:Set) (so: Rln A) (s:set A) (x1 x2:A) :
  linear_strict_order so s -> so x1 x2 -> In _ s x2.
Proof.
unfold linear_strict_order; unfold In; intros.
assert (In _ (ran so) x2).
exists x1; apply H0.
assert (In _ (Union A (dom so) (ran so)) x2).
apply incl_union_right_in; exact H1.
destruct H as [Hdr [Htrans [Hac Htot]]].
unfold Included in Hdr; apply Hdr; exact H2.
Qed.

(*End LinStrictOrder.*)

(** ** Linear Extension of an order *)

Module Type OrdExt.
Parameter Elt : Type.

(** LE (linear extension) extends a partial order to a total order *)

Parameter LE : Rln Elt -> Rln Elt.

(** A relation is included in its own linear extension and a linear extension
    is a strict linear order *)

Hypothesis OE : forall (s S:set Elt) (r:Rln Elt),
  Included _ s S ->
  partial_order r s ->
  rel_incl r (LE r) /\
  linear_strict_order (LE r) S.

(** The extension of a strict linear order is itself *)

Hypothesis le_lso : forall (s:set Elt) (r:Rln Elt),
  linear_strict_order r s -> LE r = r.
End OrdExt.

(** ** Restriction of a relation to a subset of elements *)

Section RRestrict.

(** Restrict a relation to a set, meaning that two elements are
    related in this restricted relation if they are related by the
    unrestricted version and both belong to the set. *)

Definition rrestrict (A:Set) (r:Rln A) (s:set A) : Rln A :=
    fun x => fun y =>
    r x y /\ In _ s x /\ In _ s y.

End RRestrict.

(** ** Transitive closure of a relation *)

Section TransClos.

(** Transitive closure of a relation defined as a set of pairs *)

Inductive transitive_closure (A:Type) (e:set (A*A)) : set (A*A) :=
    | t_step : forall x y, In _ e (x,y) -> In _ (transitive_closure e) (x,y)
    | t_trans : forall x y z, In _ (transitive_closure e) (x,y) ->
                     In _ (transitive_closure e) (y,z) ->
                     In _ (transitive_closure e) (x,z).

(** Transitive closure of a relation defined as a predicate *)

Inductive tc (A : Type) (r : A -> A -> Prop) : A -> A -> Prop :=
   |trc_step : forall x, forall y : A, r x y -> (tc r) x y
   |trc_ind : forall x y z : A,
      (tc r) x z ->
      (tc  r) z y -> (tc r) x y.

(** The domain of the transitive closure of relation is included in the domain
    of the relation *)

Print Included.
Lemma dom_tc_in_dom :
  forall (A:Set) (r: Rln A) (x:A),
  In _ (dom (tc r)) x ->
  In _ (dom r) x.
Proof.
intros A r x Hd.
destruct Hd as [y Hd].
induction Hd as [ x y Hs |x y Hi].
  exists y; apply Hs.
  exact IHHd1.
Qed.

(** The range of the transitive closure of relation is included in the range
    of the relation *)

Lemma ran_tc_in_ran :
  forall (A:Set) (r: Rln A) (x:A),
  In _ (ran (tc r)) x ->
  In _ (ran r) x.
Proof.
intros A r x Hr.
destruct Hr as [y Hr].
induction Hr as [ x y Hs |x y Hi].
  exists x; apply Hs.
  exact IHHr2.
Qed.

(** The union of the domain and range of a relation is the union of the domain
    and range of the transitive closure of this relation *)

Lemma dom_ran_tc :
  forall (A:Set) (r:Rln A),
  Union _ (dom r) (ran r) = Union _ (dom (tc r)) (ran (tc r)).
Proof.
intros A r.
apply (Extensionality_Ensembles _
         (Union _ (dom r) (ran r)) (Union _ (dom (tc r)) (ran (tc r))));
split; unfold Included; intros x Hx.
(*r -> stc r*)
- inversion Hx as [e Hd | e Hr].
  + apply incl_union_left_in; unfold In; unfold domain;
    unfold In in Hd; unfold domain in Hd; destruct Hd as [y Hd].
    exists y; apply trc_step; apply Hd.
  + apply incl_union_right_in; unfold In; unfold range;
    unfold In in Hr; unfold range in Hr; destruct Hr as [y Hr].
    exists y; apply trc_step; apply Hr.
(*stc r -> r*)
- induction Hx as [e Hd | e Hr].
  + apply incl_union_left_in; apply dom_tc_in_dom; apply Hd.
  + apply incl_union_right_in; apply ran_tc_in_ran; apply Hr.
Qed.

(** Transform a relation in its strict equivalent *)

Definition strict (A:Set) (r:Rln A) : Rln A :=
  fun e1 => fun e2 =>
    r e1 e2 /\ e1 <> e2.

(** Strict transitive closure of a relation *)

Definition stc (A:Set) (r: Rln A) : Rln A := strict (tc r).

End TransClos.

(** ** Acyclicity of a relation *)

Section Acyclicity.

(** A relation is acyclic if its transitive closure is irreflexive *)

Definition acyclic (A:Type) (r: Rln A) : Prop :=
  forall x, ~((tc r) x x).

End Acyclicity.

(** ** Basic facts and definitions about sets *)

Section BasicSet.

(** The union of two sets is symmetric *)

Lemma union_sym (A:Set) (r1 r2: set (A*A)) :
  (Union _ r1 r2) = (Union _ r2 r1).
Proof.
apply (Extensionality_Ensembles _ (Union _ r1 r2) (Union _ r2 r1)).
unfold Same_set; unfold Included; split; intros c Hin.
inversion Hin as [c' H1 | c' H2].
  apply incl_union_right_in; exact H1.
  apply incl_union_left_in; exact H2.
inversion Hin as [c' H2 | c' H1].
  apply incl_union_right_in; exact H2.
  apply incl_union_left_in; exact H1.
Qed.

(** Cartesian product of two sets *)

Definition cartesian (A B:Set) (sa:set A) (sb:set B) : set (A*B) :=
  fun c => match c with (a,b) =>
  In _ sa a /\ In _ sb b end.

(** A set is a singleton if it contains exactly one element *)

Definition is_singleton (A:Set) (s:set A) :=
  exists e, In _ s e /\
  ~(exists e', e <> e' /\ In _ s e').

(** A set is empty if it is equal to the empty set *)

Definition is_empty (A:Set) (s:set A) :=
  Same_set _ s (Empty_set _).

End BasicSet.

(** ** Basic facts and definitions about relations *)

Section BasicRel.

(** The empty relation relates no elements *)

Definition emp_rel (A:Set) : Rln A :=
  fun x => fun y => False.

(** Two relations are the same if they are respectively included in each
    other *)

Definition same_rel (A:Set) (r1 r2 : Rln A) : Prop :=
  rel_incl r1 r2 /\ rel_incl r2 r1.

(** Axiom of extensionality for relations define as predicates

If two relations relate the same elements, they are equal *)

Axiom ext_rel : forall (A:Type) (r1 r2 : Rln A),
  (forall x y, r1 x y <-> r2 x y) -> r1 = r2.


(** Mirror

Produce the symmetric of a relation *)

Definition inv (A:Set) (r:set (A*A)) :=
  fun c => match c with (y,x) =>
  In _ r (x,y) end.

Definition inv_strict (A:Type) (r: Rln A) : Rln A :=
  fun x => fun y => r y x.

(** Union of two relations

Two elements are related by the union of two relations if they are related by
one of the two relations *)

Definition rel_union (A:Type) (r1 r2 : Rln A) : Rln A :=
  fun x => fun y => r1 x y \/ r2 x y.

(** Union of relations is symmetric *)

Lemma union_triv : (*util*)
  forall (A:Type) (r1 r2 : Rln A),
  rel_union r1 r2 = rel_union r2 r1.
Proof.
intros A r1 r2.
apply ext_rel;
unfold rel_union; split; intro Hx;
inversion Hx as [H1 | H2].
  right; apply H1.
  left; apply H2.
  right; apply H1.
  left; apply H2.
Qed.

(** The set of maximal elements is the elements in relation only with
    themselves *)

Definition maximal_elements (A:Set) (xs:set A) (r:set (A*A)) : set A :=
  fun x => In _ xs x /\ forall x', In _ xs x'/\ In _ r (x, x') -> (x = x').

(** If an element is in the maximal elements of a set, it is also in the set *)

Lemma maximal_preserves_incl (A:Set) (xs:set A) (r:set (A*A)) (e:A):
  In _ (maximal_elements xs r) e ->
  In _ xs e.
Proof.
unfold maximal_elements; unfold In.
intros Hmax.
destruct Hmax as [Hxs].
exact Hxs.
Qed.

(** If a first relation is included in second relation, every elements related
    by the transitive closure of the first relation are also related by the
    transitive closure of the second relation *)

Lemma incl_path :
  forall (A:Set) (r1 r2 : Rln A) (x y : A),
  rel_incl r1 r2 ->
  tc r1 x y ->
  tc r2 x y.
Proof.
intros A r1 r2 x y H12 H1.
induction H1.
  apply trc_step; apply H12; apply H.
  apply trc_ind with z; auto.
Qed.

(** Every relation included in an acyclic relation, is acyclic *)

Lemma incl_ac :
  forall (A:Set) (r1 r2 : Rln A),
  rel_incl r1 r2 ->
  acyclic r2 ->
  acyclic r1.
Proof.
unfold acyclic; unfold not;
intros A r1 r2 H12 H2 x H1; apply (H2 x).
eapply incl_path; [apply H12 | apply H1].
Qed.

(** The transitive closure of a strict linear order is itself *)

Lemma lso_is_tc :
  forall A (so:Rln A) (s: set A),
  linear_strict_order so s -> tc so = so.
Proof.
intros A so s Hlin.
destruct Hlin as [Hdr [Htrans [Hac Htot]]].
assert (forall x y, (tc so) x y <-> so x y) as Hext.
  intros x y; split; intro Hxy.
    induction Hxy.
      apply H.
      apply (Htrans x z y); split; [apply IHHxy1 | apply IHHxy2].
    apply trc_step; apply Hxy.
apply (ext_rel (tc so) (so) Hext).
Qed.

(** When two elements are related by the transitive closure of a relation,
    either they were directly related in the relation, or they were related
    through a chain of one of more elements *)

Lemma tc_dec : forall (A:Type) (r:Rln A) (x y:A),
  tc r x y ->
  exists z,  (r x z /\ (tc r z y \/ z = y)).
intros.
induction H.
exists y; split;trivial. right; trivial.
destruct IHtc1 as [z1 ?]. destruct H1. destruct H2.
destruct IHtc2 as [z2 ?]. destruct H3. destruct H4.
exists z1; intuition. left.
eapply trc_ind. apply H2. eapply trc_ind. apply trc_step. apply H3.
trivial.
exists z1; intuition. left.
eapply trc_ind. apply H2. apply trc_step.  rewrite <- H4. trivial.
destruct IHtc2 as [z2 ?]. destruct H3. destruct H4.
exists z1; intuition. left.
rewrite H2. eapply trc_ind. apply trc_step. apply H3. trivial.
exists z1; intuition. left.
rewrite H2. rewrite <- H4. constructor; trivial.
Qed.

Lemma tc_dec2 : forall (A:Set) (r:Rln A) (x y:A),
  tc r x y ->
  exists z,  ((tc r x z \/ z = x) /\ r z y).
intros.
induction H.
exists x; split;trivial. right; trivial.
destruct IHtc1 as [z1 ?]. destruct H1.
destruct IHtc2 as [z2 ?]. destruct H3.
exists z2; intuition. left.
eapply trc_ind. apply H5. eapply trc_ind. apply trc_step. apply H2.
trivial.
left. apply trc_ind with z1; auto.
  rewrite H1; apply trc_step; auto.
left; eapply trc_ind. subst; apply trc_step. apply H2. auto.
subst; left. apply trc_step; auto.
Qed.

(** The transitive closure of a partial order is itself *)

Lemma po_is_tc :
  forall A (so:Rln A) (s: set A),
  partial_order so s -> tc so = so.
Proof.
intros A so s Hp.
destruct Hp as [Hdr [Htrans Hac]].
assert (forall x y, (tc so) x y <-> so x y) as Hext.
  intros x y; split; intro Hxy.
    induction Hxy.
      apply H.
      apply (Htrans x z y); split; [apply IHHxy1 | apply IHHxy2].
    apply trc_step; apply Hxy.
apply (ext_rel (tc so) (so) Hext).
Qed.

(** A strict linear order is an acyclic relation *)

Lemma lin_strict_ac :
  forall (A:Set) (s:set A) (r : Rln A),
  linear_strict_order r s ->
  acyclic r.
Proof.
intros A s r Hlin.
generalize (lso_is_tc Hlin); intro Heq.
unfold acyclic; rewrite Heq.
destruct Hlin as [Hdr [Htrans [Hac Htot]]];
  apply Hac.
Qed.

(** If a relation is included in another one, applying transitive closure
    to both relations preserves the relation of inclusion *)

Lemma tc_incl : forall  (E : Type)  (r1 r2 : Rln E),
  rel_incl r1 r2 -> rel_incl (tc r1) (tc r2).
Proof.
unfold rel_incl.
intros E r1 r2 ir12 x y tcr1xy.
induction tcr1xy.
  apply trc_step.
  apply ir12; trivial.
apply trc_ind with z; trivial.
Qed.

(** A relation is included in its transitive closure *)

Lemma tc_incl_itself: forall (E:Type) (r: Rln E),
  rel_incl r (tc r).
Proof.
intros E r.
unfold rel_incl; intros x y H.
apply trc_step in H. auto.
Qed.

(** If a relation is included in an acyclic relation, it is acyclic *)

Lemma ac_incl : forall (E : Set)  (r1 r2 : Rln E),
  acyclic r2 ->  rel_incl r1 r2 -> acyclic r1.
Proof.
intros E r1 r2 Hac Hinc.
apply (incl_ac Hinc Hac).
Qed.

(** If a first relation is included in a second relation, their union is the
    second relation *)

Lemma incl_implies_union_eq :
  forall A (r1 r2: Rln A),
  rel_incl r1 r2 ->
  rel_union r1 r2 = r2.
Proof.
unfold rel_incl;
intros A r1 r2 Hincl.
apply ext_rel; intros x y; split; intro Hxy.
  inversion Hxy as [H1 | H2].
    apply Hincl; apply H1.
    apply H2.
  unfold rel_union; right; apply Hxy.
Qed.

(** If a first relation is included in a second relation, and if the second
    relation is acyclic, their union is acyclic *)

Lemma incl_implies_ac_union :
  forall A (r1 r2: Rln A),
  rel_incl r1 r2 ->
  acyclic r2 ->
  acyclic (rel_union r1 r2).
Proof.
intros A r1 r2 Hincl Hac;
generalize (incl_implies_union_eq Hincl);
intro Heq; rewrite Heq; apply Hac.
Qed.

(** Relation union is symmetric (duplicate of union_triv) *)

Lemma rel_union_refl :
  forall A (r1 r2: Rln A),
  rel_union r1 r2 = rel_union r2 r1.
Proof.
apply union_triv.
Qed.

(** Applying union with a same relation to two relations doesn't change
    the inclusion relation between these two relations *)

Lemma rel_incl_right :
  forall A (r1 r2 r3: Rln A),
  rel_incl r1 r2 ->
  rel_incl (rel_union r1 r3) (rel_union r2 r3).
Proof.
unfold rel_incl;
intros A r1 r2 r3 H12 x y H13.
inversion H13 as [H1 | H3].
  left; apply H12; apply H1.
  right; apply H3.
Qed.

Lemma rel_incl_left :
  forall A (r1 r2 r3: Rln A),
  rel_incl r1 r2 ->
  rel_incl (rel_union r3 r1) (rel_union r3 r2).
Proof.
unfold rel_incl;
intros A r1 r2 r3 H12 x y H31.
inversion H31 as [H3 | H1].
  left; apply H3.
  right; apply H12; apply H1.
Qed.

(** Relation inclusion is transitive *)

Lemma rel_incl_trans (A:Set) (r1 r2 r3 : Rln A) :
  rel_incl r1 r2 -> rel_incl r2 r3 -> rel_incl r1 r3.
Proof.
unfold rel_incl;
intros H12 H23 x y H1.
apply H23; apply H12; apply H1.
Qed.

(** ** Composition of relations

Two elements are related by the sequence of two relations, if exist a third
elements such that, the first relation relates the first and third element, and
the second relation relates the third and second elements

We note the sequencing of two relations r1 and r2 the following way : (r1;r2) *)

Definition rel_seq (A:Type) (r1 r2 : Rln A) : Rln A :=
  fun x => fun y => exists z, r1 x z /\ r2 z y.

(** Reflexive closure of a relation

Two elements are related by the reflexive closure of a relation if they are
related by the relation or if they are equal *)

Definition maybe (A:Type) (r:Rln A) : Rln A :=
  fun e1 => fun e2 => r e1 e2 \/ e1 = e2.

(** The pre-hexa of two relations, is the transitive-reflexive closure of their
    sequence *)

Definition phx (A:Type) (r1 r2 :Rln A) : Rln A :=
  fun e1 => fun e2 => (tc (rel_seq r1 r2)) e1 e2 \/ e1 = e2.

(** The hexa of two relations is the sequence of

- the reflexive closure of the first relation
- the pre-hexa of the two relations
- the reflexive closure of the second relation *)

Definition hx (A:Type) (r1 r2:Rln A) : Rln A :=
  fun e1 => fun e2 =>
    rel_seq (maybe r2) (rel_seq (phx r1 r2) (maybe r1)) e1 e2.

(** These two alternatives versions of pre-hexa and hexa apply transitive
    closure to the second relation before applying regular pre-hexa and hexa

- [phx' r1 r2 = phx r1 (tc r2)
- [hx' r1 r2 = hx r1 (tc r2) *)

Definition phx' (A:Type) (r1 r2 :Rln A) : Rln A :=
  fun e1 => fun e2 => (tc (rel_seq r1 (tc r2))) e1 e2 \/ e1 = e2.

Definition hx' (A:Type) (r1 r2:Rln A) : Rln A :=
  fun e1 => fun e2 =>
    rel_seq (maybe (tc r2)) (rel_seq (phx r1 (tc r2)) (maybe r1)) e1 e2.

(** Definition of the transitivity of a relation *)

Definition trans (A:Type) (r:Rln A) : Prop :=
  forall x y z, r x y -> r y z -> r x z.

(*
Lemma test : forall (A:Set) (r1 r2: Rln A) x y, (phx r1 r2 x y) = (maybe (tc (rel_seq r1 r2)) x y).
intros.
unfold phx, maybe. trivial.
Qed.
*)

(** The transitive closure of a transitive relation is itself *)

Lemma trans_tc :
  forall A (r:Rln A),
  trans r -> tc r = r.
Proof.
intros A r Ht.
generalize (ext_rel (tc r) r); intro Hext.
apply Hext; split; intro Hxy.
induction Hxy; auto.
  apply Ht with z; auto.
apply trc_step; auto.
Qed.

(** The reflexive closure of a transitive relation is transitive *)

Lemma trans_maybe :
  forall A (r: Rln A),
  trans r -> trans (maybe r).
Proof.
intros A r Ht x y z Hxy Hyz.
inversion Hxy; inversion Hyz.
  left; apply Ht with y; auto.
  left; rewrite H0 in H; auto.
  left; rewrite <- H in H0; auto.
  right; subst; auto.
Qed.

(** If:

- r1 is transitive
- x r1 y (r1;r2)+ z

Then x (r1;r2)+ z *)

Lemma glue_front : forall (A:Type) (r1 r2: Rln A) x y z,
   trans r1 -> r1 x y -> tc (rel_seq r1 r2) y z -> tc (rel_seq r1 r2) x z.
intros A r1 r2 x y z Tr1 H H0.
remember (rel_seq r1 r2) as r. induction H0; subst.
(* x r1 x0 r1 z r2 y donc x r1 z r2 y (par trans) donc x r1r2 y
   donc x (r1r2)+ y *)
destruct H0 as [z [? ?]].
apply trc_step. exists z; split; trivial.
apply Tr1 with x0; trivial.
(*  cas trc_ind; trivial *)
apply trc_ind with z; trivial.
apply IHtc1; trivial.
Qed.

(** If:

- r2 is transitive
- x (r1;r2)+ y r2 z

Then x (r1;r2)+ z *)

Lemma glue_back : forall (A:Type) (r1 r2: Rln A) x y z,
   trans r2 -> tc (rel_seq r1 r2) x y -> r2 y z ->  tc (rel_seq r1 r2) x z.
intros A r1 r2 x y z Tr2 H H0.
remember (rel_seq r1 r2) as r. induction H; subst.
(* x r1 a r2 y r2 z donc x r1 a r2 z (par trans) donc x r1r2 z
   donc x (r1r2)+ z *)
destruct H as [a [? ?]].
apply trc_step. exists a; split; trivial.
apply Tr2 with y; trivial.
(*  cas trc_ind; trivial *)
apply trc_ind with z0; trivial.
apply IHtc2; trivial.
Qed.

(** If two relations are transitive, their hexa is transitive *)

Lemma hx_trans : (*2*)
  forall (A:Type) (r1 r2:Rln A),
  trans r1 -> trans r2 ->
  trans (hx r1 r2).
Proof.
intros.
unfold trans in *; intros.
unfold hx in *.
destruct H1 as [z1 [? ?]].
destruct H2 as [z2 [? ?]].
destruct H3 as [z11 [? ?]].
destruct H4 as [z21 [? ?]].
destruct H3; destruct H4.

- exists z1; split; trivial; clear x H1.
  exists z21; split; trivial; clear z H6.
  destruct H5; destruct H2; left.
  + apply trc_ind with z11; trivial; clear z1 H3.
    apply trc_ind with z2; trivial; clear z21 H4.
    apply trc_step. exists y; split; trivial.
  + apply trc_ind with z11; trivial; clear z1 H3.
    apply glue_front with y; subst; trivial.
  + apply trc_ind with z2; trivial; clear z21 H4.
    apply glue_back with y; subst; trivial.
  + apply trc_ind with z11; subst; trivial.

- subst. exists z1; split; trivial; clear x H1.
  destruct H2.
  + exists z21; split; trivial. clear z H6. left.
    destruct H5.
    { apply trc_ind with z11; trivial; clear z1 H3.
      apply trc_step. exists y; split; trivial. }
    { subst. apply glue_back with y; trivial. }

  + subst. exists z11; split.
    { left; trivial. }
    { destruct H5; destruct H6; subst.
      - left; apply H with z21; trivial.
      - left; trivial.
      - left; trivial.
      - right; trivial. }

- subst. destruct H5.
  + exists z11; split; trivial. clear x H1.
    exists z21; split; trivial. clear z H6.
    left. destruct H2; subst.
    { apply trc_ind with z2; trivial.
      apply trc_step. exists y; split; trivial. }
    { apply glue_front with z2; trivial. }

  + subst. exists z2; split.
    destruct H1; destruct H2; subst.
    left; apply H0 with y; trivial. left; trivial.
    left; trivial. right; trivial.
    clear H1 H2. exists z21; split; trivial. left; trivial.

- subst. destruct H1; destruct H5; destruct H2; destruct H6; subst.
  + exists z11; split. left; trivial.
    exists z21; split. left. apply trc_step. exists y; split; trivial.
    left; trivial.

  + exists z11; split. left; trivial.
    exists z; split. left. apply trc_step. exists y; split; trivial.
    right; trivial.

  + exists z11; split. left; trivial.
    exists z11; split. right; trivial.
    left; apply H with z21; trivial.

  + exists z11; split. left; trivial.
    exists z11; split. right; trivial. left; trivial.

  + exists z21; split. left; apply H0 with y; trivial.
    exists z21; split. right; trivial. left; trivial.

  + exists z; split. left; apply H0 with y; trivial. exists z; split; right; trivial.

  + exists z21; split. left; apply H1.
    exists z21; split. right; trivial. left; apply H4.

  + exists z; split. left; apply H1.
    exists z; split; right; trivial.

  + exists z11; split. right; trivial.
    exists z21; split.
    { left; apply trc_step; exists y; split; [apply H3 | apply H2]. }
    { left; apply H4. }

  + exists z11; split. right; trivial.
     exists z; split; [| right; trivial].
     left; apply trc_step; exists y; split; [apply H3 | apply H2].

  + exists z11; split. right; trivial.
    exists z11; split. right; trivial.
    left; apply H with z21. apply H3. apply H4.

  + exists z11; split. right; trivial.
    exists z11; split. right; trivial.
    left; apply H3.

  + exists z21; split. left; apply H2.
    exists z21; split. right; trivial.
    left; apply H4.

  + exists z; split. left; apply H2.
    exists z; split; right; trivial.

  + exists z21; split; [right; trivial |].
    exists z21; split; [right; trivial |].
    left; apply H4.

  + exists z; split; [right; trivial |].
    exists z; split; right; trivial.
Qed.

(** If two relations are transitive, their hexa' is transitive *)

Lemma hx'_trans : (*2*)
  forall (A:Type) (r1 r2:Rln A),
  trans r1 ->
  trans (hx (tc r2) r1).
Proof.
intros.
unfold trans in *; intros.
unfold hx' in *.
destruct H0 as [z1 [? ?]].
destruct H1 as [z2 [? ?]].
destruct H2 as [z11 [? ?]].
destruct H3 as [z21 [? ?]].
destruct H2; destruct H3.

- exists z1; split; trivial; clear x H0.
  exists z21; split; trivial; clear z H5.
  destruct H4; destruct H1; left.
  + apply trc_ind with z11; trivial; clear z1 H2.
    apply trc_ind with z2; trivial; clear z21 H3.
    apply trc_step. exists y; split; trivial.
  + apply trc_ind with z11; trivial; clear z1 H2.
    apply glue_front with y; subst; trivial.
    intros e1 e2 e3 H12 H23.
      apply trc_ind with e2; auto.
  + apply trc_ind with z2; trivial; clear z21 H3.
    apply glue_back with y; subst; trivial.
  + apply trc_ind with z11; subst; trivial.

- subst. exists z1; split; trivial; clear x H0.
  destruct H1.
  + exists z21; split; trivial. clear z H5. left.
    destruct H4.
    * apply trc_ind with z11; trivial; clear z1 H2.
      apply trc_step. exists y; split; trivial.

    * subst. apply glue_back with y; trivial.
  + subst. exists z11; split. left; trivial.
    destruct H4; destruct H5; subst.
    * left; apply trc_ind with z21; auto.
    * left; trivial.
    * left; trivial.
    * right; trivial.

- subst. destruct H4.
  + exists z11; split; trivial. clear x H0.
    exists z21; split; trivial. clear z H5.
    left. destruct H1; subst.
    * apply trc_ind with z2; trivial.
      apply trc_step. exists y; split; trivial.
    * apply glue_front with z2; trivial.
      subst.
      intros e1 e2 e3 H12 H23.
      apply trc_ind with e2; auto.
  + exists z2; split.
    * destruct H0; destruct H1; subst.
      left; apply H with y; trivial.
      left; trivial.
      left; trivial.
      right; trivial.
    * clear H0 H1. exists z21; split; trivial. left; trivial.

- subst. destruct H0; destruct H4; destruct H1; destruct H5; subst.
  + exists z11; split. left; trivial.
    exists z21; split. left. apply trc_step. exists y; split; trivial.
    left; trivial.

  + exists z11; split. left; trivial.
    exists z; split. left. apply trc_step. exists y; split; trivial.
    right; trivial.

  + exists z11; split. left; trivial.
    exists z11; split. right; trivial.
    left; apply trc_ind with z21; trivial.

  + exists z11; split. left; trivial.
    exists z11; split. right; trivial. left; trivial.

  + exists z21; split. left; apply H with y; trivial.
    exists z21; split. right; trivial. left; trivial.

  + exists z; split. left; apply H with y; trivial. exists z; split; right; trivial.

  + exists z21; split. left; apply H0.
    exists z21; split. right; trivial. left; apply H3.

  + exists z; split. left; apply H0.
    exists z; split; right; trivial.

  + exists z11; split. right; trivial.
    exists z21; split.
    * left; apply trc_step; exists y; split; [apply H2 | apply H1].
    * left; apply H3.

  + exists z11; split. right; trivial.
    * exists z; split; [| right; trivial].
      left; apply trc_step; exists y; split; [apply H2 | apply H1].

  + exists z11; split. right; trivial.
    exists z11; split. right; trivial.
    left; apply trc_ind with z21. apply H2. apply H3.

  + exists z11; split. right; trivial.
    exists z11; split. right; trivial.
    left; apply H2.

  + exists z21; split. left; apply H1.
    exists z21; split. right; trivial.
    left; apply H3.

  + exists z; split. left; apply H1.
    exists z; split; right; trivial.

  + exists z21; split; [right; trivial |].
    exists z21; split; [right; trivial |].
    left; apply H3.

  + exists z; split; [right; trivial |].
    exists z; split; right; trivial.
Qed.

(**
If we have three relations r, r1 and r2 such that:

- r and r2 are transitive relations
- r1 is included in r2

Then, if two elements are related by the transitive closure of the union of
r and r1, they are also related by the hexa of r2 and r.

*)

Lemma union_implies_hexa_path : (*1*)
  forall A (r1 r2 r: Rln A) (x y:A),
  trans r2 ->
  trans r ->
  rel_incl r1 r2 ->
  (tc (rel_union r1 r) x y)->
  (hx r2 r) x y.
Proof.
intros A r1 r2 r x y Ht2 Htr Hincl Hin.
induction Hin as [x y Hs |].
(*step case*)
- inversion Hs as [Hhb | Hpo].
     (*hb*)
  + unfold hx; unfold rel_seq. exists x; split;
      [right; trivial| exists x; split; [right; trivial| left; apply Hincl; apply Hhb]].
     (*po*)
  + unfold hx; unfold rel_seq; exists y; split;
      [left; apply Hpo | exists y; split; [right; trivial|right; trivial]].
  (*ind case*)
- apply (hx_trans Ht2 Htr IHHin1 IHHin2).
Qed.

(** If we have a transitive relation r2 relating x and y, and another
    relation r, if the transitive closure of (r2;r) relates z and y, it
    also relates x and y
*)

Lemma r2_left :
  forall A (r r2:Rln A) (x y z : A),
  trans r2 ->
  r2 x z ->
  tc (rel_seq r2 r) z y ->
  tc (rel_seq r2 r) x y.
Proof.
intros A r r2 x y z Ht2 Hhb_xz Htc_zy.
induction Htc_zy.
- destruct H as [z [Hhb_x0z Hpo_zy]].
  apply trc_step; exists z; split; [|apply Hpo_zy].
  eapply Ht2; [apply Hhb_xz | apply Hhb_x0z].
- apply trc_ind with z; [|apply Htc_zy2].
  apply IHHtc_zy1; apply Hhb_xz.
Qed.

(** If we have a transitive relation r2, and a smaller relation r1 relating
    x and z, and if the transitive closure of (r2;r) relates z and y, then
    it also relates x and y *)

Lemma r1_left :
  forall A (r r1 r2:Rln A) (x y z : A),
  trans r2 ->
  rel_incl r1 r2 ->
  r1 x z ->
  tc (rel_seq r2 r) z y ->
  tc (rel_seq r2 r) x y.
Proof.
intros A r r1 r2 x y z Ht2 Hincl Hhb_xz Htc_zy.
induction Htc_zy.
- destruct H as [z [Hhb_x0z Hpo_zy]].
  apply trc_step; exists z; split; [|apply Hpo_zy].
  eapply Ht2; [apply Hincl; apply Hhb_xz | apply Hhb_x0z].
- apply trc_ind with z; [|apply Htc_zy2].
  apply IHHtc_zy1; apply Hhb_xz.
Qed.

(**
If we have:

- r2 irreflexive and transitive
- r transitive
- r1 relating x and z
- the hexa of r2 and r relates z and x

Then (r2;r) contains a cycle *)

Lemma r1_hexa :
  forall A (r r1 r2:Rln A) (x z : A),
  ~(exists x, r2 x x) ->
  rel_incl r1 r2 ->
  trans r2 ->
  trans r ->
  r1 x z ->
  (hx r2 r) z x ->
  exists y, tc (rel_seq r2 r) y y.
Proof.
intros A r r1 r2 x z Hac2 Hincl Ht2 Htr Hhb_xz Hhx_zx.
destruct Hhx_zx as [y [Hor_zy [y' [Hor_yy' Hor_y'x]]]].
inversion Hor_zy as [Hpo_zy | Heq_zy];
inversion Hor_yy' as [Htc_yy' | Heq_yy'];
inversion Hor_y'x as [Hhb'_y'x | Heq_y'x].

(* x -hb-> z -po-> y -tc-> y' -hb'-> x *)
- exists y; apply trc_ind with y'; [apply Htc_yy'|].
  apply trc_step; exists z; split; [| apply Hpo_zy].
  eapply Ht2; [apply Hhb'_y'x | apply Hincl; apply Hhb_xz].

(* x -hb-> z -po-> y -tc-> y' = x *)
- exists y; rewrite Heq_y'x in Htc_yy';
  apply trc_ind with x; [apply Htc_yy' |
  apply trc_step; exists z; split;
  [apply Hincl; apply Hhb_xz|apply Hpo_zy]].

(* x -hb-> z -po-> y = y' -hb'-> x *)
- exists y; apply trc_step; exists z; split; [| apply Hpo_zy].
  subst;
  eapply Ht2; [apply Hhb'_y'x | apply Hincl; apply Hhb_xz].

(* x -hb-> z -po-> y = y' = x *)
- exists y; subst; apply trc_step; exists z; split;
  [apply Hincl; apply Hhb_xz|apply Hpo_zy].

(* x -hb-> z = y -tc-> y' -hb'-> x *)
- exists y'; eapply r2_left; [apply Ht2 | apply Hhb'_y'x |].
  eapply r1_left; [apply Ht2 | apply Hincl | apply Hhb_xz | subst; apply Htc_yy'].

(* x -hb-> z = y -tc-> y' = x *)
- exists y'; subst.
  eapply r1_left; [apply Ht2 | apply Hincl | apply Hhb_xz | apply Htc_yy'].

- (* x -hb-> z = y = y' -hb'-> x *)  (*contrad hb' x x*)
  subst; assert (r2 x x) as Hhb'_xx.
  + eapply Ht2; [ | apply Hhb'_y'x].
    apply Hincl; apply Hhb_xz.
  + assert (exists x, r2 x x) as Hcy.
    * exists x; auto.
    * generalize (Hac2 Hcy); intro Htriv;
      inversion Htriv.

(* x -hb-> z = y = y' = x *)
- assert (exists x, r2 x x) as Hc.
  subst; exists x; auto.
  contradiction.
Qed.

(** If we have a transitive relation r that relates z and y, then if the
    transitive closure of (r2;r) relates x and z, it also relates x and y *)

Lemma r_right :
  forall A (r r2 : Rln A) (x y z : A),
  trans r ->
  tc (rel_seq r2 r) x z ->
  r z y ->
  tc (rel_seq r2 r) x y.
Proof.
intros A r r2 x y z Htr Htc_xz Hpo_zy.
induction Htc_xz.
- destruct H as [z [Hhb'_xz Hpo_zy0]].
  apply trc_step; exists z; split; [apply Hhb'_xz |
  eapply Htr; [apply Hpo_zy0 | apply Hpo_zy]].
- apply trc_ind with z; [apply Htc_xz1 |].
  apply IHHtc_xz2; apply Hpo_zy.
Qed.

(** If we have:

- r an irreflexive and transitive relation relating z and x
- the hexa or hexa' of r2 and r relate x and z

Then, (r2;r) contains a cycle *)

Lemma hexa_r :
  forall A (r r2 : Rln A) (x z : A),
  ~(exists x, r x x) ->
  trans r ->
  hx r2 r x z ->
  r z x ->
  exists y, tc (rel_seq r2 r) y y.
Proof.
intros A r r2 x z Hac Htr Hhx_xz Hpo_zx.
  destruct Hhx_xz as [y [Hor_xy [y' [Hor_yy' Hor_y'z]]]].
  inversion Hor_xy as [Hpo_xy | Heq_xy];
  inversion Hor_yy' as [Htc_yy' | Heq_yy'];
  inversion Hor_y'z as [Hhb'_y'z | Heq_y'z].
  (* z -po-> x -po-> y -tc-> y' -hb'-> z *)
    generalize (Htr z x y Hpo_zx Hpo_xy); intro Hpo_zy.
  exists y; apply trc_ind with y'; [apply Htc_yy' | apply trc_step].
    exists z; split; [apply Hhb'_y'z |apply Hpo_zy].
  (* z -po-> x -po-> y -tc-> y' = z *)
    generalize (Htr z x y Hpo_zx Hpo_xy); intro Hpo_zy.
  exists y; eapply r_right; [apply Htr | apply Htc_yy' | subst; apply Hpo_zy].
  (* z -po-> x -po-> y = y' -hb'-> z *)
    generalize (Htr z x y Hpo_zx Hpo_xy); intro Hpo_zy.
  exists y; apply trc_step; exists z; split; [subst; apply Hhb'_y'z | apply Hpo_zy].
  (* z -po-> x -po-> y = y' = z *)
    generalize (Htr z x y Hpo_zx Hpo_xy); intro Hpo_zy; subst.
  (* contrad: po z z *)
    assert (exists z, r z z) as Hcy.
      exists z; auto.
    generalize (Hac Hcy); intro Hc; contradiction.
  (* z -po-> x = y -tc-> y' -hb'-> z *)
  exists y; apply trc_ind with y'; [apply Htc_yy' |].
    apply trc_step; exists z; split; [apply Hhb'_y'z | subst; apply Hpo_zx].
  (* z -po-> x = y -tc-> y' = z *)
  exists y; subst; eapply r_right; [apply Htr | apply Htc_yy' | apply Hpo_zx].
  (* z -po-> x = y = y' -hb'-> z *)
  exists y; subst; apply trc_step; exists z; split;
    [apply Hhb'_y'z | apply Hpo_zx].
  (* z -po-> x = y = y' = z *)
(* contrad: po z z *)
    assert (exists z, r z z) as Hcy.
      subst; exists z; auto.
  subst; generalize (Hac Hcy); intro Htriv; inversion Htriv.
Qed.

Lemma hexa'_r :
  forall A (r r2 : Rln A) (x z : A),
  ~(exists x, r x x) ->
  trans r ->
  hx (tc r2) r x z ->
  r z x ->
  exists y, tc (rel_seq (tc r2) (maybe r)) y y.
Proof.
intros A r r2 x z Hac Htr Hhx_xz Hpo_zx.
  destruct Hhx_xz as [y [Hor_xy [y' [Hor_yy' Hor_y'z]]]].
  inversion Hor_xy as [Hpo_xy | Heq_xy];
  inversion Hor_yy' as [Htc_yy' | Heq_yy'];
  inversion Hor_y'z as [Hhb'_y'z | Heq_y'z].
  (* z -po-> x -po-> y -tc-> y' -hb'-> z *)
    generalize (Htr z x y Hpo_zx Hpo_xy); intro Hpo_zy.
  exists y; apply trc_ind with y'; [ | apply trc_step].
  assert (rel_incl (rel_seq (tc r2) r) (rel_seq (tc r2) (maybe r))) as Hi.
    intros e1 e2 [e [H1e He2]]; exists e; split; auto. left; auto.
  apply (tc_incl Hi Htc_yy').
    exists z; split; [apply Hhb'_y'z |left; apply Hpo_zy].
  (* z -po-> x -po-> y -tc-> y' = z *)
    generalize (Htr z x y Hpo_zx Hpo_xy); intro Hpo_zy.
  exists y; eapply r_right; [apply trans_maybe; auto | | subst; left; apply Hpo_zy].
  assert (rel_incl (rel_seq (tc r2) r) (rel_seq (tc r2) (maybe r))) as Hi.
    intros e1 e2 [e [H1e He2]]; exists e; split; auto. left; auto.
  subst; apply (tc_incl Hi Htc_yy').
  (* z -po-> x -po-> y = y' -hb'-> z *)
    generalize (Htr z x y Hpo_zx Hpo_xy); intro Hpo_zy.
  exists y; apply trc_step; exists z; split; [subst; apply Hhb'_y'z | left; apply Hpo_zy].
  (* z -po-> x -po-> y = y' = z *)
    generalize (Htr z x y Hpo_zx Hpo_xy); intro Hpo_zy; subst.
  (* contrad: po z z *)
    assert (exists z, r z z) as Hcy.
      exists z; auto.
    generalize (Hac Hcy); intro Hc; contradiction.
  (* z -po-> x = y -tc-> y' -hb'-> z *)
  exists y; apply trc_ind with y'; [ |].
  assert (rel_incl (rel_seq (tc r2) r) (rel_seq (tc r2) (maybe r))) as Hi.
    intros e1 e2 [e [H1e He2]]; exists e; split; auto. left; auto.
  apply (tc_incl Hi Htc_yy').
    apply trc_step; exists z; split; [apply Hhb'_y'z | subst; left; apply Hpo_zx].
  (* z -po-> x = y -tc-> y' = z *)
  exists y; subst; eapply r_right; [apply trans_maybe; auto | | left; apply Hpo_zx].
  assert (rel_incl (rel_seq (tc r2) r) (rel_seq (tc r2) (maybe r))) as Hi.
    intros e1 e2 [e [H1e He2]]; exists e; split; auto. left; auto.
  apply (tc_incl Hi Htc_yy').
  (* z -po-> x = y = y' -hb'-> z *)
  exists y; subst; apply trc_step; exists z; split;
    [apply Hhb'_y'z | left; apply Hpo_zx].
  (* z -po-> x = y = y' = z *)
(* contrad: po z z *)
    assert (exists z, r z z) as Hcy.
      subst; exists z; auto.
  subst; generalize (Hac Hcy); intro Htriv; inversion Htriv.
Qed.

(** If we have:

- r a transitive and irreflexive relation
- r2 a transitive and irreflexive relation
- r1 included in r2,
- The union of r and r1 is irreflexive but not acyclic

Then (r2;r) is cylic *)

Lemma union_cycle_implies_seq_cycle :
  forall A (r1 r2 r : Rln A) (x:A),
  ~(exists x, rel_union r1 r x x) ->
  ~(exists x, r x x) ->
  ~(exists x, r2 x x) ->
  trans r2 ->
  trans r ->
  rel_incl r1 r2 ->
  (tc (rel_union r1 r)) x x ->
  (exists y, (tc (rel_seq r2 r)) y y).
Proof.
intros A r1 r2 r x ac_u Hacr Hac2 Ht2 Htr Hincl Hc.
generalize (tc_dec Hc); intro Hstep.
destruct Hstep as [z Hsl].
  destruct Hsl as [Hr_xz Hor_zx].
    inversion Hor_zx as [Htc_zx | Heq_zx].
      generalize (union_implies_hexa_path Ht2 Htr Hincl Htc_zx); intro Hp_zx.
      inversion Hr_xz as [Hhb_xz | Hpo_xz].
        eapply (r1_hexa); auto; [apply Hincl | apply Hhb_xz | apply Hp_zx].
        apply (hexa_r Hacr Htr Hp_zx Hpo_xz).
     generalize (ac_u); intro Hco.
     assert (exists x, rel_union r1 r x x) as Hcon.
       exists x; rewrite Heq_zx in Hr_xz; apply Hr_xz.
     contradiction.
Qed.

(** If we have two transitive relations such that the transitive closure of
    their union relates two elements, then the hexa or the hexa' of the second
    and the first relation relate the same elements *)

Lemma union_implies_hx_path :
  forall A (r1 r2: Rln A) (x y:A),
  trans r1 -> trans r2 ->
  (tc (rel_union r1 r2) x y)->
  hx r2 r1 x y.
Proof.
intros A r1 r2 x y Htr1 Htr2 Hin.
induction Hin.
  inversion H as [H1 | H2];
    unfold hx; unfold rel_seq; unfold maybe.
      exists y; split; [left; auto |exists y; split; right;auto].
      exists x; split; [right; auto | exists x; split; [right; auto | left; auto]].
  apply (hx_trans Htr2 Htr1 IHHin1 IHHin2).
Qed.

Lemma union_implies_hx'_path :
  forall A (r1 r2: Rln A) (x y:A),
  trans r1 ->
  (tc (rel_union r1 r2) x y)->
  hx (tc r2) r1 x y.
Proof.
intros A r1 r2 x y Htr1 Hin.
induction Hin.
  inversion H as [H1 | H2];
    unfold hx; unfold rel_seq; unfold maybe.
      exists y; split; [left; auto |exists y; split; right;auto].
      exists x; split; [right; auto | exists x; split; [right; auto | left; auto]].
      apply trc_step; auto.
  apply (hx'_trans Htr1 IHHin1 IHHin2).
Qed.

(** If the transitive closure of (r2;r1) relates x and y then the transitive
    closure of the union of r2 and r1 relates x and y *)

Lemma seq_path_implies_union_path :
  forall A (r1 r2: Rln A) (x y:A),
  tc (rel_seq r2 r1) x y ->
  (tc (rel_union r1 r2) x y).
Proof.
intros A r1 r2 x y Hxy.
induction Hxy.
  destruct H as [z [Hxz Hzy]].
  apply trc_ind with z; apply trc_step; [right; auto | left; auto].
  apply trc_ind with z; auto.
Qed.

(** If the hexa of r2 and r1 relate x and y, then the transitive closure of
    the union of r1 and r2 relate x and y or x is equal to y *)

Lemma hx_implies_union_path :
  forall A (r1 r2: Rln A) (x y:A),
  hx r2 r1 x y ->
  (tc (rel_union r1 r2) x y) \/ x = y.
Proof.
intros A r1 r2 x y Hin.
destruct Hin as [x0 [Hxx0 [y0 [Hx0y0 Hy0y]]]].
inversion Hxx0; [left|].
  inversion Hx0y0.
    inversion Hy0y.
      apply trc_ind with x0.
        apply trc_step; left; auto.
        apply trc_ind with y0.
          apply seq_path_implies_union_path; auto.
          apply trc_step; right; auto.
          subst; apply trc_ind with x0.
            apply trc_step; left; auto.
            apply seq_path_implies_union_path; auto.
      subst; inversion Hy0y.
      apply trc_ind with y0; apply trc_step; [left; auto | right; auto].
      subst; apply trc_step; left; auto.

  inversion Hx0y0.
    inversion Hy0y.
      left; subst; apply trc_ind with y0.
          apply seq_path_implies_union_path; auto.
          apply trc_step; right; auto.
          subst; left; apply seq_path_implies_union_path; auto.
      subst; inversion Hy0y.
      left; apply trc_step; right; auto.
      right; auto.
Qed.

(** If we have:
- r2 transitive, irreflexive and relating x and z
- The hexa of r2 and r1 relating z and x

Then (r2;r1) contains a cycle
*)

Lemma r2_hexa :
  forall A (r1 r2:Rln A) (x z : A),
    ~(exists x, r2 x x) ->
    trans r2 ->
    (*trans r1 ->*)
    r2 x z ->
    (hx r2 r1) z x ->
    exists y, tc (rel_seq r2 r1) y y.
Proof.
  intros A r1 r2 x z Hac2 Ht2 (*Ht1*) Hhb_xz Hhx_zx.
  destruct Hhx_zx as [y [Hor_zy [y' [Hor_yy' Hor_y'x]]]].
  inversion Hor_zy as [Hpo_zy | Heq_zy];
  inversion Hor_yy' as [Htc_yy' | Heq_yy'];
  inversion Hor_y'x as [Hhb'_y'x | Heq_y'x].

  (* x -hb-> z -po-> y -tc-> y' -hb'-> x *)
  - exists y; apply trc_ind with y'; [apply Htc_yy'|].
    apply trc_step; exists z; split; [| apply Hpo_zy].
    eapply Ht2; [apply Hhb'_y'x | apply Hhb_xz].

  (* x -hb-> z -po-> y -tc-> y' = x *)
  - exists y; rewrite Heq_y'x in Htc_yy';
    apply trc_ind with x; [apply Htc_yy' |
                           apply trc_step; exists z; split;
                           [apply Hhb_xz|apply Hpo_zy]].

  (* x -hb-> z -po-> y = y' -hb'-> x *)
  - exists y; apply trc_step; exists z; split; [| apply Hpo_zy].
    subst;
    eapply Ht2; [apply Hhb'_y'x | apply Hhb_xz].

  (* x -hb-> z -po-> y = y' = x *)
  - exists y; subst; apply trc_step; exists z; split;
    [apply Hhb_xz|apply Hpo_zy].

  (* x -hb-> z = y -tc-> y' -hb'-> x *)
  - subst; exists y'; eapply r2_left; [apply Ht2 | apply Hhb'_y'x |].
    eapply r2_left; [apply Ht2 | apply Hhb_xz | subst; apply Htc_yy'].

  (* x -hb-> z = y -tc-> y' = x *)
  - exists y'; subst.
    eapply r2_left; [apply Ht2 | apply Hhb_xz | apply Htc_yy'].

  (* x -hb-> z = y = y' -hb'-> x *)  (*contrad hb' x x*)
  - subst; assert (r2 x x) as Hhb'_xx.
    eapply Ht2; [ | apply Hhb'_y'x].
    apply Hhb_xz.
    assert (exists x, r2 x x) as Hcy.
    exists x; auto.
    generalize (Hac2 Hcy); intro Htriv;
    inversion Htriv.

  (* x -hb-> z = y = y' = x *)
  - assert (exists x, r2 x x) as Hc.
    subst; exists x; auto.
    contradiction.
Qed.

(** If we have:
- r2 irreflexive and relating
- r1 transitive and relating x and z
- the hexa' of r2 and r1 relating z and x

Then we have the union of the transitive closure of r2 and of the reflexive
closure of r1 contains a cycle
*)

Lemma r2_hexa' :
  forall A (r1 r2:Rln A) (x z : A),
    ~(exists x, r2 x x) ->
    trans r1 ->
    r2 x z ->
    (hx (tc r2) r1) z x ->
    exists y, tc (rel_seq (tc r2) (maybe r1)) y y.
Proof.
  intros A r1 r2 x z Hac2 Ht1 Hhb_xz Hhx_zx.
  destruct Hhx_zx as [y [Hor_zy [y' [Hor_yy' Hor_y'x]]]].
  inversion Hor_zy as [Hpo_zy | Heq_zy];
    inversion Hor_yy' as [Htc_yy' | Heq_yy'];
    inversion Hor_y'x as [Hhb'_y'x | Heq_y'x].

  (* x -hb-> z -po-> y -tc-> y' -hb'-> x *)
  - exists y; apply trc_ind with y'; [|].
    assert (rel_incl (rel_seq (tc r2) r1) (rel_seq (tc r2) (maybe r1))) as Hi.
    intros e1 e2 [e [H1e He2]]; exists e; split.
    auto. left; auto.
    apply (tc_incl Hi Htc_yy').
    apply trc_step; exists z; split; [| left; apply Hpo_zy].
    eapply trc_ind; [apply Hhb'_y'x | left; apply Hhb_xz].

  (* x -hb-> z -po-> y -tc-> y' = x *)
  - exists y; rewrite Heq_y'x in Htc_yy';
    apply trc_ind with x; [ |
                            apply trc_step; exists z; split;
                            [left; apply Hhb_xz|left; apply Hpo_zy]].
    assert (rel_incl (rel_seq (tc r2) r1) (rel_seq (tc r2) (maybe r1))) as Hi.
    intros e1 e2 [e [H1e He2]]; exists e; split.
    auto. left; auto.
    apply (tc_incl Hi Htc_yy').

  (* x -hb-> z -po-> y = y' -hb'-> x *)
  - exists y; apply trc_step; exists z; split; [|left; apply Hpo_zy].
    subst;
    eapply trc_ind; [apply Hhb'_y'x | left; apply Hhb_xz].

  (* x -hb-> z -po-> y = y' = x *)
  - exists y; subst; apply trc_step; exists z; split;
    [left; apply Hhb_xz| left; apply Hpo_zy].

  (* x -hb-> z = y -tc-> y' -hb'-> x *)
  - subst; exists y'; eapply r2_left; [ | apply Hhb'_y'x |].
    intros e1 e2 e3 H12 H23; apply trc_ind with e2; auto.
    eapply r2_left; [ | left; apply Hhb_xz | subst].
    intros e1 e2 e3 H12 H23; apply trc_ind with e2; auto.
    assert (rel_incl (rel_seq (tc r2) r1) (rel_seq (tc r2) (maybe r1))) as Hi.
    intros e1 e2 [e [H1e He2]]; exists e; split.
    auto. left; auto.
    apply (tc_incl Hi Htc_yy').

  (* x -hb-> z = y -tc-> y' = x *)
  - exists y'; subst.
    eapply r2_left; [ | left; apply Hhb_xz | ].
    intros e1 e2 e3 H12 H23; apply trc_ind with e2; auto.
    assert (rel_incl (rel_seq (tc r2) r1) (rel_seq (tc r2) (maybe r1))) as Hi.
    intros e1 e2 [e [H1e He2]]; exists e; split.
    auto. left; auto.
    apply (tc_incl Hi Htc_yy').

  (* x -hb-> z = y = y' -hb'-> x *)  (*contrad hb' x x*)
  - exists y'; apply trc_step.
    exists z; split; [|subst]; auto.
    apply trc_ind with x; auto; apply trc_step; auto.

  (* x -hb-> z = y = y' = x *)
  - assert (exists x, r2 x x) as Hc.
    subst; exists x; auto.
    contradiction.
Qed.

(**
If we have:

- r1 transitive and irreflexive
- r2 transitive and irreflexive
- Their union is irreflexive but not acyclic

Then the transitive closure of (r2;r1) contains a cycle
*)

Lemma union_cycle_implies_seq_cycle2 :
  forall A (r1 r2 : Rln A) (x:A),
  ~(exists x, r1 x x) ->
  ~(exists x, r2 x x) ->
  ~(exists y, (rel_union r1 r2) y y) ->
  trans r2 ->
  trans r1 ->
  (tc (rel_union r1 r2)) x x ->
  (exists y, (tc (rel_seq r2 r1)) y y).
Proof.
intros A r1 r2 x Hac1 Hac2 Hu Ht2 Ht1 Hc.
generalize (tc_dec Hc); intro Hstep.
destruct Hstep as [z Hsl].
destruct Hsl as [Hr_xz Hor_zx].
inversion Hor_zx as [Htc_zx | Heq_zx].
- generalize (union_implies_hx_path Ht1 Ht2 Htc_zx); intro Hp_zx.
  inversion Hr_xz as [Hhb_xz | Hpo_xz].
  + apply (hexa_r Hac1 Ht1 Hp_zx Hhb_xz).
  + eapply (r2_hexa); auto; [apply Hpo_xz | apply Hp_zx].
- assert (exists x, rel_union r1 r2 x x) as Hcon.
  exists x; rewrite Heq_zx in Hr_xz; apply Hr_xz.
  contradiction.
Qed.

(** If we have:
- r1 transitive and irreflexive
- r2 irreflexive
- Their union is irreflexive but not acyclic

Then the transitive closure of the sequence the transitive closure of r2 and
of the reflexive closure of r1 contains a cycle
*)

Lemma union_cycle_implies_seq_cycle3 :
  forall A (r1 r2 : Rln A) (x:A),
  ~(exists x, r1 x x) ->
  ~(exists x, r2 x x) ->
  ~(exists y, (rel_union r1 r2) y y) ->
  trans r1 ->
  (tc (rel_union r1 r2)) x x ->
  (exists y, (tc (rel_seq (tc r2) (maybe r1))) y y).
Proof.
intros A r1 r2 x Hac1 Hac2 Hu Ht1 Hc.
generalize (tc_dec Hc); intro Hstep.
destruct Hstep as [z Hsl].
destruct Hsl as [Hr_xz Hor_zx].
inversion Hor_zx as [Htc_zx | Heq_zx].
- generalize (union_implies_hx'_path Ht1 Htc_zx); intro Hp_zx.
  inversion Hr_xz as [Hhb_xz | Hpo_xz].
  + apply (hexa'_r Hac1 Ht1 Hp_zx Hhb_xz).
  + eapply (r2_hexa'); auto; [apply Hpo_xz | apply Hp_zx].
- assert (exists x, rel_union r1 r2 x x) as Hcon.
  exists x; rewrite Heq_zx in Hr_xz; apply Hr_xz.
  contradiction.
Qed.

(** If we have:
- r1 irreflexive
- r2 transitive and irreflexive
- Their union is irreflexive but not acyclic

 Then the transitive closure of the sequence of the transitive closure of r1 and
of the reflexive closure of r2 contains a cycle
*)

Lemma union_cycle_implies_seq_cycle4 :
  forall A (r1 r2 : Rln A) (x:A),
  ~(exists x, r1 x x) ->
  ~(exists x, r2 x x) ->
  ~(exists y, (rel_union r1 r2) y y) ->
  trans r2 ->
  (tc (rel_union r1 r2)) x x ->
  (exists y, (tc (rel_seq (tc r1) (maybe r2))) y y).
Proof.
intros A r1 r2 x Hac1 Hac2 Hu Ht2 Hc.
rewrite union_triv in Hc.
generalize (tc_dec Hc); intro Hstep.
destruct Hstep as [z Hsl].
destruct Hsl as [Hr_xz Hor_zx].
inversion Hor_zx as [Htc_zx | Heq_zx].
- generalize (union_implies_hx'_path Ht2 Htc_zx); intro Hp_zx.
  inversion Hr_xz as [Hhb_xz | Hpo_xz].
  + apply (hexa'_r Hac2 Ht2 Hp_zx Hhb_xz).
  + eapply (r2_hexa'); auto; [apply Hpo_xz | apply Hp_zx].
- assert (exists x, rel_union r1 r2 x x) as Hcon.
  exists x; rewrite Heq_zx in Hr_xz; rewrite union_triv in Hr_xz; apply Hr_xz.
contradiction.
Qed.

(** If we have:
- r1 acyclic
- r2 acyclic
- Their union is irreflexive but not acyclic

Then the sequence of the transitive closures of r2 and r1 is not acyclic
*)

Lemma union_cycle_implies_seq_cycle_fin :
  forall A (r1 r2 : Rln A) (x:A),
  ~(exists x, tc r1 x x) ->
  ~(exists x, tc r2 x x) ->
  ~(exists y, (rel_union r1 r2) y y) ->
  (tc (rel_union r1 r2)) x x ->
  (exists y, (tc (rel_seq (tc r2) (tc r1))) y y).
Proof.
  intros A r1 r2 x Hac1 Hac2 Hu Hc.
  generalize (tc_dec Hc); intro Hstep.
  destruct Hstep as [z Hsl].
  destruct Hsl as [Hr_xz Hor_zx].
  inversion Hor_zx as [Htc_zx | Heq_zx].
  - assert (trans (tc r1)) as Ht1.
    + intros e1 e2 e3 H12 H23; apply trc_ind with e2; auto.
    + assert (trans (tc r2)) as Ht2.
      intros e1 e2 e3 H12 H23; apply trc_ind with e2; auto.
      assert (tc (rel_union (tc r1) (tc r2)) z x) as Htc_zx'.
      * generalize Htc_zx; apply tc_incl; intros e1 e2 H12;
        inversion H12; [left | right]; apply trc_step; auto.
      * generalize (union_implies_hx_path Ht1 Ht2 Htc_zx'); intro Hp_zx.
        inversion Hr_xz as [Hhb_xz | Hpo_xz].
        { assert (tc r1 x z) as Hhb_xz'.
          - apply trc_step; auto.
          - apply (hexa_r Hac1 Ht1 Hp_zx Hhb_xz'). }
        { eapply (r2_hexa); auto.
          apply trc_step; apply Hpo_xz. apply Hp_zx. }
  - assert (exists x, rel_union r1 r2 x x) as Hcon.
    exists x; rewrite Heq_zx in Hr_xz; apply Hr_xz.
    contradiction.
Qed.

(** If the union of two transitive irreflexive is acyclic, their
    sequence is acyclic as well *)

Lemma union_cycle_implies_seq_cycle_final:
  forall A (r1 r2 : Rln A) (x:A),
  ~(exists x, r1 x x) ->
  ~(exists x, r2 x x) ->
  trans r1 ->
  trans r2 ->
  ~(acyclic (rel_union r1 r2)) ->
  ~(acyclic (rel_seq r1 r2)).
Proof.
  intros A r1 r2 x H1irr H2irr H1tra H2tra.
  unfold acyclic. intros H1 H2. destruct H1.
  intros x0 H3.
  assert (~(exists y, (rel_union r1 r2) y y)).
  - intros H4. unfold rel_union in H4.
    destruct H4. destruct H.
    + destruct H1irr. exists x1. auto.
    + destruct H2irr. exists x1. auto.
  - apply trans_tc in H1tra. apply trans_tc in H2tra.
    rewrite <- H1tra in H1irr. rewrite <- H2tra in H2irr.
    rewrite <- H1tra in H2. rewrite <- H2tra in H2.
    rewrite rel_union_refl in H3. rewrite rel_union_refl in H.
    destruct (union_cycle_implies_seq_cycle_fin H2irr H1irr H H3).
    destruct (H2 x1). auto.
Qed.

(** If we have two relations r1 and r2 such that the transitive closure of (r1;r2)
relates x and y, then there are two other elements e1 and e2 such that:

- r1 relates x to e1
- the irreflexive transitive closure of (r2;r1) relates e1 and e2
- r2 relates e2 to y
*)

Lemma seq_path_implies_inv_seq_path :
  forall A (r1 r2 : Rln A) (x y:A),
  (tc (rel_seq r1 r2)) x y ->
  (exists e1, exists e2, r1 x e1 /\ (maybe (tc (rel_seq r2 r1))) e1 e2 /\ r2 e2 y).
Proof.
intros A r1 r2 x y Hxy.
induction Hxy.
destruct H as [e [Hxe Hey]]; exists e; exists e; split; auto; split; auto.
- right; auto.
- destruct IHHxy1 as [e [e' [Hxe [Hee' He'z]]]];
  destruct IHHxy2 as [e1 [e2 [Hz1 [H12 H2y]]]].
  exists e; exists e2; split; auto; split; auto.
  inversion Hee'.
  + left; apply trc_ind with e'; auto.
  inversion H12.
    * apply trc_ind with e1; auto.
      apply trc_step; exists z; auto.
    * apply trc_step; exists z; split; auto; subst; auto.
  + subst.
    inversion H12.
    * left; apply trc_ind with e1; auto.
      apply trc_step; exists z; auto.
    * left; apply trc_step; exists z; split; auto; subst; auto.
Qed.

(** If (r1;r2) is not acyclic, then (r2;r1) isn't either *)

Lemma seq_cycle_implies_inv_seq_cycle :
  forall A (r1 r2 : Rln A) (x:A),
  (tc (rel_seq r1 r2)) x x ->
  (exists y, (tc (rel_seq r2 r1)) y y).
Proof.
intros A r1 r2 x Hx.
generalize (seq_path_implies_inv_seq_path Hx); intros [e [e' [Hxe [Hee' He'y]]]].
inversion Hee'.
- exists e'; apply trc_ind with e; auto.
  apply trc_step; exists x; split; auto.
- subst; exists e'; apply trc_step; exists x; split; auto.
Qed.

(** If we have:

- r1 irreflexive
- r2 transitive and irreflexive
- Their union is irreflexive but not acyclic

Then the transitive closure of the sequence of the reflexive closure of r2 and
of the transitive closure of r1 contains a cycle
*)

Lemma union_cycle_implies_seq_cycle5 :
  forall A (r1 r2 : Rln A) (x:A),
  ~(exists x, r1 x x) ->
  ~(exists x, r2 x x) ->
  ~(exists y, (rel_union r1 r2) y y) ->
  trans r2 ->
  (tc (rel_union r1 r2)) x x ->
  (exists y, (tc (rel_seq (maybe r2) (tc r1))) y y).
Proof.
intros A r1 r2 x Hac1 Hac2 Hu Ht2 Hc.
generalize (union_cycle_implies_seq_cycle4 Hac1 Hac2 Hu Ht2 Hc); intros [y Hy].
apply (seq_cycle_implies_inv_seq_cycle Hy).
Qed.

Lemma union_cycle_implies_seq_cycle6 :
  forall A (r1 r2 r : Rln A) (x:A),
  ~(exists x, rel_union r1 r x x) ->
  ~(exists x, r x x) ->
  ~(exists x, r2 x x) ->
  trans r2 ->
  rel_incl r1 r2 ->
  (tc (rel_union r1 r)) x x ->
  (exists y, (tc (rel_seq (tc r) (maybe r2) )) y y).
Proof.
intros A r1 r2 r x ac_u Hacr Hac2 Ht2 Hincl Hc.
generalize (tc_dec Hc); intro Hstep.
destruct Hstep as [z Hsl].
destruct Hsl as [Hr_xz Hor_zx].
inversion Hor_zx as [Htc_zx | Heq_zx].
- assert (tc (rel_union r2 r) z x) as Hzx'.
  + apply tc_incl with (rel_union r1 r); auto.
    intros e1 e2 H12; inversion H12; auto.
    left; apply Hincl; auto. right; auto.

  + generalize (union_implies_hx'_path Ht2 Hzx'); intro Hp_zx.
    inversion Hr_xz as [Hhb_xz | Hpo_xz].
    assert (r2 x z) as Hxz'.
    * apply Hincl; auto.
    * apply (hexa'_r Hac2 Ht2 Hp_zx Hxz').
    * eapply (r2_hexa'); auto; [apply Hpo_xz | apply Hp_zx].
- generalize (ac_u); intro Hco.
  assert (exists x, rel_union r1 r x x) as Hcon.
  exists x; rewrite Heq_zx in Hr_xz; apply Hr_xz.
  contradiction.
Qed.

(** If we have:
- r irreflexive
- r2 transitive and irreflexive
- The union of r1 and r irreflexive but not acyclic
- r1 is included in r2

Then the transitive closure of the sequence of the reflexive closure of r2
and of the transitive closure of r contains a cycle
*)

Lemma union_cycle_implies_seq_cycle' :
  forall A (r1 r2 r : Rln A) (x:A),
  ~(exists x, rel_union r1 r x x) ->
  ~(exists x, r x x) ->
  ~(exists x, r2 x x) ->
  trans r2 ->
  rel_incl r1 r2 ->
  (tc (rel_union r1 r)) x x ->
  (exists y, (tc (rel_seq (maybe r2) (tc r))) y y).
Proof.
intros A r1 r2 r x Hacu Hacr Hac2 Ht2 Hincl Hc.
generalize (union_cycle_implies_seq_cycle6 Hacu Hacr Hac2 Ht2 Hincl Hc); intros [y Hy].
apply (seq_cycle_implies_inv_seq_cycle Hy).
Qed.

(** If (r2;r1) relates x and y, then the sequence of the reflexive closure of
    r2 and of the sequence of r1 and the reflexive closure of r2 also relates
    x and y
*)

Lemma seq_in_maybe_sure_maybe :
  forall A (r1 r2: Rln A) (x y:A),
  tc (rel_seq r2 r1) x y ->
  tc (rel_seq (maybe r2) (rel_seq r1 (maybe r2))) x y.
Proof.
intros A r1 r2 x y Hxy.
induction Hxy.
- destruct H as [z [Hxz Hzy]]; apply trc_step.
  exists z; split; [left; auto | exists y; split; [auto | right; auto]].
- apply trc_ind with z; auto.
Qed.

(** If we have:

- r1 transitive and irreflexive
- r2 transitive and irreflexive
- Their union is not acyclic

Then, the transitive closure of the reflexive closure of r2 and of the sequence
of r1 and the reflexive closure of r2 also contains a cycle
*)

Lemma union_cycle_implies_seq_seq_cycle :
  forall A (r1 r2: Rln A) (x:A),
  ~(exists x, r1 x x) ->
  ~(exists x, r2 x x) ->
  trans r2 ->
  trans r1 ->
  (tc (rel_union r1 r2)) x x ->
  (exists y, (tc (rel_seq (maybe r2) (rel_seq r1 (maybe r2)))) y y).
Proof.
intros A r1 r2 x Hac1 Hac2 Ht2 Ht1 Hc.
generalize (tc_dec Hc); intro Hstep.
destruct Hstep as [z Hsl].
destruct Hsl as [Hr_xz Hor_zx].
inversion Hor_zx as [Htc_zx | Heq_zx].
- generalize (union_implies_hx_path Ht1 Ht2 Htc_zx); intro Hp_zx.
  inversion Hr_xz as [Hhb_xz | Hpo_xz].
  + generalize (hexa_r Hac1 Ht1 Hp_zx Hhb_xz); intros [y Hy].
    exists y; apply seq_in_maybe_sure_maybe; auto.
  + generalize (r2_hexa Hac2 Ht2 Hpo_xz Hp_zx); intros [y Hy].
    exists y; apply seq_in_maybe_sure_maybe; auto.
- rewrite Heq_zx in Hr_xz; inversion Hr_xz.
  + assert (exists x, r1 x x) as H1.
    exists x; auto.
    contradiction.
  + assert (exists x, r2 x x) as H2.
    exists x; auto.
    contradiction.
Qed.

(** If the transitive closure of the union of r, r1 and r2 relates x and y
    Then the transitive closure of the union of r and the hexa of r2 and r1
    also relates x and y
*)

Lemma union_union_implies_union_hx_path :
  forall A (r1 r2 r : Rln A) (x y:A),
  (tc (rel_union r (rel_union r1 r2)) x y)->
  tc (rel_union r (hx r2 r1)) x y.
Proof.
intros A r1 r2 r x y Hin.
induction Hin.
inversion H as [Hr | H12]; apply trc_step.
- left; auto.
- inversion H12 as [H1 | H2];
  unfold hx; unfold rel_seq; unfold maybe; right.
  + exists y; split; [left; auto |exists y; split; right;auto].
  + exists x; split; [right; auto | exists x; split; [right; auto | left; auto]].
- apply trc_ind with z; auto.
Qed.

(** Relation difference : all the pairs that are related by r2 but not by r1 *)

Definition rel_sub (A:Set) (r1 r2 : Rln A) :=
  fun e1 e2 => r2 e1 e2 /\ not (r1 e1 e2).

(** Corresponds to r if b is true, and to the empty relation otherwise *)

Definition mrel (A:Set) (b:bool) (r:Rln A) :=
  if b then r else (fun e1 => fun e2 => False).

(** A transitive irreflexive relation is acyclic *)

Lemma irr_trans_ac :
  forall A (r : Rln A),
  trans r ->
  ~ (exists x, r x x) ->
  acyclic r.
Proof.
unfold acyclic;
intros A r Ht Hc y Hy.
rewrite (trans_tc Ht) in Hy.
assert (exists x, r x x) as Hco.
- exists y; auto.
- contradiction.
Qed.

(** A linear strict order is a partial order *)

Lemma lin_implies_part :
  forall A (r:Rln A) (s:set A),
  linear_strict_order r s ->
  partial_order r s.
Proof.
intros A r s Hlin.
destruct_lin Hlin; split; auto.
Qed.

(** The union of (r1;r2), (r2;r1), r1 and r2, is included in the transitive
    closure of the union of r1 and r2 *)

Lemma convoluted_u :
  forall A (r1 r2 : Rln A),
  rel_incl (rel_union (rel_union (rel_seq r1 r2) (rel_seq r2 r1))
    (rel_union r1 r2))
      (tc (rel_union r1 r2)).
Proof.
intros A r1 r2 x y Hxy.
inversion Hxy as [Hs | Hu].
- inversion Hs as [H12 | H21].
+ destruct H12 as [z [H1 H2]]; apply trc_ind with z;
    apply trc_step; [left | right]; auto.
+    destruct H21 as [z [H2 H1]]; apply trc_ind with z;
        apply trc_step; [right | left]; auto.
- apply trc_step; auto.
Qed.

End BasicRel.

Unset Implicit Arguments.
