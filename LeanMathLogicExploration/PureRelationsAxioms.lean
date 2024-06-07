import MathLib.Tactic
set_option pp.coercions false
universe u v

-- This is very rough and experimental. I'm exploring the idea of defining an implicit domain of "pure relations" on analogy with the set theoretic idea of pure sets. Thus, all objects are relations, and relations are any objects that satisfy the axioms.


structure PureRel where
  Rel: Type*
  -- Evaluates R with the pair x, y. Note however, that x and y are also themselves relations, unlike with the usual way of thinking.
  eval (x R y: Rel): Prop

  ax_empty: ∃ (E: Rel), (∀ (x y: Rel), ¬ (eval x E y))

  -- This is the actual empty relation element used in the proof of ax_empty.
  empty : Rel := ax_empty.fst

  ax_extensionality (R S: Rel) :  R = S ↔ ∀ (x y: Rel), eval x R y = eval x S y

  -- Defines a relation that pairs two relations.
  ax_pairing (x y:Rel): (∃ (P:Rel), (∀ (z w:Rel), (eval z P w) ↔ x = z ∧ y = w ))

  -- This uses the axiom of pairing to get the pair relation, i.e., the relation P that has only x P y.
  pair (x y: Rel) := (ax_pairing x y).fst

  -- Union of relations is a relation, we can now build up finite relations as pairs.
  ax_union (R S: Rel): ∀ (x y: Rel), ∃ (U: Rel), eval x U y ↔ (eval x R y) ∧ (eval x S y)

  union (R S: Rel) := (ax_union R S).fst

  ax_complement (R:Rel): ∃ (R' :Rel), ∀ (x y: Rel), (eval x R' y) ↔ ¬(eval x R y)

  complement (R:Rel): (ax_complement R).fst

  ax_converse (R:Rel): ∃ (R': Rel), ∀ (x y: Rel), (eval y R' x) ↔ (eval x R y)

  converse (R:Rel): (ax_complement R).fst

  -- This says that their exists an infinite relation.
  -- It has the the empty relation related to itself, and for every pair which it relates reflexively, it also relates reflexively the pair of that relation. This makes it closed under the reflexive application of the pair axiom which functions here analogously to a successor function.
  -- Note: This does not exclude the possibility that it could have additional structure. We might want to add that it is the minimal such relation, but that would add further complexity to the axiom.
  ax_infinity: ∃ (I:Rel), eval (emptyRel I emptyRel) ∧ ∀ (x: Rel), (eval x InfRel x) → (eval (pair x x) I (pair x x))
