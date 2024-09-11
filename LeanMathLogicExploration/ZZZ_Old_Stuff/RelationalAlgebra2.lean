-- Work In Progress


import Mathlib.Tactic
set_option pp.coercions false

universe u v

abbrev Relation.Pairs {α β: Type u} : Type u  :=  (a:α) -> (b:β) -> Prop

abbrev Context := List String
def addContexts := fun (a b: Context) => (List.append a b).dedup

-- Not sure how this is supposed to work.

-- The Relation inductive type gives the syntactic composition structure of relations. Relation.eval defines the semantic domain for this syntax.
inductive Relation  : (contex: List String)-> (Dom:Type u) -> (Cod:Type u) -> Type (u+1)
-- atomic forms a relation directly from a set of pairs
| atomic (f:  α -> β -> Prop) : Relation [] α β

-- TODO: We need to ensure the varName has the correct type.
| vari  {α β: Type u}(varName: String)  : Relation [varName] α β

-- pair forms a relation as a pair of two values. This is useful for forming higher-order relations from existing relations.
| pair {α β: Type u} (a: α)(b: β): Relation [] α β

-- comp stands for composition, and it is the sequential composition operation, which is defined analogously to function composition.
| comp {α β γ : Type u} (R:Relation ctx1 α β) (S:Relation ctx2 β γ) : Relation (addContexts ctx1 ctx2) α γ

-- converse is one of the involutions of relations, it reverses the direction of the pairs.
| converse {α β : Type u} (R:Relation ctx α β) : Relation ctx β α

-- complement is the other involution, it consists of the set theoretic complement of pairs relative to a given relation.
| complement {α β : Type u} (R:Relation ctx α β) : Relation ctx α β

-- full is the relation which is the full subset of the Cartersian product of domain and codomain. It's complement is an empty relation.
| full (α β: Type u): Relation [] α β

-- product is a monoidal product in the category Rel. It corresponds to one of the conjunction operations in linear logic, usually represented as ⊗.
| product  {α β γ δ : Type u} (R: Relation ctx1 α β )(S: Relation ctx2 γ δ) : Relation (addContexts ctx1 ctx2) (α × γ) (β × δ)

-- This is the coproduct in the category Rel. It corresponds to one of the disjunction operations in linear logic, usually represented as ⊕. It is interpreted as a disjoint union of domain, codomain, and relational pairs.
| coproduct {α β γ δ : Type u} (R: Relation ctx1 α β )(S: Relation ctx2 γ δ) : Relation  (addContexts ctx1 ctx2) (Sum α γ ) (Sum β δ)

-- Copy is the diagonal relation, connecting each value in the domain to a pair of identical copies in the codomain. The converse of this is a "merge" relation that sents pairs of identicals to a single copy.  The converse complement (linear negation) of copy is a "different" relation that sends pairs of different elements to all elements.
| copy (α : Type u): Relation [] α (α × α)

-- cocopy is the categorical dual of copy.  It relates the left and right values of a reflexitve sum type to their common value. This allows us to collapse or merge the disjoint sets of the Sum into a single set which is used to define union. The converse is a "split" relation that splits a single value into two parallel copies in disjoint sets.
| cocopy (α: Type u): Relation [] (Sum α α) α

-- First is a projection relation from a pair in the domain to the first member of the pair. The converse inserts a value into all pairs where it occurs in first position.
| first (α β: Type u): Relation [] (α × β) α

-- Second is a projection relation from a pair in the domain to the second member of the pair. The converse inserts a value into all pairs where it occurs in second position.
| second (α β: Type u): Relation [] (α × β) β

-- Left is an injection relation from a value to itself in the left side of a sum type. The converse is a kind of first projection that works with Sum types.
| left (α β :Type u): Relation [] α (Sum α β)

-- Right is an injection relation from a value to itself in the right side of a sum type. The converse is a kind of second projection that works with Sum types.
| right (α β :Type u): Relation [] α (Sum β α)

open Relation


def Interpret (R: Relation ctx α β) (varName: String) :=
  if not (ctx.contains varName) then R else
  (f: α -> β -> Prop) :=
