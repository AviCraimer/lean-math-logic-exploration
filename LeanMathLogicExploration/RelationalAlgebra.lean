import MathLib.Tactic
set_option pp.coercions false

#check Relation


universe u v

abbrev RelationPairs α β  := (a:α) -> (b:β) -> Prop

inductive Relation : (Dom Cod : Type u) -> Type (max u v + 1 )
| atomic (f:RelationPairs α β) : Relation α β
| comp (R:Relation α β) (S:Relation β γ) : Relation α γ
| full (α β: Type u): Relation α β
| id  (α: Type u)  :  Relation α α
| converse (R:Relation α β) : Relation β α
| complement (R:Relation α β) : Relation α β
| product (R: Relation α β )(S: Relation γ δ) : Relation (α × γ ) (β × δ)
| coproduct (R: Relation α β )(S: Relation γ δ) : Relation (Sum α γ ) (Sum β δ)
| copy (α :Type u): Relation α (α × α)
open Relation

def Relation.relativeComp (R:Relation α β) (S:Relation β γ) := complement (comp (complement R) (complement S))

def Relation.negation (R: Relation α β) := converse (complement R)

abbrev Relation.neg (R: Relation α β) :=  R.negation

def Relation.par (R: Relation α β )(S: Relation γ δ) : Relation (α × γ ) (β × δ) := neg (product (neg R) (neg S))

def Relation.with (R: Relation α β )(S: Relation γ δ) :=  neg (coproduct (neg R) (neg S))

def Relation.same (α : Type u) := converse (copy α)

def Relation.different (α: Type u) := complement (equals α)

def Relation.domain (_: Relation α β) := α
def Relation.codomain (_: Relation α β) := β

-- Relation.eval takes a relation and returns a function that tells use whether a pair is in the function.
def Relation.eval (R:Relation α β) : RelationPairs α β :=
match R with
| atomic f => f
| comp R S => fun (a : R.domain) (b : S.codomain) =>
  ∃ (c : S.domain), Relation.eval R a c ∧ Relation.eval S c b
| full α β => fun _ _ => True
| id α => fun a b => a = b
| converse R => fun a b => (Relation.eval R b a)
| complement R => fun a b => ¬(Relation.eval R a b)
| product R S => fun (a: (product R S).domain)(b: (product R S).codomain) => (Relation.eval R a.1 b.1) ∧ (Relation.eval S a.2 b.2)
| coproduct R S => fun (a: (coproduct R S).domain) (b: (coproduct R S).codomain) =>
  match a, b with
  | Sum.inl a', Sum.inl b' => Relation.eval R a' b'
  | Sum.inr a', Sum.inr b' => Relation.eval S a' b'
  | _, _ => False
| copy α => fun a (a1, a2) => a = a1 ∧ a = a2
