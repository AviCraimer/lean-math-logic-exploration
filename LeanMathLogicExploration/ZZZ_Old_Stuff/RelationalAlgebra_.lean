import Mathlib.Tactic
set_option pp.coercions false

universe u v

abbrev Relation.Pairs (α β: Type u): Type u  := (a:α) -> (b:β) -> Prop



#check fun {α β: Type u} (R S: Relation.Pairs α β ) => R ≤ S

-- The Relation inductive type gives the syntactic composition structure of relations. Relation.eval defines the semantic domain for this syntax.
inductive Relation  :  (Dom:Type u) -> (Cod:Type u) -> Type (u+1)
-- atomic forms a relation directly from a set of pairs
| atomic  {α β: Type u}(f:Relation.Pairs α β)  :   Relation α β

-- pair forms a relation as a pair of two values. This is useful for forming higher-order relations from existing relations.
| pair {α β: Type u} (a: α)(b: β): Relation α β

-- comp stands for composition, and it is the sequential composition operation, which is defined analogously to function composition.
| comp {α β γ : Type u} (R:Relation α β) (S:Relation β γ) : Relation α γ

-- converse is one of the involutions of relations, it reverses the direction of the pairs.
| converse {α β : Type u} (R:Relation α β) : Relation β α

-- complement is the other involution, it consists of the set theoretic complement of pairs relative to a given relation.
| complement {α β : Type u} (R:Relation α β) : Relation α β

-- full is the relation which is the full subset of the Cartersian product of domain and codomain. It's complement is an empty relation.
| full (α β: Type u): Relation α β

-- product is a monoidal product in the category Rel. It corresponds to one of the conjunction operations in linear logic, usually represented as ⊗.
| product  {α β γ δ : Type u} (R: Relation α β )(S: Relation γ δ) : Relation (α × γ) (β × δ)

-- This is the coproduct in the category Rel. It corresponds to one of the disjunction operations in linear logic, usually represented as ⊕. It is interpreted as a disjoint union of domain, codomain, and relational pairs.
| coproduct {α β γ δ : Type u} (R: Relation α β )(S: Relation γ δ) : Relation (Sum α γ ) (Sum β δ)

-- Copy is the diagonal relation, connecting each value in the domain to a pair of identical copies in the codomain. The converse of this is a "merge" relation that sents pairs of identicals to a single copy.  The converse complement (linear negation) of copy is a "different" relation that sends pairs of different elements to all elements.
| copy (α : Type u): Relation α (α × α)

-- cocopy is the categorical dual of copy.  It relates the left and right values of a reflexitve sum type to their common value. This allows us to collapse or merge the disjoint sets of the Sum into a single set which is used to define union. The converse is a "split" relation that splits a single value into two parallel copies in disjoint sets.
| cocopy (α: Type u): Relation (Sum α α) α

-- First is a projection relation from a pair in the domain to the first member of the pair. The converse inserts a value into all pairs where it occurs in first position.
| first (α β: Type u): Relation (α × β) α

-- Second is a projection relation from a pair in the domain to the second member of the pair. The converse inserts a value into all pairs where it occurs in second position.
| second (α β: Type u): Relation (α × β) β

-- Left is an injection relation from a value to itself in the left side of a sum type. The converse is a kind of first projection that works with Sum types.
| left (α β :Type u): Relation α (Sum α β)

-- Right is an injection relation from a value to itself in the right side of a sum type. The converse is a kind of second projection that works with Sum types.
| right (α β :Type u): Relation α (Sum β α)

open Relation



def Relation.domain (_: Relation α β) := α
def Relation.codomain (_: Relation α β) := β

-- *** Eval - Semantics for Relations ***
-- Relation.eval defines the semantic domain of the Relation inductive type. It allows us to prove that different syntactic Relation expressions are extensionally equal.


def Relation.eval (R:Relation α β) : Relation.Pairs α β :=
match R with
-- For atomic relations, we simply return the pair function
| atomic f => f

-- Pair relations consist of the single pair of elements used in their definition
| pair a b => fun (a': α )(b': β ) => a = a' ∧ b = b'

-- A sequential composition of relations yeilds pair if there exists a common element in the middle Codomain/Domain. Note that for relations which have the structure of a function (i.e., relations with the properties of totality and determinism) this definition specializes to the standard definition of function composition.
| comp R S => fun (a : R.domain) (c : S.codomain) =>
  ∃ (b : S.domain), Relation.eval R a b ∧ Relation.eval S b c

-- A full relation has all pairs so returns a constant True proposition.
| full α β => fun _ _ => True

-- Converse returns an evaluation with the order of the arguments switched.
| converse R => fun a b => (Relation.eval R b a)

-- Complement returns the negation of evaluated proposition for each pair.
| complement R => fun a b => ¬(Relation.eval R a b)

-- Product returns true iff the first element of the domain is related by R to the first element of the codomain AND the second element of domain is related by S to the second element of the codomain.
| product R S => fun (a: (product R S).domain)(b: (product R S).codomain) => (Relation.eval R a.1 b.1) ∧ (Relation.eval S a.2 b.2)

-- Coproduct returns true iff a left element of the domain is related by R to a left element of the codomain OR a right element of the domain is related by S to the right element of the codomain.
| coproduct R S => fun (a: (coproduct R S).domain) (b: (coproduct R S).codomain) =>
  match a, b with
  | Sum.inl a', Sum.inl b' => Relation.eval R a' b'
  | Sum.inr a', Sum.inr b' => Relation.eval S a' b'
  | _, _ => False

| copy α => fun a (a1, a2) => a = a1 ∧ a = a2

| cocopy α => fun (aa) a =>
  match aa with
  | Sum.inl a' => a' = a
  | Sum.inr a' => a' = a

-- First and second relate the first (second) elements of a pair in domain to itself in codomain.
| first α β  => fun pair a => pair.1 = a
| second α β => fun pair b => pair.2 = b

-- Left and right relate an element of the domain to the corresponding left (right) elements of the codomain.
| left α β => fun a ab =>
  match ab with
  | Sum.inl a' => a = a'
  | _ => False
| right α β => fun a ba =>
  match ba with
  | Sum.inr a' => a = a'
  | _ => False


-- Expresses the evaluation function as a relation
def Relation.evalRel  {α β : Type u}  : Relation (Relation α β) (PLift (Relation.Pairs α  β)) :=
  atomic fun (R:Relation α β) (f: PLift (Pairs α β) ) =>
    let evaluatedR := PLift.up (Relation.eval R)
  evaluatedR = f

-- **DEFINED RELATION OPERATIONS** --

-- Merge is the converse of copy
def Relation.merge (α) := converse (copy α)

-- Compositional definition of intersection of relations. There is a proof below that this yeilds the set theoretic definition of intersection of pairs.
def Relation.intersection (R: Relation α β) (S: Relation α β) := comp (comp (copy α) (product R S)) (Relation.merge β)


-- Sends each a in α to left a and right a
def Relation.split  (α : Type u) := converse (cocopy α)

-- Compositional definition of union of relations. I should prove that this yeilds the set theoretic definition of union of pairs.
def Relation.union (R: Relation α β) (S: Relation α β) := comp (comp (Relation.split α) (coproduct R S)) (cocopy β)

-- This is a notion from Peirce/Tarski of a second sequential composition operation that is the logical dual of ordinary composition. It replaces the  existential quantifier (∃) in the definition of composition with a universal quantifier (∀). However, it can be defined by a De Morgan equivalence.
-- TODO: Add a proof that this compositional definition is equal to the direct logical definition.
def Relation.relativeComp (R:Relation α β) (S:Relation β γ) := complement (comp (complement R) (complement S))

-- The converse complement of a relation is often refered to as the relative or linear negation of the relation. Note, that this is order invariant, i.e. complement converse = converse complemetn (proof below).
def Relation.negation (R: Relation α β) := converse (complement R)

abbrev Relation.neg (R: Relation α β) :=  R.negation

-- In linear logic, Par is the DeMorgan dual of product.
def Relation.par (R: Relation α β )(S: Relation γ δ) : Relation (α × γ ) (β × δ) := neg (product (neg R) (neg S))

-- In linear logic, With is the DeMOrgan dual of coproduct.
def Relation.with (R: Relation α β )(S: Relation γ δ) :=  neg (coproduct (neg R) (neg S))

-- An empty relation is the complement of the full relation.
def Relation.empty (α β :Type u) := complement (full α β)

-- The different relation is the negation (converse complement) of copy.
def Relation.different (α: Type u) := neg (copy α)

-- The identity relation is the composition of copy and merge
def Relation.id (α : Type u) := comp (copy α) (merge α)

-- The complement of identity is a relation consisting of all pairs of elements that are not equal.
def Relation.notEqual (α : Type u) := complement (Relation.id α)


-- *** Simplification Theorems ***

-- Double converse equals original relation
@[simp]
theorem Relation.double_converse (R: Relation α β) : eval (converse (converse R)) = eval R := by
  apply funext; intro a; apply funext; intro b
  simp [Relation.eval, Relation.converse]

-- Double complement equals original relation
@[simp]
theorem Relation.double_complement (R: Relation α β) : eval (complement (complement R)) = eval R := by
  apply funext; intro a; apply funext; intro b
  simp [Relation.eval, Relation.complement]

-- Double negation (converse complement) equals original relation
@[simp]
theorem Relation.double_neg (R: Relation α β) : eval (neg (neg R)) = eval R := by
  apply funext; intro a; apply funext; intro b
  simp [Relation.eval, Relation.neg,  Relation.complement, Relation.converse]

-- complement-converse equals converse-complement. We simply to the later.
@[simp]
theorem Relation.converse_complement_sym (R: Relation α β) : eval (complement (converse R)) =  eval (converse ( complement  R))  := by
  apply funext; intro b; apply funext; intro a;
  simp [Relation.eval]

-- Complement-converse simplifies to negation. This is really trival but it helps display the expressions in a more readable way.
@[simp]
theorem Relation.complement_converse_to_neg (R: Relation α β) : eval (complement (converse R)) = eval (neg R) := by
  apply funext; intro b; apply funext; intro a;
  simp [Relation.eval, Relation.neg]


-- Converse distributes over composition
@[simp]
theorem Relation.converse_comp (R: Relation α β) (S: Relation β γ) :
  eval (converse (comp R S)) = eval (comp (converse S) (converse R)) := by
  apply funext; intro c; apply funext; intro a
  simp [Relation.eval, Relation.comp, Relation.converse]
  apply Iff.intro
  . intro ⟨b, hab, hbc⟩
    exact ⟨b, hbc, hab⟩
  . intro ⟨b, hcb, hba⟩
    exact ⟨b, hba, hcb⟩

-- TODO:
  -- Complement distributes over composition?
  -- Negation distributes over composition?

-- Converse distributes across product
@[simp]
theorem Relation.converse_product (R: Relation α β) (S: Relation γ δ) :
  eval (converse (product R S)) = eval (product (converse R) (converse S)) := by
  apply funext; intro ⟨b, d⟩; apply funext; intro ⟨a, c⟩
  simp [Relation.eval, Relation.product, Relation.converse]

-- Complement distributes across product
@[simp]
theorem Relation.complement_product (R: Relation α β) (S: Relation γ δ) :
  eval (complement (product R S)) = eval (par (complement R) (complement S)) := by
  apply funext; intro ⟨a, c⟩; apply funext; intro ⟨b, d⟩
  simp [Relation.eval]

-- Negation distribtes across product
@[simp]
theorem Relation.neg_product (R: Relation α β) (S: Relation γ δ) :
  eval (neg (product R S)) = eval (par (neg R) (neg S)) := by
  apply funext; intro ⟨a, c⟩; apply funext; intro ⟨b, d⟩
  simp [Relation.eval]

-- Converse distributes across coproduct
@[simp]
theorem Relation.converse_coproduct (R: Relation α β) (S: Relation γ δ) :
  eval (converse (coproduct R S)) = eval (coproduct (converse R) (converse S)) := by
  apply funext; intro ab; apply funext; intro cd
  cases ab <;> cases cd
  . simp [Relation.eval]
  . simp [Relation.eval]
  . simp [Relation.eval]
  . simp [Relation.eval]

--  Complement distributes across coproduct
@[simp]
theorem Relation.complement_coproduct (R: Relation α β) (S: Relation γ δ) :
eval (complement (coproduct R S)) = eval (Relation.with (complement R) (complement S)) := by
apply funext; intro ab; apply funext; intro cd
cases ab <;> cases cd
. simp [Relation.eval]
. simp [Relation.eval]
. simp [Relation.eval]
. simp [Relation.eval]

-- Composition is associative.
@[simp]
theorem Relation.assoc_comp (R: Relation α β) (S: Relation β γ) (T: Relation γ δ) :
  eval (comp (comp R S) T) = eval (comp R (comp S T)) := by
  apply funext; intro a; apply funext; intro d
  simp [Relation.eval, Relation.comp]
  apply Iff.intro
  . intro ⟨c, ⟨b, hab, hbc⟩, hcd⟩
    exact ⟨b, hab, ⟨c, hbc, hcd⟩⟩
  . intro ⟨b, hab, ⟨c, hbc, hcd⟩⟩
    exact ⟨c, ⟨b, hab, hbc⟩, hcd⟩



--- *** Union and Intersection Theorems ***
-- We give the direct set-theoretic definition of an intersection of two relations.
abbrev intersect_pairs_def (R: Relation α β) (S: Relation α β): Pairs α β  := fun a b => (eval R) a b ∧ (eval S) a b

-- Proof that the compositional definition of intersection is equal to the set theoretic definiton.
theorem Relation.intersect_pairs (R: Relation α β) (S: Relation α β) : eval (Relation.intersection R S) = intersect_pairs_def R S := by
apply funext
intro a
apply funext
intro b
simp [Relation.eval, intersect_pairs_def, Relation.intersection]
constructor
intro ⟨⟨c1, c2⟩, ⟨⟨a1, a2⟩, ⟨ha1, ha2⟩, hr, hs⟩, ⟨hb1, hb2⟩⟩
subst ha1
subst ha2
subst hb1
subst hb2
exact ⟨hr, hs⟩
intro ⟨hr, hs⟩
use (b, b)
constructor
use (a, a)
constructor <;> rfl

-- We give the direct set-theoretic definition of a union of two relations.
abbrev union_pairs_def (R: Relation α β) (S: Relation α β): Pairs α β  := fun a b => (eval R) a b ∨ (eval S) a b

-- Proof that the compositional definition of union is equal to the set theoretic definiton.
theorem Relation.union_pairs (R: Relation α β) (S: Relation α β) : eval (Relation.union R S) = union_pairs_def R S := by
apply funext
intro a
apply funext
intro b
simp [Relation.eval, union_pairs_def, Relation.union]
constructor
intro ⟨c, ⟨c₁, h₁, h₂⟩, h₃⟩
cases c₁ <;> cases c <;> simp at h₁ h₂ h₃ <;> subst h₁<;> subst h₃
· exact Or.inl h₂
· exact Or.inr h₂
· intro h4
  cases h4 with
  | inl h4R =>
    use Sum.inl b
    constructor
    use Sum.inl a
    constructor
  | inr hS =>
    use Sum.inr b
    constructor
    use Sum.inr a
    constructor


-- Ordering by Inclusion
-- Define the LE instance for Relation
-- Now we can use ≤ notation for relations
  instance : LE (Relation α β) where
    le R S := ∀ a b, eval R a b → eval S a b

--  R ≤  S if and only if they eval to pair functions that are less than or equal to eachother.
theorem Relation.le_rel_iff_le_eval {α β : Type u} {R S : Relation α β} :
  R ≤ S ↔ (eval R ≤ eval S) := by
  constructor
  · intro h
    intro a b
    exact h a b
  · intro h
    intro a b
    exact h a b


-- Prove that this ordering is reflexive
theorem Relation.le_refl (R : Relation α β) : R ≤ R := by
  intros a b h
  exact h

-- Prove that this ordering is transitive
theorem Relation.le_trans {R S T : Relation α β} (h₁ : R ≤ S) (h₂ : S ≤ T) : R ≤ T := by
  intros a b hR
  exact h₂ a b (h₁ a b hR)

-- Create the Preorder instance
instance : Preorder (Relation α β) where
  le := (· ≤ ·)
  le_refl := Relation.le_refl
  le_trans := @Relation.le_trans _ _


theorem Relation.le_union_left (R S : Relation α β) : R ≤ Relation.union R S := by
  intros a b h
  simp [Relation.eval, Relation.union]
  use Sum.inl b
  constructor
  · use Sum.inl a
  · simp

theorem Relation.le_union_right (R S : Relation α β) : S ≤ Relation.union R S := by
  intros a b h
  simp [Relation.eval, Relation.union]
  use Sum.inr b
  constructor
  · use Sum.inr a
  · simp

theorem Relation.union_le {R S T : Relation α β} (hR : R ≤ T) (hS : S ≤ T) : Relation.union R S ≤ T := by
  intros a b h
  simp [Relation.eval, Relation.union] at h
  rcases h with ⟨c, ⟨d, hd, hc⟩, hb⟩
  cases d
  case inl d' =>
    cases c
    case inl c' =>
      simp at hc hb
      subst hb
      subst hd
      exact hR _ _ hc
    case inr _ => contradiction
  case inr d' =>
    cases c
    case inl _ => contradiction
    case inr c' =>
      simp at hc hb
      subst hb
      subst hd
      exact hS _ _ hc

theorem Relation.union.assoc {R S T: Relation α β } : union (union R S)

-- Define custom equality for Relation based on union order (inclusion)
def Relation.eq (R S : Relation α β) : Prop :=
  R ≤ S ∧ S ≤ R

-- Notation for extensional equality
infix:50 " ≃ " => Relation.eq



theorem Relation.eval_eq_iff_eq {R S : Relation α β} : (eval R = eval S) ↔ (R ≃ S) := by
  constructor
  · intro h
    unfold eq
    constructor
    · apply le_rel_iff_le_eval.mpr
      rw [h]
      -- exact le_refl _
    · apply le_rel_iff_le_eval.mpr
      rw [←h]
      -- exact le_refl _
  · intro h
    unfold eq at h
    apply funext
    intro a
    apply funext
    intro b
    apply propext
    constructor
    · exact (le_rel_iff_le_eval.mp h.left) a b
    · exact (le_rel_iff_le_eval.mp h.right) a b




-- Prove reflexivity
@[refl]
theorem Relation.eq_refl (R : Relation α β) : R ≃ R :=
  ⟨le_refl R, le_refl R⟩

-- Prove symmetry
@[symm]
theorem Relation.eq_symm {R S : Relation α β} (h : R ≃ S) : S ≃ R :=
  ⟨h.2, h.1⟩

-- Prove transitivity
@[trans]
theorem Relation.eq_trans {R S T : Relation α β} (h₁ : R ≃ S) (h₂ : S ≃ T) : R ≃ T :=
  ⟨le_trans h₁.1 h₂.1, le_trans h₂.2 h₁.2⟩

theorem Relation.eq_iff_eval_eq {R S : Relation α β} :
    R ≃ S ↔ (∀ a b, eval R a b ↔ eval S a b) := by
  constructor
  · intro h
    intro a b
    exact ⟨fun hr => h.1 a b hr, fun hs => h.2 a b hs⟩
  · intro h
    constructor
    · intro a b hr
      exact (h a b).1 hr
    · intro a b hs
      exact (h a b).2 hs

-- Extentional equality implies evaluation equality

theorem Relation.eq_to_eval {R S : Relation α β} (h : R ≃ S) :
    eval R = eval S := by
  funext a b
  exact propext (Relation.eq_iff_eval_eq.1 h a b)

theorem Relation.eval_to_eq {R S : Relation α β} (h: eval R = eval S) : R ≃ S := by
  unfold eq
  constructor
  · intro a b hR
    rw [←h]
    exact hR
  · intro a b hS
    rw [h]
    exact hS



theorem Relation.union_comm {R S : Relation α β} : Relation.union R S ≃ Relation.union S R := by
  apply Relation.eq_iff_eval_eq.2
  intro a b
  simp [Relation.union]
  have h: coproduct R S = coproduct S R := sorry
  rw [h]

theorem Relation.union_assoc {R S T : Relation α β} :
    Relation.union (Relation.union R S) T ≃ Relation.union R (Relation.union S T) := by

    have h := Relaion.union_trans
    rw [Relation.union_comm]


-- Create Setoid instance
-- A Setoid is a set together with an equivalence relation
instance : Setoid (Relation α β) where
  r :=  Relation.eq
  iseqv := {
    refl := Relation.eq_refl
    symm := Relation.eq_symm
    trans := Relation.eq_trans
  }

  instance : HasEquiv (Relation α β) where
  Equiv := Relation.eq




-- Tarski's theory works for relations with the same domain and codomain
abbrev Relation.EndoRel (α: Type U) := Relation α α





-- TODO: Prove that the so-called "allegory" laws holds for relations.
-- https://en.wikipedia.org/wiki/Allegory_(mathematics)
-- Allegory laws for intersection
-- Prove, intersection is idempotent, associative, commutative
-- Prove, converse distributes over intersection
-- composition is semi-distributive over union
-- modularity law
  -- Questions:
    -- should complement distribute over union?
    -- Does complement form a second allegory structure?


-- *** First Order Logic

-- Helper for getArityType. Note that arity' is arity - 1.
def getProduct (α :Type u) (arity': Nat):Type u :=
  match arity' with
    | n+1 => α × (getProduct α n)
    | _ => α

-- Returns PUnit for arity 0, returns α for arity 1, α × α for arity 2, etc.
def getArityType (α :Type u)(arity: Nat): Type u :=
if arity == 0 then PUnit else  getProduct α (arity-1)





-- 2 => α × α

-- not zero
-- arity' := 3
-- match artiy' with 2 + 1 => α × getArityType α 2
-- match artiy' with 1 + 1 => α × getArityType α 1


-- abbrev EndoRel (α: Type u) := Relation α α

-- def FirstOrderRelation (α : Type u) (arity: Nat) (coarity: Nat) :

-- Based on EndoRelations and Relations on products of EndoRelations
  -- Coproducts are used to define union, but these are never exposed as an interface in the logic.
-- Univesally quantified props
  -- Implicit free variables
--Existentially quantified props
  -- Compose with full at one end or the other to implicity existentially quantify
-- Not, complement
-- And, Intersection
-- Or, Union
-- Evaluate at constant
  -- Compose with pair constructor on left or right or both left and right.
-- The whole relation is interpreted as a proposition by asking if there are any pairs in it. If it is empty the associated proposition is false.
-- Arity and co-arity
  -- Cartesian product on the right of relation gives arity
  -- Cartesian product on the left of relation gives coarity
  -- We ignore different bracketings (we can have some cannonical bracketing from top to bottom)

-- Higher Order Logic
  -- Relation Types
  -- Base type of individuals
  -- Relations built inductively from relations on individuals
  -- Could have a version of the inductive type which only takes the base type as a type parameter. This way all higher order relations built on a given base type could live in the same type universe (I think)
  -- Use ⊕ and ⊗ instead of union and intersection for or and and.




-- *** Odds and Ends (Very Rough WIP) ***

-- theorem Relation.product_coproduct__dist (R: Relation α α) (S: Relation α α) (T: Relation α α) :
--   eval (product (coproduct R S) T) = eval (coproduct (product R T) (product S T)) := sorry

-- theorem Relation.coproduct_product_dist (R: Relation α β) (S: Relation γ δ) (T: Relation ε ζ) :
-- eval (product (coproduct R S) T) = eval (coproduct (product R T) (product S T))  := by sorry

--  Equiv.sumProdDistrib is the distributivity equivalence for Sum and Product types. We need to apply this so the types match on either side of the eqution.


-- (R⊕S)⊗T = (R⊗T)⊕(S⊗T)
theorem Relation.coproduct_product_dist (R: Relation α β) (S: Relation γ δ) (T: Relation ε ζ) :
  eval (product (coproduct R S) T) =
    fun (a:(α ⊕ γ) × ε) (b: (β ⊕ δ) × ζ) =>
      let prodPlusProd := eval (coproduct (product R T) (product S T))
      let isoDomain := (Equiv.sumProdDistrib α γ ε)
      let isoCodomain := (Equiv.sumProdDistrib β δ ζ)
      prodPlusProd (isoDomain a) (isoCodomain b) := by
  apply funext; intro a; apply funext; intro b
  dsimp [Relation.eval, Equiv.sumProdDistrib]
  cases a.1 <;> cases b.1
  . simp
  . simp
  . simp
  . simp






-- -- T⊕(R⊗S) = (T⊕R) ⊗ (T⊕S)
-- theorem Relation.product_coproduct_dist (R: Relation α β) (S: Relation γ δ) (T: Relation ε ζ) :


-- Other Relation Theorems

--Pairs:
-- Prove that every relation is equal to a (possibly infinite) union of pairs. Not sure if my current union definition allows for infinite unions.

-- Prove that if S ⊆ R and S is non-empty then there is a composition T;R;T' = S such that T and T' are subrelations of Id

-- Prove demorgan dualities between union and intersection

-- Prove distributive laws from Tarski paper for union and intersection.

-- Prove that Types and Relations form a category.

-- Show that this category forms an allegoy with union.
