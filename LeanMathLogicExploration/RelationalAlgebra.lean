import MathLib.Tactic
set_option pp.coercions false

universe u v

abbrev Relation.Pairs α β  := (a:α) -> (b:β) -> Prop

inductive Relation : (Dom Cod : Type u) -> Type (max u + 1 )
| atomic (f:Relation.Pairs α β) : Relation α β
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

def Relation.empty (α β :Type u) := complement (full α β)

def Relation.same (α : Type u) := converse (copy α)
def Relation.different (α: Type u) := neg (copy α)

def Relation.domain (_: Relation α β) := α
def Relation.codomain (_: Relation α β) := β

-- Relation.eval takes a relation and returns a function that tells use whether a pair is in the function.
def Relation.eval (R':Relation α β) : Relation.Pairs α β :=
match R' with
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



@[simp]
theorem Relation.double_converse (R: Relation α β) : eval (converse (converse R)) = eval R := by
  apply funext; intro a; apply funext; intro b
  simp [Relation.eval, Relation.converse]

@[simp]
theorem Relation.double_complement (R: Relation α β) : eval (complement (complement R)) = eval R := by
  apply funext; intro a; apply funext; intro b
  simp [Relation.eval, Relation.complement]

@[simp]
theorem Relation.double_neg (R: Relation α β) : eval (neg (neg R)) = eval R := by
  apply funext; intro a; apply funext; intro b
  simp [Relation.eval, Relation.neg,  Relation.complement, Relation.converse]

-- complement-converse equals converse-complement and we simply to the later.
@[simp]
theorem Relation.converse_complement_sym (R: Relation α β) : eval (complement (converse R)) =  eval (converse ( complement  R))  := by
  apply funext; intro b; apply funext; intro a;
  simp [Relation.eval]

-- Complement-converse simplifies to negation
@[simp]
theorem Relation.complement_converse_to_neg (R: Relation α β) : eval (complement (converse R)) = eval (neg R) := by
  apply funext; intro b; apply funext; intro a;
  simp [Relation.eval, Relation.neg]


-- Composition is associative
theorem Relation.assoc_comp (R: Relation α β) (S: Relation β γ) (T: Relation γ δ) :
  eval (comp (comp R S) T) = eval (comp R (comp S T)) := by
  apply funext; intro a; apply funext; intro d
  simp [Relation.eval, Relation.comp]
  apply Iff.intro
  . intro ⟨c, ⟨b, hab, hbc⟩, hcd⟩
    exact ⟨b, hab, ⟨c, hbc, hcd⟩⟩
  . intro ⟨b, hab, ⟨c, hbc, hcd⟩⟩
    exact ⟨c, ⟨b, hab, hbc⟩, hcd⟩

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

@[simp]
theorem Relation.neg_product (R: Relation α β) (S: Relation γ δ) :
  eval (neg (product R S)) = eval (par (neg R) (neg S)) := by
  apply funext; intro ⟨a, c⟩; apply funext; intro ⟨b, d⟩
  simp [Relation.eval]

@[simp]
theorem Relation.converse_coproduct (R: Relation α β) (S: Relation γ δ) :
  eval (converse (coproduct R S)) = eval (coproduct (converse R) (converse S)) := by
  apply funext; intro ab; apply funext; intro cd
  cases ab <;> cases cd
  . simp [Relation.eval]
  . simp [Relation.eval]
  . simp [Relation.eval]
  . simp [Relation.eval]

@[simp]
theorem Relation.complement_coproduct (R: Relation α β) (S: Relation γ δ) :
eval (complement (coproduct R S)) = eval (with (complement R) (complement S)) := by
apply funext; intro ab; apply funext; intro cd
cases ab <;> cases cd
. simp [Relation.eval]
. simp [Relation.eval]
. simp [Relation.eval]
. simp [Relation.eval]


-- theorem Relation.product_coproduct__dist (R: Relation α α) (S: Relation α α) (T: Relation α α) :
--   eval (product (coproduct R S) T) = eval (coproduct (product R T) (product S T)) := sorry

-- theorem Relation.coproduct_product_dist (R: Relation α β) (S: Relation γ δ) (T: Relation ε ζ) :
-- eval (product (coproduct R S) T) = eval (coproduct (product R T) (product S T))  := by sorry

--  Equiv.sumProdDistrib is the distributivity equivalence for Sum and Product types. We need to apply this so the types match on either side of the eqution.

#print Relation.eval
#print Relation.Pairs


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

-- T⊕(R⊗S) = (T⊕R) ⊗ (T⊕S)
theorem Relation.product_coproduct_dist (R: Relation α β) (S: Relation γ δ) (T: Relation ε ζ) :
  eval (coproduct T (product R S)) =
    fun (a:(ε ⊕ α × γ)) (b: ζ ⊕ β × δ) =>
      let coprodTimesCoprod := eval (product (coproduct T R) (coproduct T S))

      let isoA := (Equiv.prodSumDistrib ε α γ )
      let isoA' := (Equiv.sumProdDistrib ε α γ )
       -- I need:   ε ⊕ α × γ ≃ (ε ⊕ α) × (ε ⊕ γ))
       -- Equiv.prodSumDistrib ε α γ gives: ε × (α ⊕ γ) ≃ ε × α ⊕ ε × γ
       -- Equiv.sumProdDistrib ε α γ gives: (ε ⊕ α) × γ ≃ ε × γ ⊕ α × γ
       -- These are just two sides of the same distributive law. But I need the other distributive law for adding over a product.


      let isoB := (Equiv.prodSumDistrib β δ ζ)
      coprodTimesCoprod (isoA a) (isoB b) := by
  apply funext; intro a; apply funext; intro b
  dsimp [Relation.eval, Equiv.sumProdDistrib]
  cases a <;> cases b
    . simp
    . simp
    . simp
    . simp


-- theorem Relation.product_coproduct__dist (R: Relation α β) (S: Relation γ δ) (T: Relation ε ζ) :
--   eval (product (coproduct R S) T) = eval (coproduct (product R T) (product S T)) := sorry


-- @[simp]
-- theorem Relation.complement_coproduct (R: Relation α β) (S: Relation γ δ) :
--   eval (complement (coproduct R S)) = eval (coproduct (complement R) (complement S)) := by
--   apply funext; intro αβ ; apply funext; intro  βδ
--   cases αβ <;> cases  βδ
--   . simp [Relation.eval]
--   . simp [Relation.eval, Relation.complement, Relation.coproduct]
--   . simp [Relation.eval]
--   . simp [Relation.eval]



-- theorem Relation.complement_relativeComp (R: Relation α β) (S: Relation β γ) :
--   eval (complement (relativeComp R S)) = eval (relativeComp (complement R) (complement S)) := by
--   apply funext; intro a; apply funext; intro c
--   simp [Relation.eval, Relation.complement, Relation.relativeComp]
--   apply Iff.intro
--   . intro h
--     by_contra h'
--     case h.h.mp =>
--       cases h with
--       | intro c₁ hc₁ =>
--         apply h' c₁
--         . simp [Relation.eval, Relation.complement] at hc₁
--           exact hc₁.left
--         . simp [Relation.eval, Relation.complement] at hc₁
--           exact hc₁.right
--   . intro h
--     by_contra h'
--     case h.h.mpr =>
--       by_contra h'
--       apply h' (fun x hRax => h x hRax)
