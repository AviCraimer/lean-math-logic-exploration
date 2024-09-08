-- Started working on this but it was too complicated and I don't know if I really need it.

-- Define the quotient type for relations
def RelationQuotient (α β : Type u) := Quotient (@instSetoidRelation α β)

-- Lifts both arguments to the quotient.
def RelationQuotient.le (R S : RelationQuotient α β) : Prop :=
  Quotient.lift₂
    (fun R S : Relation α β => R ≤ S)
    (fun (R1 S1 R2 S2 : Relation α β) (eqR : ext_eq R1 R2) (eqS : ext_eq S1 S2) =>
      let forward :  (R1 ≤ S1) → (R2 ≤ S2) := by
        intro R1_le_S1
        have R1_eq_R2 : eval R1 = eval R2 :=  Relation.eval_eq_iff_eq.mpr eqR
        have S1_eq_S2 : eval S1 = eval S2 :=  Relation.eval_eq_iff_eq.mpr eqS
        have conseqent := le_rel_iff_le_eval.mp R1_le_S1
        rw [R1_eq_R2, S1_eq_S2] at conseqent
        exact conseqent

      let backward : (R2 ≤ S2) → (R1 ≤ S1) := by
        intro R2_le_S2
        have R2_eq_R1 : eval R2 = eval R1 :=  (Relation.eval_eq_iff_eq.mpr eqR).symm
        have S2_eq_S1 : eval S2 = eval S1 :=  (Relation.eval_eq_iff_eq.mpr eqS).symm
        have consequent := le_rel_iff_le_eval.mp R2_le_S2
        rw [R2_eq_R1, S2_eq_S1] at consequent
        exact consequent

      let biImpl :  (R1 ≤ S1) ↔  (R2 ≤ S2) :=
        ⟨forward, backward⟩

      propext  biImpl
    )
    R S

-- This sends relations to the quotient type based on the ext_eq equivalence
def Relation.toQuotient (R : Relation α β) : RelationQuotient α β :=
  Quotient.mk (α := Relation α β) (@instSetoidRelation α β) R

 instance : LE (RelationQuotient α β) where
    le R S := RelationQuotient.le R S

-- def lift_rel_le {R S: Relation α β }(h: R ≤ S) : (toQuotient R) ≤ (toQuotient S)  := sorry


theorem lift_rel_le {α β : Type u} {R S: Relation α β} (h: R ≤ S) : ( ⟦R⟧ ≤ ⟦S⟧) := by
  unfold toQuotient


  -- unfold  instLERelationQuotient.1 ⟦R⟧ ⟦S⟧

  -- RelationQuotient.le

  exact h

-- Create PartialOrder instance
-- A partial order is a pre-order plus anti-symmetry
-- Now define the PartialOrder on the Quotient type
instance : PartialOrder (RelationQuotient α β) where
  le := RelationQuotient.le
  lt := fun R S => RelationQuotient.le R S ∧ ¬RelationQuotient.le S R
  le_refl := by
    intro R
    apply Quotient.ind R
    intro R'
    exact le_refl R'
  le_trans := by
    intro R S T
    apply Quotient.ind R
    intro R'
    apply Quotient.ind S
    intro S'
    apply Quotient.ind T
    intro T'
    intro hRS hST
    exact le_trans hRS hST
  le_antisymm := by
    intro R S
    apply Quotient.ind R
    intro R'
    apply Quotient.ind S
    intro S'
    intro hRS hSR
    apply Quotient.sound
    exact ⟨hRS, hSR⟩
  lt_iff_le_not_le := by
    intro R S
    apply Quotient.ind R
    intro R'
    apply Quotient.ind S
    intro S'
    exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
