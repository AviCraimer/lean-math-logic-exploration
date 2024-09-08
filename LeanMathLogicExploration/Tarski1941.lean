import  «LeanMathLogicExploration».RelationalAlgebra

-- Tarskis Notation
abbrev one (α) := full α α
abbrev zero (α) := Relation.empty α α
abbrev one' (α) := Relation.id α
abbrev zero' (α) := Relation.notEqual α



-- *** Prove Tarski Axioms as Special Cases ***
theorem tarski1941_axiom_1 : ∀ (x y: α), (Relation.eval (one α)) x y := by
simp [Relation.eval]

theorem tarski1941_axiom_2 : ∀ (x y: α), ¬(Relation.eval (zero α)) x y := by
simp [Relation.eval]

theorem tarski1941_axiom_3 : ∀ (x: α), (Relation.eval (one' α)) x x := by
simp [Relation.eval] ; intro x ; exact ⟨(x, x), by simp⟩

theorem tarski1941_axiom_4 : ∀ (x y z: α),∀ (R: EndoRel α), (eval R x y ∧ eval (one' α) y z) → (eval R x z) := by
intros x y z R; unfold one' Relation.id; simp [Relation.eval, Relation.merge, Relation.domain]; intro evalR yEqz ; rw [yEqz.symm]; use evalR

-- TODO: Prove the remaining axioms and theorems about union and intersection presented in Tarski 1941 paper.
