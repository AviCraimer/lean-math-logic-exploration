import Mathlib.Tactic
import Mathlib.Data.Vector
import LeanMathLogicExploration.SubstructuralLogics.Language
set_option pp.coercions false



inductive Punctuation (n: Nat)
| punct (arity: ℕ) (name: String) : Punctuation n
deriving DecidableEq
open Punctuation


def Punctuation.arity (_: Punctuation n) := n


-- Very similar to the definition of a formula. Only structural difference is it is parameterized by a language.
-- Definition 2.14 p 19. Restall doesn't use the term "Combined Formulas" but it seems appropriate to have a name analogous to "Formulas"
mutual
  inductive CombinedFormula (L: Language)
  | formula (a: L.Formulas)
  | composite (c: Punctuation n) (args: ComboArgs L n)
  deriving DecidableEq

  inductive ComboArgs (L: Language) : Nat → Type
  | nil : ComboArgs L 0
  | cons : (CombinedFormula L) → ComboArgs L n → ComboArgs L (n+1)
  deriving DecidableEq
end


open CombinedFormula


def ComboArgs.arity (_: ComboArgs L n) := n


mutual
def CombinedFormula.substruct {L : Language} (f: CombinedFormula L):Finset (CombinedFormula L) :=
match f with
| formula _ => {f}
| composite _ args =>  {f} ∪ ComboArgs.getArgsFormulas args.arity args

def ComboArgs.getArgsFormulas (n: ℕ) (args: ComboArgs L n) :=
  match n with
  | (m+1) =>
    match args with
    | ComboArgs.cons P (args': ComboArgs L m) => (P.substruct) ∪ (ComboArgs.getArgsFormulas m args')
  | _ => ∅
end


def ComboArgs.every {L:Language} (f: (CombinedFormula L) -> Prop)(args: ComboArgs L n) :=
match args with
| cons P args' => f P ∧ (every f args')
| nil => True

-- A finite set of n-ary connective for each arity.
def FinitePunctuation :=  (n:ℕ) -> ↑(Finset (Punctuation n))


mutual
  def isInStructure  {L:Language}(fp: FinitePunctuation)(f: CombinedFormula L): Prop :=
    match f with
    | formula _ => True
    | composite c args => (c ∈ fp c.arity) ∧ isInComboArgs fp args

  def isInComboArgs  {L:Language} (fp: FinitePunctuation) : ∀ {n : ℕ}, ComboArgs L n → Prop
  | _, (ComboArgs.cons P args') => isInStructure fp P ∧ isInComboArgs fp args'
  | _, _ => True
end


-- Definition 2.14, p. 19
structure LogicStructure (L:Language) where
  punctuation : FinitePunctuation
  ComboFormulas := {S: (CombinedFormula L) | isInStructure punctuation S  }
  Singletons := {S: (CombinedFormula L) | ∃(P:L.Formulas), S = (formula P)  }
  Composites := {S: (CombinedFormula L) | isInStructure punctuation S ∧ ¬∃(A: L.Formulas), S = (formula A) }


-- Definition 2.16, p. 20
structure Consecution (L:Language)(S:LogicStructure L) where
  antecedant: S.ComboFormulas
  consequent: L.Formulas


structure Inference (L:Language)(S:LogicStructure L) where
  premises: Finset (Consecution L S)
  conclusion: Consecution L S

-- An axiom is an inference with an empty set of premises
def Axiom (L:Language)(S:LogicStructure L) := {I: Inference L S | I.premises = ∅  }

-- A rule is a set of inferences
abbrev Rule (L:Language)(S:LogicStructure L) := Set (Inference L S)

-- An axiom schema is a rule where all members are axioms.
def AxiomSchema (L:Language)(S:LogicStructure L) := {R: Rule L S | ∀ (I: Inference L S), ((I ∈ R) →  I.premises = ∅ ) }
