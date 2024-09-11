
-- Langauge P
-- An Introduction To Mathematical Logic by Peter B. Andrews p 12
inductive PropLogic where
 | atom (name:String)
 | or (a: PropLogic) (b: PropLogic)
 | neg (a: PropLogic)
deriving  BEq



-- TODO: Implement custom Repr so it is readable in the infoview.

open PropLogic

prefix:75 "~" => neg
infix:67 "∨" => or

@[match_pattern]
def PropLogic.ifthen (A B: PropLogic): PropLogic := ~A ∨ B
infix:60 "⊃" => PropLogic.ifthen

@[match_pattern]
def PropLogic.and (A B: PropLogic): PropLogic := ~ (~A ∨ ~B)
infix:65 "&" => PropLogic.and

@[match_pattern]
def PropLogic.iff (A B: PropLogic): PropLogic := (A ⊃ B) & (B ⊃ A)
infix:50 "≡" => PropLogic.iff

def PropLogic.toString (P: PropLogic) (inner: Bool := false) :=
  let bracketWrap := fun (x:String) => if  inner then "("++ x ++ ")" else x

  match P with
  | atom name => name
  | ifthen A B => bracketWrap ( (A.toString true) ++ " ⊃ " ++ (B.toString true))
  | and A B => bracketWrap ( (A.toString true) ++ " & " ++ (B.toString true))
  | or A B =>  bracketWrap ( (A.toString true) ++ " ∨ " ++ (B.toString true))
  | neg A => " ~" ++ (A.toString true)

instance : Repr PropLogic where
  reprPrec t _ := PropLogic.toString t

abbrev T : PropLogic := atom "T"
abbrev S : PropLogic := atom "S"

#eval (T ⊃ S) & (T ⊃ ~S) ∨ T

-- Precedence order ~ & ∨ ⊃ ≡


--p. 23
def PropLogic.axiom_schema1 (A: PropLogic) : PropLogic := (A ∨ A) ⊃ A

def PropLogic.axiom_schema2 (A B: PropLogic) : PropLogic := A ⊃ (B ∨ A )

def PropLogic.axiom_schema3 (A B C: PropLogic) : PropLogic :=  (A ⊃ B) ⊃ ((C ∨ A) ⊃ (B ∨ C))

-- Form a canonical instance of a concrete logically true proposition for convinence.
def PropLogic.TrueProp := axiom_schema1 (atom "Used for True Prop")

def PropLogic.inferencePair (A B: PropLogic) :=
  match A, B with
  |  (P ⊃ _), Q => P == Q
  | _,_ => false

-- If the provided proposition has the form of (P ⊃ Q) & P this will return Q otherwise it returns the conjunction A & B
def PropLogic.infer (A B: PropLogic) : PropLogic :=
 match A, B with
  |  (P ⊃ Q), Arg => if P == Arg then Q else A & B
  | _,_ => A & B


-- A derivation starts with a list of hypotheses (possible empty) in the context
-- Derived statements are added to the context
-- Each step either invokes and axiom schema with some propositions in the context or applies infer

abbrev PropLogic.Context := List PropLogic

inductive DerivationStep (context: PropLogic.Context) where
 -- Axioms schemas may be invoked with any proposition
 | invoke_axiom_schema1 (A: PropLogic)
 | invoke_axiom_schema2 (A B: PropLogic )
 | invoke_axiom_schema3 (A B C: PropLogic)
-- Inference must only be used for propositions in the current derivation context
 | infer (A B: { X:PropLogic // context.contains X})

def PropLogic.applyStep (step: DerivationStep assumptions) : PropLogic :=
  match step with
    | DerivationStep.invoke_axiom_schema1 A => PropLogic.axiom_schema1 A
    | DerivationStep.invoke_axiom_schema2 A B => PropLogic.axiom_schema2 A B
    | DerivationStep.invoke_axiom_schema3 A B C =>  PropLogic.axiom_schema3 A B C
    | DerivationStep.infer A B => PropLogic.infer A.val B.val

inductive Derivation : (assumptions: PropLogic.Context ) -> Type where
 | start (hypotheses : PropLogic.Context) : Derivation hypotheses
 | current (prevSteps: Derivation prevContex) (nextStep: DerivationStep prevContext) : Derivation  ([(applyStep nextStep)].append prevContext).eraseDups

def Derivation.getHypotheses (d: Derivation assumptions): PropLogic.Context :=
  match d with
  | Derivation.start h => h
  | Derivation.current prev _ => getHypotheses prev

def foldAndFn (current: PropLogic) (head: PropLogic) : PropLogic := current & head
def foldAnd (props: PropLogic.Context) :=
  let default := props.headD TrueProp
  let rest := props.tailD []
  rest.foldl foldAndFn default



def PropLogic.getTheorem (d: Derivation assumptions)  (h: assumptions ≠ [] ) :=
  let hypotheses := Derivation.getHypotheses d
  let conclusion := assumptions.head h
   -- If proven with no hypotheses then just the conclusion is a theorem
   -- If proven with some hypotheses the hypotheses are conjuncts and and the conclusion follows.
   if hypotheses == [] then conclusion else  (foldAnd hypotheses) ⊃ conclusion

-- A type that asserts a prop logic proposition as a theorem or schema
inductive PropLogic.Theorem : PropLogic -> Type  where
 | isTheorem (d: Derivation assumptions) (h: assumptions ≠ [] ) : PropLogic.Theorem (getTheorem d h)


-- A schema replaces each atomic proposition in a theorem with a meta-variables (i.e., a Lean variable of type PropLogic)



-- Takes a theorem and returns a schema
inductive PropLogic.DerivedSchema   where
 | isSchema (t: Theorem T) -- ...
