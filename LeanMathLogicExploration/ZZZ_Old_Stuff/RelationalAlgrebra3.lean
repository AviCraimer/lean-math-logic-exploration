

-- Goal write version of relation exp that has arity rather than types.

-- Define a Relation as an interpretation of a relation exp that assigns every atomic relation a function that is compatible with the arity, and where the types match for things like composition, ⊕, ⊗, etc.

-- The context holds the names of atomic relations and a list of constraints on them, e.g., equality to other types, etc.


-- Then eval works on the Relation


def getArityType (α :Type u)(arity: Nat): Type u :=

match arity with
  | n+1 => α × (getArityType α  n)
  | _ => α
