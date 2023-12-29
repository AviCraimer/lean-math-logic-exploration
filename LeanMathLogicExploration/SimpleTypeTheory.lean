import MathLib.Tactic
set_option pp.coercions false


inductive SimpType :=
| ind
| truthVal
| func : SimpType -> SimpType -> SimpType

def SimpType.toString  (T: SimpType) (inner: Bool := false) :=
  let bracketWrap := fun (x:String) => if  inner then "("++ x ++ ")" else x
  match T with
  | ind => "𝑖"
  | truthVal => "o"
  | func dom cod  => bracketWrap ( (dom.toString true) ++  " ⟶ " ++ (cod.toString true))

instance : Repr SimpType where
  reprPrec t _ := SimpType.toString t

open SimpType
infix:60 "-->" => func
infix:60 "⟶" => func -- shortcut \-->

#eval (ind ⟶ (ind ⟶ ind)) ⟶ truthVal

def SimpType.toLeanType (T: SimpType) :=
match T with
  | ind => ℕ
  | truthVal => Bool
  | func dom cod =>  dom.toLeanType → cod.toLeanType

@[match_pattern]
def SimpType.getCodomain (t: SimpType ) :=
match t with
| ind => t
| truthVal => t
| func _ cod => cod


inductive TermSyntax :=
| lamAbs
| var
| app

inductive Term : TermSyntax -> SimpType -> Type where

  | var (sType: SimpType) (term: sType.toLeanType) : Term TermSyntax.var sType

  -- An abstraction must be a function type.
  -- Since we are using lean types and terms for the lambda implementation we don't need to worry about abstracting over variables, etc.
  | lamAbs (dom: SimpType) (cod: SimpType)  (term: (dom ⟶ cod).toLeanType ) : Term TermSyntax.lamAbs (dom ⟶ cod)

  -- An application stores a function and its argument and has the type of the functions codomain.
  | app (f: Term TermSyntax.lamAbs absType) (arg: Term x dom) : Term TermSyntax.app absType.getCodomain

  -- A constant equality term (called Q in the Q0 notation)
  -- It takes two terms of the same simple type to truth values
  | equals (sType: SimpType) (term1: Term syn1 sType) (term2: Term syn2 sType) : Term TermSyntax.lamAbs (sType ⟶ (sType ⟶ truthVal))
open Term




-- Implement a getLeanTerm function
-- For equality terms it gets a function that compares for boolean term equality
   -- Implement BEq typeclass for Term

-- I can't just return a lean value from the beta reduction. I need to return a simply typed term.
-- So I need to extract the Lean term, run the computation, then repackage the value.
-- def betaReduceStep (redex: Term TermSyntax.app sType)  :=
-- match redex with
-- | app (lamAbs dom _ f) (var typeX x )  => f x
-- | app (lamAbs dom cod f) (lamAbs _ _ g) => f g
-- | app (lamAbs dom _ f) (app argFunc argArg) => betaReduceStep app argFunc argArg
-- | app (abs dom cod f) (equals _ t1 t2 ) => 0
