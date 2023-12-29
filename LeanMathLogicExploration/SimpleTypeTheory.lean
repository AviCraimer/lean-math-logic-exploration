import MathLib.Tactic
-- set_option pp.coercions false


inductive SimpType :=
| ind
| truthVal
| unit
| func : SimpType -> SimpType -> SimpType
deriving BEq

def SimpType.toString  (T: SimpType) (inner: Bool := false) :=
  let bracketWrap := fun (x:String) => if  inner then "("++ x ++ ")" else x
  match T with
  | ind => "𝑖"
  | unit => "{*}"
  | truthVal => "o"
  | func dom cod  => bracketWrap ( (dom.toString true) ++  " ⟶ " ++ (cod.toString true))

instance : ToString SimpType where
  toString t := SimpType.toString t

instance : Repr SimpType where
  reprPrec t _ := SimpType.toString t

open SimpType
infix:60 "-->" => func
infix:60 "⟶" => func -- shortcut \-->

#eval (ind ⟶ (unit ⟶ ind)) ⟶ truthVal
#eval (ind ⟶ unit).toString

def SimpType.toLeanType (T: SimpType) :=
match T with
  | ind => ℕ
  | unit => PUnit
  | truthVal => Bool
  | func dom cod =>  dom.toLeanType → cod.toLeanType

@[match_pattern]
def SimpType.getCodomain (t: SimpType ) :=
match t with
| ind => t
| truthVal => t
| unit => t
| func _ cod => cod


inductive TermSyntax :=
| lamAbs
| var
| app
| equals
| equalsPartial

-- inductive Term : TermSyntax -> SimpType -> Type where

--   | var (sType: SimpType) (term: sType.toLeanType) : Term TermSyntax.var sType

--   -- An abstraction must be a function type.
--   -- Since we are using lean types and terms for the lambda implementation we don't need to worry about abstracting over variables, etc.
--   | lamAbs (dom: SimpType) (cod: SimpType)  (term: (dom ⟶ cod).toLeanType ) : Term TermSyntax.lamAbs (dom ⟶ cod)

--   -- An application stores a function and its argument and has the type of the functions codomain.
--   | app (f: Term TermSyntax.lamAbs (func dom cod)) (arg: Term x dom) : Term TermSyntax.app cod

--   -- A constant equality term (called Q in the Q0 notation)
--   | equals (sType: SimpType) : Term TermSyntax.equals (sType ⟶ (sType ⟶ truthVal))

--   -- A Q constant with one side applied.
--   | equalsPartial (sType: SimpType) (term1: Term syn1 sType)  : Term TermSyntax.equalsPartial (sType ⟶ truthVal)
-- open Term

-- inductive CtxSyn :=
-- | empty
-- | singleMember
-- | multiMember

inductive Context :=
| emptyCtx
| fullCtx (t: SimpType) (ts: List SimpType)

def Context.extend (c: Context) (newType: SimpType) :=
match c with
  | emptyCtx => fullCtx newType []
  | fullCtx t ts => fullCtx newType (t::ts)

def Context.tail (c: Context) :=
match c with
  | emptyCtx => emptyCtx
  | fullCtx _ (x::ts) => fullCtx x ts
  | fullCtx _ [] => emptyCtx

def Context.head (c: Context) (_: c = (fullCtx t ts)) : SimpType := t

def Context.length (c:Context):Nat :=
 match c with
  | emptyCtx => 0
  | fullCtx _ ts => ts.length + 1

def Context.get? (c:Context)(index: Nat) : Option SimpType :=
match c with
 | emptyCtx => none
 | fullCtx t ts => (t::ts).get? index

def Context.fromList (list: List SimpType):Context :=
match list with
| [] => emptyCtx
| x::xs => fullCtx x xs


def testCtx : Context := Context.fullCtx unit  [ind, ind ⟶ truthVal]

#eval testCtx.length

-- Following type theory convension we reverse the order of the context when displaying it so the head of the context is on the right side before the turnstile
def Context.toString (c:Context) :=
  match c with
  | emptyCtx => "[] ⊢ "
  | fullCtx head tail => (List.toString (head::tail).reverse) ++ " ⊢ "

instance : Repr Context where
  reprPrec t _ := Context.toString t

instance : ToString Context where
  toString t := Context.toString t

#eval testCtx
#eval Context.emptyCtx


-- abbrev FinIndex (length: ℕ ) := { (n:ℕ) | n < length }

-- def testFin : FinIndex [1,2,3].length := ⟨ 2, by dsimp⟩

-- #eval testFin

-- Using traditional lambda calc
inductive Term : Context -> TermSyntax -> SimpType -> Type where
-- Given any Context, the variable's index picks out a simple type in the context.
-- The name is for infoview only, it is not used for computation or equality comparison
  | var ( ctx : Context) (index: Nat) (h: ctx.length > index) (name: String := ""): Term ctx TermSyntax.var

  -- Provide any term with a non-empty context.
  -- The lambda abstracts over the head of the context of the body
  -- We don't shift indexes of the nested variables as they refer to their own context
-- e.g.,
--   i, o, i ⊢ 0 1 2
--   i, o ⊢ λ (i, o, i ⊢ 0 1 2 )
  | lamAbs (body: Term (Context.fullCtx dom tail) bodySyn cod)  :  Term (Context.fromList tail) TermSyntax.lamAbs (dom ⟶ cod)

  | app (f: Term  ctx  TermSyntax.lamAbs (func dom cod)) (arg: Term ctx argSyn dom) : Term ctx TermSyntax.app cod

  -- A constant equality term (called Q in the Q0 notation)
  | equals (ctx: Context) (sType: SimpType) : Term ctx TermSyntax.equals (sType ⟶ (sType ⟶ truthVal))

  -- A Q constant with one argument applied.
  -- This could be done with app but it means we can't pattern match on the lamAbs syntax for the first argument of app, so just making a separate constructor for it.
  | equalsPartial (equalsTerm: Term ctx TermSyntax.equals (equalsFirstArg ⟶ equalsPartiallyAppliedType)) (term1: Term ctx syn1 equalsFirstArg)  : Term ctx TermSyntax.equalsPartial equalsPartiallyAppliedType
open Term


-- Why doesn't this work?
def testVar : Term testCtx TermSyntax.var  := var testCtx  1 (by admit)  "x"




def Term.toString (t: Term ctx syn sType)(inner: Bool := false) :=
let bracketWrap := fun (x:String) => if  inner then "("++ x ++ ")" else x
let ctxStr := if inner then "" else ctx.toString
  match t with
    | var  _ _ index varName => ctxStr ++  bracketWrap (varName ++ ":" ++ sType.toString)
    | lamAbs body _ => sorry
    | app f arg => sorry
    | equals _ eqSideType => sorry
    | equalsPartial _ term1 => sorry


#check (·<3)

-- I need to understand equalities and inequalities in terms of proof.

-- ∃ n < OfNat.ofNat 1, n = OfNat.ofNat 1
-- What is OfNat.ofNat ?
def testVar := var testCtx  1 (by simp)  "x"
#eval testVar.toString
/-
 1
 abs 1 => λ.1
 app 0 (abs 1) => 0 λ1   -- The 0 and 1 are actually the same free variable
 abs (abs 1) => [λ.0 λ1]   -- The outer lambda binds both


 2
 abs 2 => λ.2
 app 0 (abs 2) => 0 λ2   -- The 0 and 2 are different free variables
 abs (abs 2) => [λ.0 λ2]   -- The outer lambda binds the 0 but not the 2


WITH FREE VAR CONTEXT

 i, unit, unit  ⊢ 2 => var (var [] unit)   -- To pad the context we add the unit type since this corresponds to calling a function without varying the argument.

 i, null ⊢ abs (i, unit, unit ⊢ 2) => λ:unit.1   -- Nothing is bound, context shifts by 1, the lambda holds the type, but does not need to explicitly hold its variable as it always binds from index 0 in its immediate scope.

 i, null ⊢ app 0 (abs (i, unit, unit ⊢ 2)) => 0 λ2   -- The 0 and 2 are different free variables

 abs (abs 2) => [λ.0 λ2]   -- The outer lambda binds the 0 but not the 2


WITH FREE VAR CONTEXT

 i, unit, unit  ⊢ 2   -- To pad the context we add the unit type since this corresponds to calling a function without varying the argument.

 i, null ⊢ abs (i, unit, unit ⊢ 2) => λ:unit.1   -- Nothing is bound, context shifts by 1, the lambda holds the type, but does not need to explicitly hold its variable as it always binds from index 0 in its immediate scope.

 i, null ⊢ app 0 (abs (i, unit, unit ⊢ 2)) => 0 λ2   -- The 0 and 2 are different free variables

 abs (abs 2) => [λ.0 λ2]   -- The outer lambda binds the 0 but not the 2

-----

i, o, i ⊢ 0 1 2
i, o ⊢ λ (i, o, i ⊢ 0 1 2 )
-- Above, I don't need to shift the variable indexes because they refer to their own nested context, and they remain valid for that.

-/



-- Implement a getLeanTerm function
-- For equality terms it gets a function that compares for boolean term equality
   -- Implement BEq typeclass for Term

-- I can't just return a lean value from the beta reduction. I need to return a simply typed term.
-- So I need to extract the Lean term, run the computation, then repackage the value.
-- def betaReduceStep (redex: Term TermSyntax.app sType)  :=
-- match redex with
-- | app (lamAbs dom _ f) (var _ x )  => f x
-- -- | app (lamAbs dom _ f) (lamAbs _ _ g) => f g
-- | app (lamAbs dom _ f) (app argFunc argArg) => betaReduceStep app argFunc argArg
-- | app (lamAbs _ _ f) (equals _ ) => redex -- hmm, should I be returning a lean type or a Term?
