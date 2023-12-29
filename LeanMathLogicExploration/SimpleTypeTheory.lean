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



structure CtxEl :=
  type: SimpType
  name: String

def CtxEl.toString (el : CtxEl) :=  el.name ++ ":" ++ el.type.toString


instance : Repr CtxEl where
  reprPrec t _ := CtxEl.toString t

instance : ToString CtxEl where
  toString t := CtxEl.toString t

#eval CtxEl.mk ind "x"

inductive Context :=
| emptyCtx
| fullCtx (t: CtxEl) (ts: List CtxEl)

def Context.extend (c: Context) (newEl: CtxEl) :=
match c with
  | emptyCtx => fullCtx newEl []
  | fullCtx t ts => fullCtx newEl (t::ts)

def Context.tail (c: Context) :=
match c with
  | emptyCtx => emptyCtx
  | fullCtx _ (x::ts) => fullCtx x ts
  | fullCtx _ [] => emptyCtx

def Context.head (c: Context) (_: c = (fullCtx t ts)) : CtxEl := t

def Context.length (c:Context):Nat :=
 match c with
  | emptyCtx => 0
  | fullCtx _ ts => ts.length + 1

def Context.toList (c: Context): List CtxEl :=
match c with
  | emptyCtx => []
  | fullCtx t ts => t::ts

def Context.toTypes (c: Context): List SimpType := c.toList.map (fun (el:CtxEl) => el.type )

def Context.toNames (c: Context): List String := c.toList.map (fun (el:CtxEl) => el.name )

def Context.fromList (list: List CtxEl):Context :=
match list with
| [] => emptyCtx
| x::xs => fullCtx x xs

def testCtx : Context := Context.fullCtx (CtxEl.mk unit "x")  [CtxEl.mk ind "p", CtxEl.mk (ind ⟶ truthVal) "f"]

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

inductive TermSyntax :=
| lamAbs
| var
| app
| equals
| equalsPartial


inductive Term : Context -> TermSyntax -> SimpType -> Type where
-- Given any Context, the variable's index picks out a simple type in the context.
-- The name is for infoview only, it is not used for computation or equality comparison
  | var ( ctx : Context) (index: Fin (ctx.toList.length)) : Term ctx TermSyntax.var (ctx.toList.get index).type

  -- Provide any term with a non-empty context.
  -- The lambda abstracts over the head of the context of the body
  -- We don't shift indexes of the nested variables as they refer to their own context
-- e.g.,
--   i, o, i ⊢ 0 1 2
--   i, o ⊢ λ (i, o, i ⊢ 0 1 2 )
  | lamAbs (body: Term (Context.fullCtx domEl tail) bodySyn codType)   :  Term (Context.fromList tail) TermSyntax.lamAbs ((domEl.type) ⟶ (codType))
-- Issue: You can't apply the variable to the lambda because they will have different contexts!


  | app (f: Term  ctx  TermSyntax.lamAbs (dom ⟶ cod)) (arg: Term ctx argSyn dom) : Term ctx TermSyntax.app cod

  -- A constant equality term (called Q in the Q0 notation)
  | equals (ctx: Context) (sType: SimpType) : Term ctx TermSyntax.equals (sType ⟶ (sType ⟶ truthVal))

  -- A Q constant with one argument applied.
  -- This could be done with app but it means we can't pattern match on the lamAbs syntax for the first argument of app, so just making a separate constructor for it.
  | equalsPartial (equalsTerm: Term ctx TermSyntax.equals (equalsFirstArg ⟶ equalsPartiallyAppliedType)) (term1: Term ctx syn1 equalsFirstArg)  : Term ctx TermSyntax.equalsPartial equalsPartiallyAppliedType
open Term



def Term.varName (x: Term ctx TermSyntax.var sType ):=
match x with
| var ctx index => (ctx.toList.get index).name

def Term.toContext (_: Term ctx syn sType) := ctx
def Term.toType  (_: Term ctx syn sType) := sType

def Term.toString (t: Term ctx syn sType)(inner: Bool := false) :=
let ctxStr := if inner then "" else ctx.toString
let wrap := fun (x:String) => ctxStr ++ if  inner then "("++ x ++ ")" else x
  match t with
    | var ctx index => wrap ((ctx.toList.get index).name  ++ ":" ++ sType.toString)
    | lamAbs body => wrap ( "λ(" ++ (body.toContext.head (by rfl)).toString ++ ")."  ++ (body.toString true) )
    | app f arg => wrap (f.toString true ++ arg.toString true )
    | equals _ side => wrap ( "Q:" ++  (side ⟶ (side ⟶ truthVal)).toString )
    | equalsPartial _ term1 => wrap ( "Q:" ++  (term1.toType ⟶ (term1.toType ⟶ truthVal)).toString ++ (term1.toString true) )


def testVar  := var testCtx ⟨ 2, by decide⟩
#eval testVar.toString

def testLambda := lamAbs testVar
#eval testLambda.toString

-- def testApp := app testLambda testVar
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
