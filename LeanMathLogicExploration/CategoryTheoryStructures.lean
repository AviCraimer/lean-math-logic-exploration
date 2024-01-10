-- import Mathlib.Tactic
-- set_option pp.coercions false
-- set_option autoImplicit false

import Mathlib.Combinatorics.Quiver.Basic

#check Quiver

structure Category where
  Obj: Type*
  Hom (A: Obj) (B: Obj): Type*
  id_morph (X:Obj) : Hom X X
  comp {A B C : Obj} (f: Hom A B) (g: Hom B C) : Hom A C

  -- Laws
  unit_right (f: Hom A B) : comp f (id_morph B) = f
  unit_left (f: Hom A B) : comp (id_morph A) f = f
  comp_assoc {A B C D: Obj}(f: Hom A B)(g: Hom B C)(h: Hom C D) : comp f (comp g h) = comp (comp f g) h

-- This doesn't work because comp takes the category as an implicit argument and when parsing it includes that argument as the left list of the infix operation.

-- namespace Category
-- scoped infixr:80 " ≫ " => Category.comp
-- end Category
open Category

/-
Ternary notation. The `C` argument can be ommited (as in the category theory development in Mathlib)
if `Obj` is a parameter of the structure `Category`
-/
notation f " ≫[" C "] " g => Category.comp C f g

-- Some API

-- Telling the simplifier what to do
-- Using @[simp] will change what the simp tactic does.
-- In this case we are saying to always simplify compositions with identity
@[simp]
lemma comp_id_right {C : Category} {A B : C.Obj} (f : C.Hom A B) : C.comp f (C.id_morph B) = f := C.unit_right _

@[simp]
lemma comp_id_left {C : Category} {A B : C.Obj} (f : C.Hom A B) : C.comp (C.id_morph A) f = f := C.unit_left _


def TypeCat : Category where
  Obj := Type
  Hom A B := A → B
  id_morph _ := λ x => x
  comp f g x := g (f x)
  unit_right _ := rfl
  unit_left _ := rfl
  comp_assoc _ _ _ := rfl


structure CatFunctor (Dom Cod: Category) :=
  objMap (A: Dom.Obj): Cod.Obj

  funcMap {A B: Dom.Obj} (f: Dom.Hom A B) : Cod.Hom (objMap A) (objMap B)

  -- The id morphism of each object in C is sent by fMap to the id morphism in Category D
  func_map_id : ∀ (A : Dom.Obj),
    let idA := Dom.id_morph A
    let FA := objMap A
    funcMap idA = Cod.id_morph FA

  func_map_comp {A B C: Dom.Obj} (f : Dom.Hom A B) (g : Dom.Hom B C) : funcMap (Dom.comp f g) = Cod.comp (funcMap f) (funcMap g)

open CatFunctor

structure NatTrans (F G: CatFunctor C D) :=
  component (X : C.Obj) :
    D.Hom (F.objMap X) (G.objMap X)

  naturality : (f: C.Hom X Y) ->
      let Ff := F.funcMap f
      let Gf := G.funcMap f
      let α_X := component X
      let α_Y := component Y
      D.comp Ff α_Y = D.comp α_X Gf
open NatTrans

def horizontalCompNT  {F G H: CatFunctor C D} (α :  NatTrans F G)(β : NatTrans G H) : NatTrans F H where
  component := fun (X:C.Obj) => D.comp (α.component X) (β.component X)
  naturality := by
    intro X Y f_xy
    dsimp
    -- rw? is a tactic that askes what I can re-write with things available
    -- Put cursoe on the r
    -- rw?
    rw [Category.comp_assoc]
    rw [α.naturality, ← Category.comp_assoc, β.naturality ]
    rw [comp_assoc]
    done

lemma horizontalCompNT.assoc {F G H K: CatFunctor C D} (α :  NatTrans F G)(β : NatTrans G H)(γ: NatTrans H K ) : horizontalCompNT α (horizontalCompNT β γ) = horizontalCompNT (horizontalCompNT  α β) γ := by
  unfold horizontalCompNT
  simp
  -- Using function extensionality axiom to remove outer function
  ext X
  exact comp_assoc D (component α X) (component β X) (component γ X)




-- Code actions
--- Put an underscore to serve as a hole to fill in.
--- ctrl + . -- Gives the auto complete

def identityNatTrans (F: CatFunctor C D) : NatTrans F F where
  component X := D.id_morph (F.objMap X)
  -- The simp tactic only worked after we defined the custom simplication rules above.
  naturality f := by simp


def FunctorCat (C D: Category) : Category where
  Obj := CatFunctor C D
  Hom := fun (A B: CatFunctor C D) => NatTrans A B
  id_morph := fun (F: CatFunctor C D) => identityNatTrans F
    -- I've got to define the identity natrual transformation.
  comp := horizontalCompNT -- {A B C: CatFunctor C D} => fun (f: NatTrans A B) => fun (g: NatTrans B C )
  unit_right := by
    -- dsimp
    -- unfold replaces an identifier with the definition of the identifier
    unfold identityNatTrans horizontalCompNT
    simp

    -- rw [(h:horizontalCompNT = comp]
  unit_left := by
    unfold identityNatTrans horizontalCompNT
    simp
  comp_assoc := horizontalCompNT.assoc



/-
-- General Solving Tactics
  - apply?
  - exact?
  - rw?
-/

inductive GraphDiagram.Obj where
 | E
 | V
 deriving DecidableEq


inductive GraphDiagram.Morph : (Dom  Cod : Obj) -> Type where
 | src :  Morph .E .V
 | trg :  Morph .E .V
 | id_E : Morph .E .E
 | id_V : Morph .V .V
deriving DecidableEq

def GraphDiagram.Morph.comp (f: Morph A B)(g: Morph B C): Morph A C   :=
  match A, B, C, f, g with
    | .E, .V, .V,  .src, .id_V => .src
    | .E, .V, .V, .trg, .id_V => .trg
    | .E, .E, .V, .id_E, .src => .src
    | .E, .E, .V, .id_E, .trg => .trg
    | .V, .V, .V, .id_V, .id_V => .id_V
    | .E, .E, .E, .id_E, .id_E => .id_E

-- # Diagram Category for defining Grph
def GraphDiagramCat : Category where
  Obj := GraphDiagram.Obj
  Hom := GraphDiagram.Morph

  id_morph X := match X with
    | .E => GraphDiagram.Morph.id_E
    | .V => GraphDiagram.Morph.id_V

  comp :=  GraphDiagram.Morph.comp

  unit_right := by
    intro A B f
    cases f <;> rfl

  unit_left := by
    intro A B f
    cases f <;> rfl

  comp_assoc := by
    intro A B C D f g h
    dsimp
    cases f <;> cases g <;> cases h <;> rfl

-- The category of graphs defined as the functor category from graph diagram to TypeCat (which is analogous to Set in category theory).
def Grph : Category := FunctorCat GraphDiagramCat TypeCat

abbrev Graph := Grph.Obj
#check  Quiver

#check (·≃·) -- \equ
abbrev Quiver0 := @Quiver Type

-- structure Equiv (α : Sort*) (β : Sort _) where
--   protected toFun : α → β
--   protected invFun : β → α
--   protected left_inv : LeftInverse invFun toFun
--   protected right_inv : RightInverse invFun toFun

-- class Quiver (V : Type u) where
--   /-- The type of edges/arrows/morphisms between a given source and target. -/
--   Hom : V → V → Sort v

class QuiverObj where
   Q : Type
   str : Quiver Q

def copairing (f: γ    -> α  ) (g: γ   -> β  ): γ -> (α × β ) := fun x  => ((f x), g x)
/--
We need to define `Hom : Type -> Type -> _`
Given v and u in Type; v and u are vertices in F(V)
-/
theorem equiv_graph_quiver :  Graph ≃ QuiverObj  where
  toFun g := {
    Q := g.objMap GraphDiagram.Obj.V
    str := {
      Hom := fun u v =>
        let src := g.funcMap  GraphDiagram.Morph.src
        let trg := g.funcMap  GraphDiagram.Morph.trg
        ({ e :  (g.objMap GraphDiagram.Obj.E) // src e = u ∧ trg e = v })
    }
  }
  invFun q := sorry
  left_inv := by sorry
  right_inv := by sorry

-- u, v should be elements of F(V), they are mapped to a subset of F(E)


-- #print CatFunctor
-- #check @id PUnit

-- The graph with one node and one self loop
def terminalGraph : Graph where
  objMap := fun _ => PUnit
  funcMap := fun
    | _ => @id PUnit
  func_map_id X := by cases X <;> rfl
  func_map_comp f g := by cases f <;> cases g <;> rfl



inductive M2.Obj where | M2Dot
open M2.Obj

inductive M2.Hom : (X:M2.Obj)  -> (Y:M2.Obj) -> Type   where
 | id : M2.Hom X X
 | src :  M2.Hom  X Y
 | trg : M2.Hom  X Y
 | complex (components: List (M2.Hom M2Dot M2Dot))  : M2.Hom  M2Dot M2Dot

def M2.Morph := M2.Hom M2Dot M2Dot

def xs : List ℕ := [1, 2, 4]
#eval   ([5,6]: List ℕ).append xs


def M2.comp  (f: M2.Morph) (g: M2.Morph)  :=
 match f, g with
 | _, .id => f
 | .id, _ => g
 | .complex listF, .complex listG => .complex (listF.append listG)
 | .complex listF, _ => .complex (listF.append [g])
 | _, .complex listG => .complex  ([f].append listG)
 | _, _ => .complex [f, g]

@[simp]
lemma M2.comp_id_right  (f : M2.Morph ) : M2.comp f M2.Hom.id = f := by cases f <;>  rfl

@[simp]
lemma M2.comp_id_left  (f : M2.Morph ) : M2.comp M2.Hom.id f = f := by cases f <;>  rfl

@[simp]
lemma M2.complex_complex : (comp (Hom.complex listF) (Hom.complex listG)) = (Hom.complex (listF.append listG)) :=  by rfl

@[simp]
lemma M2.complex_trg : (comp (Hom.complex listF) (Hom.trg)) = (Hom.complex $ (listF.append [Hom.trg])) :=  by rfl

@[simp]
lemma M2.complex_src : (comp (Hom.complex listF) (Hom.src)) = (Hom.complex $ (listF.append [Hom.src])) :=  by rfl

@[simp]
lemma M2.trg_complex : (comp (Hom.trg) (Hom.complex listG)) = (Hom.complex $ [Hom.trg].append listG) :=  by rfl

@[simp]
lemma M2.src_complex : (comp (Hom.src) (Hom.complex listG)) = (Hom.complex $ [Hom.src].append  listG) :=  by rfl

@[simp]
lemma M2.src_src_complex : (comp Hom.src Hom.src) = (Hom.complex [Hom.src, Hom.src]) :=  by rfl

@[simp]
lemma M2.trg_trg_complex : (comp Hom.trg Hom.trg) = (Hom.complex [Hom.trg, Hom.trg]) :=  by rfl

@[simp]
lemma M2.trg_src_complex : (comp Hom.trg Hom.src) = (Hom.complex [Hom.trg, Hom.src]) :=  by rfl

@[simp]
lemma M2.src_trg_complex : (comp Hom.src Hom.trg) = (Hom.complex [Hom.src, Hom.trg]) :=  by rfl




-- lemma M2.comp_complex_assoc : comp (Hom.complex listF) (comp (Hom.complex listG) (Hom.complex listH)) = comp (comp (Hom.complex listF) (Hom.complex listG)) (Hom.complex listH) := by
--   have h1: comp (Hom.complex listF) (comp (Hom.complex listG) (Hom.complex listH)) = Hom.complex  (listF.append (listG.append listH)) := by rfl
--   have h2: comp (comp (Hom.complex listF) (Hom.complex listG)) (Hom.complex listH) = Hom.complex  ((listF.append listG).append listH) := by rfl
--   have h3 : (listF.append (listG.append listH)) =  ((listF.append listG).append listH) := by simp
--   rw [h1, h2, h3]

def AutographDiagramCat : Category where
  Obj := M2.Obj
  Hom := M2.Hom

  id_morph X := M2.Hom.id

  comp := M2.comp

  unit_right := by
    intro A B f
    cases f <;> rfl

  unit_left := by
    intro A B f
    cases f <;> rfl

  comp_assoc := by
    dsimp
    intro A B C D f g h
    cases A ; cases B ; cases C ; cases D ;
    cases f <;> cases g <;> cases h <;> try simp

def AutoG : Category := FunctorCat AutographDiagramCat TypeCat






---
-- structure Arrow  (ObjName: Set String) :  Type :=
--   name: String
--   dom: ObjName
--   cod: ObjName
-- deriving Repr, DecidableEq, BEq

-- inductive ComposablePath {ObjName: Set String} :  ObjName -> ObjName -> Type   :=
--  -- Paths of length zero still have domains and codomains assigned in the type
--  -- An empty path corresponds to an identity morphism so it must have the same domain and codomain
--  | emptyPath {obj: ObjName}  : ComposablePath obj obj
--  -- The codomain of the path matches the domain of the new arrow being added to form a new path
--  -- The new path has the codomain of the added arrow, this is the new endpoint of the path
--  | fullPath {codArrow domPath codPath  : ObjName}  (prev: ComposablePath domPath codPath)  (next: Arrow ObjName ) (h: next = Arrow.mk name codpath codArrow)  : ComposablePath domPath codArrow
-- open ComposablePath


-- def validateConstituents  {ObjName: Set String} {dom cod: ObjName} (path: ComposablePath dom cod  ) (possibleConstituents: Set (Arrow ObjName)) :=
--   match path with
--     | emptyPath => True
--     | fullPath prev next _ => if possibleConstituents next = True then False else (validateConstituents prev possibleConstituents)


-- -- Before applying composition equations
-- def FinitePaths {ObjName: Set String}  (Generators: Set (Arrow ObjName)) (dom cod: ObjName): Type := { path: ComposablePath dom cod // validateConstituents path Generators }

-- -- Theorem Empty path is always valid when dom and cod are the same.
-- -- FinitePaths.empty theorm


-- def mkObjName (ObjNames : Set String) (name: String) (h: name ∈ ObjNames )  : ObjNames := ⟨ name, h ⟩

-- -- Example of how to create instance of x ∈ mySet
-- #print Set.mem_insert

-- def GraphDiagramObj : Set String := {"E", "V"}
-- def mkGraphObj := mkObjName GraphDiagramObj
-- def EInSet := mkGraphObj "E" (Or.inl rfl)
-- def VInSet := mkGraphObj "V" (Or.inr rfl)

-- def GraphDiagramGenerators : Set (Arrow GraphDiagramObj) := {Arrow.mk "src" EInSet  VInSet, Arrow.mk "trg" EInSet  VInSet }

-- def GraphDiagramMorphs (dom cod: GraphDiagramObj) := FinitePaths GraphDiagramGenerators dom cod


-- def GraphDiagram : Category where
--  Obj := GraphDiagramObj
--  Hom := GraphDiagramMorphs
--  id_morph X := ⟨ emptyPath, emptyPath⟩
