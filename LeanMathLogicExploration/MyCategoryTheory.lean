import MathLib.Tactic
set_option pp.coercions false

class Category where
  Obj: Type*
  Hom (A: Obj) (B: Obj): Type*
  id (X:Obj) : Hom X X
  comp {A B C : Obj} (f: Hom A B) (g: Hom B C) : Hom A C

  -- Laws
  unit_right (f: Hom A B) : comp f (id B) = f
  unit_left (f: Hom A B) : comp (id A) f = f
  comp_assoc {A B C D: Obj}(f: Hom A B)(g: Hom B C)(h: Hom C D) : comp f (comp g h) = comp (comp f g) h

-- Is there a difference between using instance and using def in this context?
instance TypeCat : Category where
  Obj := Type
  Hom A B := A → B
  id _ := λ x => x
  comp f g x := g (f x)
  unit_right _ := rfl
  unit_left _ := rfl
  comp_assoc _ _ _ := rfl




instance GraphDiagramCat : Category where
  Obj := ({"E", "V"}: Set String)

  Hom A  :=
    let E : Set.Elem {"E", "V"} := ⟨ "E", by simp⟩
    let V : Set.Elem {"E", "V"} := ⟨ "V", by simp⟩
    match A with
    -- How do I make the function polymorphic in it's return type? Do i need to explictly define the type using a function returning Type as a function of the inputs.
      | E => fun B => match B with
        | V => ({"src", "trg"}: Set String)
        | E => ({"id_E"}: Set String)
      | V => fun B => match B with
        | V => {"id_V"}
        | E => {}

  id x := match x with
    | ⟨ "V", by simp⟩  => "id_V"
    | ⟨ "E", by simp⟩ => "id_E"
  comp f g :=
    match f, g with
    | "src", "id_V" => "src"
    | "trg", "id_V" => "trg"
    | "id_V", "id_V" => "id_V"
    | "id_E", "id_E" => "id_E"

  unit_right f := by rfl
  unit_left f := by rfl
  comp_assoc := by rfl




class CatFunctor (Dom Cod: Category) :=
  objMap (A: Dom.Obj): Cod.Obj

  funcMap {A B: Dom.Obj} (f: Dom.Hom A B) : Cod.Hom (objMap A) (objMap B)

  -- The id morphism of each object in C is sent by fMap to the id morphism in Category D
  func_map_id : ∀ (A : Dom.Obj),
    let idA := Dom.id A
    let FA := objMap A
    funcMap idA = Cod.id FA

  func_map_comp {A B C: Dom.Obj} (f : Dom.Hom A B) (g : Dom.Hom B C) : funcMap (Dom.comp f g) = Cod.comp (funcMap f) (funcMap g)


class NatTrans (F G: CatFunctor C D) :=
  component (X : C.Obj) :
    D.Hom (F.objMap X) (G.objMap X)

  naturality : (f: C.Hom X Y) ->
      let Ff := F.funcMap f
      let Gf := G.funcMap f
      let α_X := component X
      let α_Y := component Y
      D.comp Ff α_Y = D.comp α_X Gf

def identityNatTrans (F: CatFunctor C D) : NatTrans F F where
  component X := D.id (F.objMap X)
  naturality f := sorry


def FunctorCat (C D: Category) : Category where
  Obj := CatFunctor C D
  Hom := fun (A B: CatFunctor C D) => NatTrans A B
  id := fun (F: CatFunctor C D) => identityNatTrans F
    -- I've got to define the identity natrual transformation.
  comp  := sorry -- {A B C: CatFunctor C D} => fun (f: NatTrans A B) => fun (g: NatTrans B C )
  unit_right := sorry
  unit_left := sorry
  comp_assoc := sorry




-- # FINITELY PRESENTABLE CATEGORIES using explicit generators - work in progress


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
--  id X := ⟨ emptyPath, emptyPath⟩
