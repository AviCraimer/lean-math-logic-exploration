import  «LeanMathLogicExploration».RelationalAlgebra

open Relation

inductive Province :=
| Alta
| BC
| Sask
| On
| Qc

open Province

def adjacent : (Pairs Province Province) := fun (a b) => match a, b with
  | Alta, BC => True
  | BC, Alta => True
  | Alta, Sask => True
  | Sask, Alta => True
  | On, Qc => True
  | Qc, On => True
  | _, _ => False


inductive Colour :=
| red
| green
| blue

open Colour

-- Now I'd like to be able to define an expression without defining the actual relation for Dif.
