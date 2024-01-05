-- 6 Simple Algebraic Data Types

-- 6.1 Product Types

-- snippet 01
def swap : a × b → b × a := λ ⟨x, y⟩ => ⟨y, x⟩

namespace snippet02thru08
  variable
    (a b c : Type)
  -- snippet 02
  #check (a × b) × c
  -- snippet 03
  #check a × (b × c)

  -- snippet 04
  def α : (a × b) × c → a × (b × c) :=
    λ ⟨⟨x, y⟩, z⟩ => ⟨x, ⟨y, z⟩⟩

  -- snippet 05
  def α_inv: a × (b × c) → (a × b) × c :=
    λ ⟨x, ⟨y, z⟩⟩ => ⟨⟨x, y⟩, z⟩

  -- snippet 06
  #check a × Unit

  -- snippet 07
  def ρ : a × Unit → a := λ ⟨x, ()⟩ => x

  -- snippet 08
  def ρ_inv : a → a × Unit := λ x => ⟨x, ()⟩
end snippet02thru08

namespace snippet09and10
  -- snippet 09
  inductive Pair (a b : Type) : Type where
    | P : a → b → Pair a b

  open Pair

  -- snippet 10
  def stmt : Pair String Bool := P "This statement is" false
end snippet09and10

-- snippet 11
inductive Pair (a b : Type) : Type where
  | Pair : a → b → Pair a b

-- snippet 12
def stmt := (λ x y => (x , y)) "This statement is" false

-- or:  def stmt := ("This statement is" , false)

-- snippet 13
inductive Stmt : Type where
  | stmt : String → Bool → Stmt

namespace snippet14
  def starsWithSymbol : String × String × Int → Bool :=
    λ ⟨s, t, _⟩ => t.isPrefixOf s
end snippet14

-- 6.2 Records (Structures)

-- snippet 15
structure Element where
  name : String
  symbol : String
  atomicNumber : Int

open Element

-- snippet 16
def tupleToElem : String × String × Int → Element :=
  λ ⟨name, symbol, atomicNumber⟩ => ⟨name, symbol, atomicNumber⟩

-- snippet 17
def elemToTuple : Element → String × String × Int :=
  λ ⟨name, symbol, atomicNumber⟩ => ⟨name, symbol, atomicNumber⟩

-- snippet 18
#check atomicNumber
-- Element.atomicNumber (self : Element) : Int

namespace snippet19
-- snippet 19
def startsWithSymbol : Element → Bool :=
  λ e => e.symbol.isPrefixOf e.name
end snippet19

-- snippet20
infix:50 "isPrefixOf" => String.isPrefixOf
def startsWithSymbol' : Element → Bool :=
  λ e => e.symbol isPrefixOf e.name

-- 6.3 Sum Types

-- snippet 21
inductive Either (a b : Type) : Type where
  | Left  : a → Either a b
  | Right : b → Either a b

-- snippet 22
inductive OneOfThree (a b c : Type) : Type where
  | Sinistral : a → OneOfThree a b c
  | Medial    : b → OneOfThree a b c
  | Dextral   : c → OneOfThree a b c

-- snippet 23
variable (a : Type)
#check Either a Empty

-- snippet 24
inductive Color : Type where
  | Red   : Color
  | Green : Color
  | Blue  : Color

namespace snippet25
  -- snippet 25
  inductive Bool : Type where
    | True  : Bool
    | False : Bool
end snippet25

-- snippet 26
inductive Maybe (a : Type) : Type where
  | Nothing : Maybe a
  | Just    : a → Maybe a

-- snippet 27
inductive NothingType : Type where
  | Nothing : NothingType

-- snippet 28
inductive JustType (a : Type) : Type where
  | Just : a → JustType a

namespace snippet29
  def Maybe (a : Type) : Type := Either Unit a
end snippet29

namespace snippet30and31
  -- snippet 30
  inductive List (a : Type) : Type where
    | Nil  : List a
    | Cons : a → List a → List a

  open List Maybe
  -- snippet 31
  def maybeTail (l : List a) : Maybe (List a) := match l with
    | Nil => Nothing
    | Cons _ xs => Just xs
end snippet30and31

-- 6.4 Algebra of Types

variable (a b c : Type)
-- snippet 32
#check a × Either b c

-- snippet 33
#check Either (a × b) (a × c)

open Either

-- snippet 34
def prodToSum : a × Either b c → Either (a × b) (a × c) :=
  λ ⟨x, e⟩ => match e with
    | Left y  => Left  (x, y)
    | Right z => Right (x, z)

-- snippet 35
def sumToProd : Either (a × b) (a × c) → a × Either b c :=
  λ e => match e with
    | Left  ⟨x, y⟩ => ⟨x, Left  y⟩
    | Right ⟨x, z⟩ => ⟨x, Right z⟩

-- snippet 36
def prod1 : Int × Either String Float := (2, Left "Hi!")

namespace snippet37
  inductive List (a : Type) : Type where
    | Nil  : List a
    | Cons : a → List a → List a
end snippet37
