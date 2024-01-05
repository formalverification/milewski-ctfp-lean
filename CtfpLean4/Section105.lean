-- 5 Products and Coproducts ----------------------------------------------------

-- 5.1 Initial Object -----------------------------------------------------------
-- snippet 01
variable (absurd : False → a)

-- 5.2 Terminal Object ----------------------------------------------------------
-- snippet 02
def unit : a → Unit := λ _ => ()

-- snippet 03
def yes : a → Bool := λ _ => true

-- snippet 04
def no : a → Bool := λ _ => false

-- 5.3 Duality ------------------------------------------------------------------
-- 5.4 Isomorphisms -------------------------------------------------------------
variable (f : a → b) (g : b → a)
-- snippet 05
#check f ∘ g = id
#check g ∘ f = id

-- 5.5 Products -----------------------------------------------------------------
-- snippet 06
def fst : a × b → a := λ (x, _) => x

-- snippet 07
def snd : a × b → b := λ (_, y) => y

-- snippet 08
-- λ (x, _) => x
-- λ (_, y) => y

namespace snippet09
  variable
    (p : c → a)
    (q : c → b)
end snippet09

namespace snippet10
  def p : Int → Int := λ x => x
  def q : Int → Bool := λ _ => true
end snippet10

namespace snippet11
  def p : Int × Int × Bool → Int := λ (x, _, _) => x
  def q : Int × Int × Bool → Bool := λ (_, _, b) => b
end snippet11

namespace snippet12
  variable
    (a b c c' : Type)
    (p : c → a)
    (q : c → b)
    (m : c' → c)
  -- snippet 12
  def p' := p ∘ m
  def q' := q ∘ m
end snippet12

-- snippet 13
namespace snippet13
  def m : Int → Int × Bool := λ x => (x, true)
  -- snippet 14
  def p := λ x => fst (m x)
  example : p = λ x => x := rfl
  def q := λ x => snd (m x)
  example : q = λ _ => true := rfl
end snippet13

namespace snippet15
  def m : Int × Int × Bool → Int × Bool := λ (x, _, b) => (x, b)
end snippet15

namespace snippet16
  variable
    (m' : Int × Bool → Int × Int × Bool)
    (p : Int × Int × Bool → Int)
    (q : Int × Int × Bool → Bool)
  -- snippet 16
  #check fst = p ∘ m'
  #check snd = q ∘ m'
end snippet16
namespace snippet17
  def m' : Int × Bool → Int × Int × Bool := λ (x, b) => (x, x, b)
end snippet17

namespace snippet18
  def m' : Int × Bool → Int × Int × Bool := λ (x, b) => (x, 42, b)
end snippet18

namespace snippet19
  variable (p : c → a) (q : c → b)
  -- snippet 19
  def m : c → a × b := λ x => (p x, q x)
end snippet19

namespace snippet20
  def factorizer : (c → a) → (c → b) → (c → a × b) :=
    λ p q x => (p x, q x)
end snippet20

-- 5.6 Coproduct ----------------------------------------------------------------
namespace snippet21
  variable
    -- snippet 21
    (i : a → c)
    (j : b → c)
end snippet21

namespace snippet22
  variable
    (i : a → c)(j : b → c)
    (m : c → c')
    -- snippet 22
    def i' := m ∘ i
    def j' := m ∘ j
end snippet22

-- snippet 23
inductive Contact : Type
  | PhoneNum : Int → Contact
  | EmailAddr : String → Contact

open Contact

-- snippet 24
def helpdesk : Contact := PhoneNum 2222222

-- snippet 25
inductive Either (a b : Type) : Type
  | Left : a → Either a b
  | Right : b → Either a b

open Either

-- snippet 26
def factorizer : (a → c) → (b → c) → Either a b → c :=
  λ i j x => match x with
    | Left a  => i a
    | Right b => j b

-- 5.7 Asymmetry ----------------------------------------------------------------
namespace snippet27
  variable
    (m : c → a × b )
    (p : c → a)
    (q : c → b)
  -- snippet 27
  #check p = fst ∘ m
  #check q = snd ∘ m
end snippet27

namespace snippet28
  variable
    (m : Unit → a × b )
    (p : Unit → a)
    (q : Unit → b)
  -- snippet 27
  #check p () = fst (m ())
  #check q () = snd (m ())
end snippet28
