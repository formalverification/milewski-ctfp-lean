-- 9 Function Types -------------------------------------------------------------

variable (a b c : Type)

-- 9.2 Currying -----------------------------------------------------------------

-- snippet 01
#check a → (b → c)

-- snippet 02
#check a → b → c

-- snippet 03
def catstr : String → String → String :=
  λ s s' => s ++ s'

-- snippet 04
def catstr' (s : String) := λ s' => s ++ s'

-- snippet 05
def greet : String → String := catstr "Hello "

-- snippet 06
#check a × b → c

-- snippet 07
def curry : (a × b → c) → (a → b → c) :=
  λ f a b => f (a, b)

-- snippet 08
def uncurry : (a → b → c) → (a × b → c) :=
  λ f (a, b) => f a b

-- snippet 09
def factorizer : (a × b → c) → a → b → c :=
  λ g => λ a => λ b => g (a, b)

-- 9.3 Exponentials -------------------------------------------------------------

-- 9.4 Cartesian Closed Categories ----------------------------------------------

-- 9.5 Exponentials and Algebraic Data Types ------------------------------------
namespace snippet10
  inductive Either (a b : Type) : Type
    | left : a → Either a b
    | right : b → Either a b

  -- snippet 10
  def f : Either Int Float → String :=

  -- snippet 11
    λ x => match x with
      | Either.left n => if (n < 0) then "Negative int" else "Positive int"
      | Either.right x => if (x < 0.0) then "Negative float" else "Positive float"

end snippet10

-- 9.6 Curry-Howard Isomorphism ------------------------------------------------
-- snippet 12
-- def eval : (a → b) × a → b :=

-- snippet 13
def eval : (a → b) × a → b :=
  λ (f, x) => f x

-- snippet 14
-- Either a b → a

namespace snippet15
  -- snippet 15
  def absurd : False → a
    := λ x => False.elim x
end snippet15
