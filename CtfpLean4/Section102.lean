-- 2 Types and Functions --------------------------------------------------------

-- 2.1 Who Needs Types? ---------------------------------------------------------
-- 2.2 Types Are About Composability --------------------------------------------
-- 2.3 What Are Types? ----------------------------------------------------------

variable (x : Int)          -- snippet 01
-- snippet 02
namespace snippet02
  variable (f : Bool → Bool)
end snippet02

-- snippet 03
namespace snippet03
  def f : Bool → Bool := λ x => sorry
end snippet03

-- snippet 04
namespace snippet04
  def f : Bool → Bool := sorry
end snippet04

-- 2.4 Why Do We Need A Mathematical Model --------------------------------------
-- snippet 05
def fact (n : Nat) : Nat := match n with
  | 0   => 1
  | n+1 =>  (n + 1) * fact n

-- 2.5 Pure and Dirty Functions -------------------------------------------------
-- 2.6 Examples of Types --------------------------------------------------------
-- snippet 06
variable (a : Type)
variable (absurd : False → a)

-- snippet 07
def f44 : Empty → Int := λ _ => 44

-- snippet 08
def fInt : Int → Unit := λ _ => ()

namespace snippet09
  def fInt : Int → Unit := λ _ => ()
end snippet09

-- snippet 10
def unit : a → Unit := λ _ => ()

namespace snippet11
  inductive Bool : Type where
    | true
    | false
end snippet11
