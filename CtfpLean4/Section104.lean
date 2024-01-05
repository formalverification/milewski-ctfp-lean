-- 4 Kleisli Categories ---------------------------------------------------------
-- 4.1 The Writer Category ------------------------------------------------------
-- 4.2 Writer in Haskell --------------------------------------------------------
-- snippet 01
def Writer : Type → Type := λ a => a × String

-- snippet 02
namespace snippet02
  variable (a b : Type)
  #check a → Writer b
end snippet02

variable {a b c : Type}
-- snippet 03
def fish : (a → Writer b) → (b → Writer c) → (a → Writer c) :=
  λ f g x => let (y, s) := f x
             let (z, t) := g y
             (z, s ++ t)
infix:55 ">=>" => fish

-- snippet 04
def _return : a → Writer a := λ x => (x, "")
-- (prepending `_` to avoid name clash with Lean's `return`)

-- snippet 05
def upCase : String → Writer String := λ s => (s.toUpper, "upCase ")

def toWords : String → Writer (List String) :=
  λ s => (s.splitOn " ", "toWords ")

-- snippet 06
def process : String → Writer (List String) :=
  upCase >=> toWords

-- 4.3 Kleisli Categories -------------------------------------------------------
