-- 1 Category: The Essence of Composition ---------------------------------------
-- 1.1 Arrows as Functions ------------------------------------------------------
variable (A B C D : Type)
variable (f : A → B)   -- snippet 1
variable (g : B → C)   -- snippet 2
#check g ∘ f           -- snippet 3

-- 1.2 Properties of Composition -----------------------------------------------
-- snippet 4
example :
  ∀ {f : A → B}
    {g : B → C}
    {h : C → D},
    h ∘ (g ∘ f) = (h ∘ g) ∘ f := rfl

-- snippet 5
namespace snippet5
  def id : A → A := λ x => x
  #eval id Nat 10
end snippet5

-- snippet 6
example : f ∘ id = f := rfl
example : id ∘ f = f := rfl

-- 1.3 Composition is the Essence of Programming --------------------------------
