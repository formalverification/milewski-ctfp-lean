-- 10 Natural Transformations ---------------------------------------------------

-- 10.1 Polymorphic Functions ---------------------------------------------------
variable (F : Type → Type) [Functor F]
variable (G : Type → Type) [Functor G]
variable (α : ∀ a, F a → G a)  -- snippet 01
variable (α : F a → G a)       -- snippet 02
variable (α : F a → G a)       -- snippet 03

inductive Maybe (α : Type u) where
  | Nothing : Maybe α
  | Just : α → Maybe α
open Maybe

-- snippet 04
def safeHead {a} : List a → Maybe a :=
  λ xs => match xs with
    | [] => Nothing
    | (x :: _) => Just x

namespace snippet05thru09
  class Functor (F : Type → Type) where
    fmap : ∀ {a b}, (a → b) → F a → F b
  open Functor

  instance : Functor Maybe where
    fmap := λ f x => match x with
      | Nothing => Nothing
      | (Just x) => Just (f x)

  instance : Functor List where fmap := List.map

  example : ∀ (f : a → b) (l : List a),
    -- snippet 05
    (fmap f ∘ safeHead) l = (safeHead ∘ fmap f) l
      := λ _ l => match l with
        | []       => rfl
        -- snippet 06 (lhs)
        -- fmap f (safeHead []) = fmap f Nothing = Nothing
        -- snippet 07 (rhs)
        -- safeHead (fmap f []) = safeHead [] = Nothing
        | (_ :: _) => rfl
        -- snippet 08
        -- fmap f (safeHead (x :: xs)) = fmap f (Just x) = Just (f x)
        -- snippet 09
        -- safeHead (fmap f (x :: xs)) = safeHead (f x :: fmap f xs) = Just (f x)
end snippet05thru09

namespace snippet10
  -- snippet 10
  def fmap (f : a → b)(l : List a) : List b := match l with
    | []      => []
    | (x::xs) => f x :: fmap f xs
end snippet10

namespace snippet11
  -- snippet 11
  def fmap (f : a → b)(m : Maybe a) : Maybe b := match m with
    | Nothing => Nothing
    | Just x  => Just (f x)
end snippet11


namespace snippet12
  inductive Const (c : Type)(a : Type) : Type where
    | const : c → Const c a

  open Const

  class Functor (f : Type → Type) where
    fmap : (a → b) → f a → f b

  instance {c : Type} : Functor (Const c) where
    fmap := λ _ (const v) => const v

  -- snippet 12
  def length : List Nat → Const Nat a := λ l => match l with
    | []      => const 0
    | (_::xs) => const (Nat.succ (length xs))

end snippet12
