-- 10 Natural Transformations ---------------------------------------------------

-- 10.1 Polymorphic Functions ---------------------------------------------------
namespace snippet01thru03
  variable (F : Type → Type) [Functor F]
  variable (G : Type → Type) [Functor G]
  variable (α : ∀ a, F a → G a)  -- snippet 01
  variable (α : F a → G a)       -- snippet 02
  variable (α : F a → G a)       -- snippet 03
end snippet01thru03

inductive Maybe (α : Type u) where
  | Nothing : Maybe α
  | Just : α → Maybe α
open Maybe

-- snippet 04
def safeHead {a} : List a → Maybe a :=
  λ xs => match xs with
    | [] => Nothing
    | (x :: _) => Just x

namespace snippet05thru15
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
  -- snippet 10
  def fmap (f : a → b)(l : List a) : List b := match l with
    | []      => []
    | (x::xs) => f x :: fmap f xs

  -- snippet 11
  def fmap' (f : a → b)(m : Maybe a) : Maybe b := match m with
    | Nothing => Nothing
    | Just x  => Just (f x)

  inductive Const (c : Type)(a : Type) : Type where
    | const : c → Const c a

  open Const

  instance : Functor (Const c) where
    fmap := λ _ (const v) => const v

  -- snippet 13
  def unConst : Const c a → c :=
    λ (const v) => v

  -- snippet 12
  def length : List a → Const Int a :=
    λ l => match l with
      | []      => const 0
      | (_::xs) => const (1 + unConst (length xs))

  -- snippet 14
  -- def length : List a → Int
  -- snippet 15
  def scam : Const Int a → Maybe a :=
    λ _ => Nothing

  -- snippet 16
  def Reader (e a : Type) := e → a

  -- snippet 17
  instance : Functor (Reader e) where
    fmap := λ f g => f ∘ g

  -- snippet 18
  -- def α : Reader Unit a → Maybe a

  -- snippet 19
  def dumb : Reader Unit a → Maybe a :=
    λ _ => Nothing

  -- snippet 20
  def obvious : Reader Unit a → Maybe a :=
    λ g => Just (g ())

  -- snippet 21
  def Op (r a : Type) : Type := a → r

  class Contravariant (f : Type → Type) where
    contramap : (b → a) → f a → f b

  open Contravariant
  -- snippet 22
  instance : Contravariant (Op r) where
    contramap := λ f g => g ∘ f

  -- snippet 23
  def predToStr : (Op Bool α) → (Op String α) :=
    λ f => (λ x => if f x then "T" else "F")

  -- snippet 24
  example : contramap f ∘ predToStr = predToStr ∘ contramap f := rfl

  -- snippet 25
  -- contramap : (b → a) → (Op Bool a → Op Bool b)

  -- snippet 26
  -- a → a

  -- snippet 27
  -- (a → a) → f a

end snippet05thru15
