-- 7 Functors -------------------------------------------------------------------
import Mathlib.Data.Stream.Defs

-- 7.1 Functors in Programming --------------------------------------------------
-- snippet 01
inductive Maybe (a : Type) : Type where
  | Nothing : Maybe a
  | Just : a → Maybe a
open Maybe

namespace snippets02thru04
  variable
    -- snippet 02
    (f : a → b)

  -- snippet 03
  def f' : Maybe a → Maybe b := fun
    | Nothing => Nothing
    | Just x => Just (f x)

  variable
    -- snippet 04
    (fmap : (a → b) → (Maybe a → Maybe b))
end snippets02thru04

namespace snippets05thru09
  -- snippet 05
  def fmap : (a → b) → Maybe a → Maybe b :=
    -- snippet 06
    λ f ma => match ma with
      | Nothing => Nothing
      | Just x => Just (f x)

  -- snippet 07
  def id (a : Type) : a → a := λ x => x

  -- snippet 08
  example : (∀ x : Maybe a, fmap (id a) x = id (Maybe a) x) := λ x => match x with
    | Nothing => rfl
    | Just _ => rfl

  example : fmap (id a) Nothing = id (Maybe a) Nothing := rfl

  example : fmap (id a) (Just x) = id (Maybe a) (Just x) := rfl

  variable (f : a → b)(g : b → c)
  -- snippet 09
  example : (∀ x : Maybe a, fmap (g ∘ f) x = (fmap g ∘ fmap f)  x) :=
    λ x => match x with
      | Nothing => rfl
      | Just _ => rfl

end snippets05thru09

-- Type classes

namespace snippet10
  -- snippet 10
  class Eq (a : Type) where
    eq : a → a → Bool

  open Eq
  infix:50 "==" => eq

  -- snippet 11
  inductive Point : Type where
    | Pt : Float → Float → Point

  open Point

  -- snippet 12
  instance : Eq Point where
    eq := λ (Pt x y) (Pt x' y') => x == x' && y == y'

end snippet10

namespace snippet13thru18
  -- snippet 13
  class Functor (f : Type → Type) where
    fmap : (a → b) → f a → f b

  -- snippet 14
  instance : Functor Maybe where
    fmap := λ f ma => match ma with
      | Nothing => Nothing
      | Just x => Just (f x)

  -- snippet 15
  inductive List (a : Type) : Type where
    | Nil : List a
    | Cons : a → List a → List a
  open List

  -- snippet 16
  def fmap : (a → b) → List a → List b :=
  -- snippet 17
    λ f la => match la with
      | Nil => Nil
      | Cons x xs => Cons (f x) (fmap f xs)

  -- snippet 18
  instance : Functor List where
    fmap := λ f la => match la with
      | Nil => Nil
      | Cons x xs => Cons (f x) (fmap f xs)
end snippet13thru18

namespace snippet19thru24
  class Functor (f : Type → Type) where
    fmap : (a → b) → f a → f b
  variable
    (a b f : Type)
  def arrow : Type → Type → Type := λ a b => a → b

  prefix:10 "->" => arrow

  -- snippet 19
  #check (-> a) b

  -- snippet 20
  #check -> a

  -- snippet 21
  def fmap : (a → b) → (r → a) → (r → b) :=
    λ f g => f ∘ g

  -- snippet 22
  instance : Functor (-> a) where
    fmap := λ f g => f ∘ g

  prefix:10 " ∘ " => Function.comp

  -- snippet 23
  instance : Functor (-> a) where
    fmap := λ f g => (∘ f) g

  -- snippet 24
  instance : Functor (-> a) where
    fmap := Function.comp
end snippet19thru24

-- 7.2 Functors as Containers ---------------------------------------------------
-- snippet 25
def nats := Stream'.iterate Nat.succ 0

namespace snippet25
  -- snippet 26
  inductive Const (c : Type)(a : Type) : Type where
    | const : c → Const c a

  open Const
  -- snippet 27
  def fmap : (a → b) → Const c a → Const c b :=
    λ _ (const c) => const c

  class Functor (f : Type → Type) where
    fmap : (a → b) → f a → f b

  -- snippet 28
  instance : Functor (Const c) where
    fmap := λ _ (const v) => const v
end snippet25

-- 7.3 Functor Composition ------------------------------------------------------
namespace snippets29thru31
  class Functor (f : Type → Type) where
    fmap : (a → b) → f a → f b
  open Functor

  instance : Functor Maybe where
    fmap := λ f ma => match ma with
      | Nothing => Nothing
      | Just x => Just (f x)

  instance : Functor List where
    fmap := λ f la => match la with
      | [] => []
      | x :: xs => (f x) :: (Functor.map f xs)

  -- snippet 29
  def maybeTail : List a → Maybe (List a) :=
    λ la => match la with
      | [] => Nothing
      | _ :: xs => Just xs

  -- snippet 30
  def square : Int → Int := λ x => x * x

  def mis : Maybe (List Int) := Just (1 :: 2 :: 3 :: [])

  def mis2 := fmap (fmap square) mis

  -- snippet 31
  def mis2' := (fmap ∘ fmap) square mis

end snippets29thru31

namespace snippets32thru35
  variable
    (f : Type → Type)
    -- snippet 32
    (fmap : (a → b) → (f a → f b))
    -- snippet 33
    (square : Int → Int)
    -- snippet 34
    (_ : List Int → List Int)
    -- snippet 35
    (_ : Maybe (List Int) → Maybe (List Int))
end snippets32thru35
