-- 8 Functoriality --------------------------------------------------------------

import Mathlib.Control.Bifunctor

-- 8.1 Bifunctors
namespace snippets01thru04
  -- snippet 01
  class Bifunctor (f : Type → Type → Type) where
    bimap : (a → c) → (b → d) → f a b → f c d
    first : (a → c) → f a b → f c b := λ g => bimap g id
    second : (b → d) → f a b → f a d := λ g => bimap id g
  open Bifunctor
  axiom bimap_law : ∀ (f : Type → Type → Type) [Bifunctor f] {a b c d : Type}
    (g : a → c) (h : b → d) (x : f a b), (bimap g h x) = (first g (second h x))

-- 8.2 Product and Coproduct Bifunctors ----------------------------------------
  -- snippet 02
  instance : Bifunctor Prod where
    bimap := λ f g pr => (f pr.1, g pr.2)

    -- first := λ f pr => (f pr.1, pr.2)
    -- second := λ g pr => (pr.1, g pr.2)

  -- snippet 03
  -- bimap : (a → c) → (b → d) → a × b → c × d

  inductive Either (α β : Type u) where
    | inl (a : α) : Either α β
    | inr (b : β) : Either α β

  open Either
  -- snippet 04
  instance : Bifunctor Either where
    bimap := λ f g x => match x with
      | inl a => inl (f a)
      | inr b => inr (g b)
end snippets01thru04

-- 8.3 Functorial Algebraic Data Types ------------------------------------------
namespace snippet05
  inductive Identity (α : Type u) where
    | identity : α → Identity α
  open Identity

  class Functor (f : Type → Type) where
    fmap : (a → b) → f a → f b

  -- snippet 05
  instance : Functor Identity where
    fmap := λ f (identity a) => identity (f a)
end snippet05

namespace snippet06
  inductive Maybe a where
    | Nothing : Maybe a
    | Just : a → Maybe a
end snippet06

namespace snippet07
  inductive Either (α β : Type u) where
    | inl (a : α) : Either α β
    | inr (b : β) : Either α β
  inductive Const (α : Type u) (β : Type v) where
    | const : α → Const α β
  open snippet05
  -- snippet 07
  def Maybe a := Either (Const Unit a) (Identity a)
end snippet07

namespace snippet08thru12
  class Bifunctor (f : Type → Type → Type) where
    bimap : (a → c) → (b → d) → f a b → f c d
    first : (a → c) → f a b → f c b := λ g => bimap g id
    second : (b → d) → f a b → f a d := λ g => bimap id g
  class Functor (f : Type → Type) where
    fmap : (a → b) → f a → f b

  -- snippet 08
  def BiComp (_ : Bifunctor B)(_ : Functor F) (_ : Functor G) :=
    λ a b => B (F a) (G b)

  -- snippet 09
  instance (bf : Bifunctor B) (fu : Functor F) (gu : Functor G) :
    Bifunctor (BiComp bf fu gu) where
      bimap := λ f1 f2 x => bf.bimap (fu.fmap f1 ) (gu.fmap f2) x

  -- snippet 10
  -- x : BiComp bf fu gu a✝ b✝ ⊢ B (F a✝) (G b✝)

  variable
  -- snippet 11
    (f1 : a → a')
    (f2 : b → b')

  -- snippet 12
    (bimap : (fu a → fu a') → (gu b → gu b')
      → bf (fu a) (gu b) → bf (fu a') (gu b'))

end snippet08thru12

namespace snippet13and14
  class Functor (f : Type → Type) where
    fmap : (a → b) → f a → f b

  -- snippet 13
  inductive Tree (a : Type) : Type where
    | Leaf : (x : a) → Tree a
    | Node : Tree a → Tree a → Tree a

  open Tree

  -- snippet 14
  def mapTree : (a → b) → Tree a → Tree b := λ f x => match x with
    | (Leaf x) => Leaf (f x)
    | (Node l r) => Node (mapTree f l) (mapTree f r)
  instance : Functor Tree where fmap := mapTree

end snippet13and14

-- 8.5 The Writer Functor -------------------------------------------------------
namespace snippet15thru26
  class Functor (f : Type → Type) where
    fmap : (a → b) → f a → f b

  -- snippet 15
  def Writer (a : Type) : Type := a × String

  -- snippet 16
  def fish : (a → Writer b) → (b → Writer c) → (a → Writer c) :=
    λ m1 m2 x =>
      let (y, s1) := m1 x
      let (z, s2) := m2 y
      (z, s1 ++ s2)

  infixr:55 " >=> " => fish

  -- snippet 18
  def ret : a → Writer a := λ x => (x, "")
  -- (return is a keyword in Lean)

  instance : Functor Writer where
    -- snippet 19
    fmap := λ f => id >=> (λ x => ret (f x))

  variable (r : Type)

-- 8.6 Covariant and Contravariant Functors -------------------------------------
  -- snippet 20
  #check λ a => r → a

  -- snippet 21
  def Reader (r a : Type) := r → a

  -- snippet 22
  instance : Functor (Reader r) where
    fmap := λ f g => f ∘ g

  -- snippet 23
  def Op (r a : Type) : Type := a → r

  -- snippet 24
  -- fmap : (a → b) → (a → r) → (b → r)

  -- snippet 25
  class Contravariant (f : Type → Type) where
    contramap : (b → a) → f a → f b

  -- snippet 26
  instance : Contravariant (Op r) where
    -- (b → a) → Op r a → Op r b
    contramap := λ f g => g ∘ f

  -- snippet 27
  def flip : (a → b → c) → (b → a → c) :=
    λ f y x => f x y

  -- snippet 28
  -- contramap = flip (∘)
end snippet15thru26

-- 8.7 Profunctors --------------------------------------------------------------

namespace snippet29and30
  -- snippet 29
  class Profunctor (p : Type → Type → Type)  where
    dimap : (a → b) → (c → d) → p b c → p a d
    lmap : (a → b) → p b c → p a c := λ f => dimap f id
    rmap : (b → c) → p a b → p a c := λ g => dimap id g
  open Profunctor
  axiom profunctor_law : ∀ {a b c d} p [Profunctor p]
    (f : a → b) (g : c → d) (x : p b c), dimap f g x = lmap f (rmap g x)

  -- snippet 30
  instance : Profunctor (λ r a => r → a) where
    dimap := λ ab cd bc => cd ∘ bc ∘ ab
    lmap := λ f g => g ∘ f
    rmap := λ f g => f ∘ g

end snippet29and30
