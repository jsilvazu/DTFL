------------------------------------------------------------------------------
-- Dependently typed functional languages - CB0683/2011-01

-- Propositions-as-types principle
------------------------------------------------------------------------------
-- Author: John Jairo Silva  <jsilvazu@eafit.edu.co>
-----------------------------------------------------------------------------
-- (Tested with Agda 2.2.10.)
------------------------------------------------------------------------------
-- References:
-- [1] Dirk Dalen, Logic and structure. Springer. 2004.
-- [2] John O’Donnell, Cordelia Hall and Rex Page. Discrete Mathematics 
--      Using Computers. 2nd Edition. Springer. 2006.
------------------------------------------------------------------------------
module Homework1 where

open import PropositionsAsTypes

-- (¬ ∃x.Px → ∀x.¬Px )[1, p.155]
PP1 : {A : Set}{P : A → Set} →
    ¬ ∃ A P → ((x : A) →
    ( ¬ P x))
PP1 p d b = p (d , b)

-- (∀x.Fx ∨ ∀x.Gx) → ∀x.(Fx ∨ Gx) [2, p.183]
PP2 : {A : Set}{F G : A → Set} →
    (((x : A) → F x) ∨ ((x : A) → G x)) →
    ((x : A) → (F x ∨ G x))
PP2 (inj₂ g) a = inj₂ (g a)
PP2 (inj₁ f) a = inj₁ (f a)

-- ∃x(Px ∨ Qx) → (∃x.Px ∨ ∃x.Qx) [2, p.183]
PP3 : {A : Set}{P Q : A → Set} →
    ∃ A (\x → (P x ∨ Q x)) →
    (∃ A P ∨ ∃ A Q)
PP3 (p , inj₁ y) = inj₁ (p , y)
PP3 (p , inj₂ y) = inj₂ (p , y)
