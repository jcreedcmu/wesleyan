module 2018-08-20 where

open import HoTT hiding (Path ; Square)

Square : Set → Set
Square A = A × A

module Cats where
  -- We can do some n-category-like cells

  postulate
    Obj : Set

  Shape1 : Set
  Shape1 = Obj × Obj

  postulate
    Cell1 Path1 : Shape1 → Set
    η1 : {σ : Shape1} → Cell1 σ → Path1 σ
    id1 : (x : Obj) → Path1 (x , x)
    comp1 : {x y z : Obj} → Path1 (x , y) → Path1 (y , z) → Path1 (x , z)

  Shape2 : Shape1 → Set
  Shape2 σ = Path1 σ × Path1 σ

  postulate
    Cell2 Path2 : {σ1 : Shape1} (σ2 : Shape2 σ1) → Set
    η2 : {σ1 : Shape1} (σ2 : Shape2 σ1) → Path2 σ2
    id2 : {σ1 : Shape1} (x : Path1 σ1) → Path2 (x , x)
    comp2,2 : {c d : Obj} {x y z : Path1 (c , d)} → Path2 (x , y) → Path2 (y , z) → Path2 (x , z)
    comp2,1 : {c d e : Obj} {x1 x2 : Path1 (c , d)} {y1 y2 : Path1 (d , e)}
      (α : Path2 (x1 , x2)) (β : Path2 (y1 , y2)) → Path2 (comp1 x1 y1 , comp1 x2 y2)

  Prefix : ℕ → Set

  -- wrapping them up like so

  postulate
    Path : (n : ℕ) → Prefix n → Set

  Prefix O = Unit
  Prefix (S n) = Σ (Prefix n) (λ x → Square (Path n x))


module Rels where
  -- or we can think about not just two-ended things

  -- a dependent list of cells
  data Shape : Set
  data Red : Shape → Shape → Set

  postulate
    Cell : Shape → Set

  data Shape where
    nil : Shape
    cons : (σ σ' : Shape) → Red σ σ' → Cell σ' → Shape

  -- we don't have to use all the things in the shape up till now to
  -- index later things in the shape
  data Red where
    rnil : Red nil nil
    ryes : {σ σ' σ'' : Shape} (ρ : Red σ σ'') (ρ' : Red σ' σ'') (k : Cell σ'')
      → Red σ σ' → Red (cons σ σ'' ρ k) (cons σ' σ'' ρ' k)
    rno : {σ σ' σ'' : Shape} (ρ : Red σ σ'')                    (k : Cell σ'')
      → Red σ σ' → Red (cons σ σ'' ρ k) σ'

  Obj : Set
  Obj = Cell nil

  MorShape : Obj → Obj → Shape
  MorShape x y = cons (cons nil nil rnil x) nil (rno rnil x rnil) y
