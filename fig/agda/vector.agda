data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : ∀{n : ℕ} (x : A) (xs : Vec A n) → Vec A (suc n)