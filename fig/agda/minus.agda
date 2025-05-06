infix 6 _∸_
infix 4 _≡_

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

_∸_ : ℕ → ℕ → ℕ
n ∸ zero = n
zero ∸ suc m = zero
suc n ∸ suc m = n ∸ m
{-# BUILTIN NATMINUS _∸_ #-}

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

0∸1≡0 : 0 ∸ 1 ≡ 0
0∸1≡0 = refl