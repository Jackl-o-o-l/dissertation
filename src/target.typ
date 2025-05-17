#import "@preview/color-my-agda:0.1.0": init-color-my-agda
#show: init-color-my-agda

    ```agda
module target where

-- Operator precedence and associativity
infix 4 _≤ₛ_
infixl 6 _–ₛ_

open import lib

-- Stack descriptor: (frames, displacement)
record SD : Set where
    constructor ⟨_,_⟩
    field f d : ℕ

-- Stack descriptor operations    
_+ₛ_ : SD → ℕ → SD
⟨ f , d ⟩ +ₛ n = ⟨ f , d + n ⟩

-- _∸ₛ_ : SD → ℕ → SD
-- ⟨ f , d ⟩ ∸ₛ n = ⟨ f , d ∸ n ⟩

-- _-ₛ_ : (sd : SD) → (n : ℕ) → n ≤ SD.d sd → SD
-- (⟨ S_f , S_d ⟩ -ₛ n) p = ⟨ S_f , (S_d - n) p ⟩

_–ₛ_ : (sd : SD) → (n : ℕ) → (n≤d : n ≤ SD.d sd) → SD
(⟨ f , d ⟩ –ₛ n) n≤d = ⟨ f , (d – n) n≤d ⟩

–ₛ≡ : ∀ {f d d′ n} → {n≤d′ : n ≤ d′} → (d′ – n) n≤d′ ≡ d 
        → ⟨ f , d ⟩ ≡ (⟨ f , d′ ⟩ –ₛ n) n≤d′
–ₛ≡ p rewrite p = refl


-- Stack descriptor lexicographic ordering
data _≤ₛ_ : SD → SD → Set where
    <-f : ∀ {f f′ d d′} → f < f′ → ⟨ f , d ⟩ ≤ₛ ⟨ f′ , d′ ⟩
    ≤-d : ∀ {f d d′} → d ≤ d′ → ⟨ f , d ⟩ ≤ₛ ⟨ f , d′ ⟩

≤ₛ-refl : ∀{sd : SD} → sd ≤ₛ sd
≤ₛ-refl {⟨ f , d ⟩} = ≤-d ≤-refl

≤ₛ-trans : ∀{sd sd′ sd″ : SD} → sd ≤ₛ sd′ → sd′ ≤ₛ sd″ → sd ≤ₛ sd″
≤ₛ-trans (<-f f<f′) (≤-d _) =  <-f f<f′
≤ₛ-trans (<-f f<f′) (<-f f′<f″) = <-f (<-trans f<f′ f′<f″)
≤ₛ-trans (≤-d _) (<-f f′<f″) = <-f f′<f″
≤ₛ-trans (≤-d d≤d′) (≤-d d′≤d″) = ≤-d (≤-trans d≤d′ d′≤d″)

+ₛ→≤ₛ : ∀{sd : SD} → ∀{n : ℕ} → sd ≤ₛ sd +ₛ n
+ₛ→≤ₛ = ≤-d +→≤ 

sub-sd≤ₛ : ∀ {sd sd′ sd″} → sd′ ≡ sd″ → sd ≤ₛ sd′ → sd ≤ₛ sd″
sub-sd≤ₛ sd′≡sd″ sd≤ₛsd′ rewrite sd′≡sd″ = sd≤ₛsd′

-- Operator
data UnaryOp : Set where 
    UNeg : UnaryOp

data BinaryOp : Set where
    BPlus BMinus BTimes : BinaryOp

data RelOp : Set where
    RLeq RLt : RelOp

-- Nonterminals
-- Lefthand sides
data L (sd : SD) : Set where
    l-var : (sdᵛ : SD) → sdᵛ ≤ₛ sd → L sd
    l-sbrs : L sd

-- Simple righthand sides
data S (sd : SD) : Set where
    s-l : L sd → S sd
    s-lit : ℤ → S sd

-- Righthand sides
data R (sd : SD) : Set where
    r-s : S sd → R sd
    r-unary : UnaryOp → S sd → R sd
    r-binary : S sd → BinaryOp → S sd → R sd

-- Instruction sequences
data I (sd : SD) : Set where
    stop : I sd
    assign-inc : (δ : ℕ) → L (sd +ₛ δ) → R sd → I (sd +ₛ δ) → I sd
    assign-dec : (δ : ℕ) → (δ≤d : δ ≤ SD.d sd) → L ((sd –ₛ δ) δ≤d) 
                    → R sd → I ((sd –ₛ δ) δ≤d) → I sd
    if-then-else-inc : (δ : ℕ) → S sd → RelOp → S sd 
                            → I (sd +ₛ δ) → I (sd +ₛ δ) → I sd
    if-then-else-dec : (δ : ℕ) → (δ≤d : δ ≤ SD.d sd) 
                            → S sd → RelOp → S sd 
                            → I ((sd –ₛ δ) δ≤d) 
                            → I ((sd –ₛ δ) δ≤d) → I sd
    adjustdisp-inc : (δ : ℕ) → I (sd +ₛ δ) → I sd
    adjustdisp-dec : (δ : ℕ) → (δ≤d : δ ≤ SD.d sd) 
                        → I ((sd –ₛ δ) δ≤d) → I sd
    popto : (sd′ : SD) → sd′ ≤ₛ sd → I sd′ → I sd 


I-sub : ∀ {f d d′ n} → {n≤d′ : n ≤ d′} → (d′ – n) n≤d′ ≡ d 
            → I (⟨ f , d ⟩) → I ((⟨ f , d′ ⟩ –ₛ n) n≤d′)
I-sub {n = n} d′–n≡d c = sub I (–ₛ≡ {n = n} d′–n≡d) c
```
