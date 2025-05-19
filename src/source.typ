#import "@preview/color-my-agda:0.1.0": init-color-my-agda
#show: init-color-my-agda

    ```agda
module source where

open import lib

-- Operator precedence and associativity
infix 1 _≤:_
infix 2 _⟶_ 
infix 4 _⊢_
infix 4 _∈_
infixl 5 _,_
infixr 7 _⇒_

-- Types
data Type : Set where
    comm intexp intacc intvar : Type
    _⇒_ : Type → Type → Type

-- Subtype relation
data _≤:_ : Type → Type → Set where
    ≤:-refl : ∀{A} → A ≤: A
    ≤:-trans : ∀{A A′ A″} → A ≤: A′ → A′ ≤: A″ → A ≤: A″
    ≤:-fn : ∀{A A′ B B′} → A′ ≤: A → B ≤: B′ → A ⇒ B ≤: A′ ⇒ B′

    var-≤:-exp : intvar ≤: intexp
    var-≤:-acc : intvar ≤: intacc

-- Contexts
data Context : Set where
    · : Context
    _,_ : Context → Type → Context

-- Variables and the lookup judgement
data _∈_ : Type → Context → Set where
    Zero : ∀{Γ A} → A ∈ Γ , A
    Suc : ∀{Γ A B} → B ∈ Γ → B ∈ Γ , A

-- Terms and the typing judgement
data _⊢_ : Context → Type → Set where
    Var : ∀{Γ A} → A ∈ Γ → Γ ⊢ A

    -- subtyping
    Sub : ∀{Γ A B} → Γ ⊢ A → A ≤: B → Γ ⊢ B

    -- lambda function and application
    Lambda : ∀{Γ A B} → Γ , A ⊢ B → Γ ⊢ A ⇒ B
    App : ∀{Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B

    -- command
    Skip : ∀{Γ} → Γ ⊢ comm
    Seq : ∀{Γ} → Γ ⊢ comm → Γ ⊢ comm → Γ ⊢ comm
    NewVar : ∀{Γ} → Γ , intvar ⊢ comm → Γ ⊢ comm
    Assign : ∀{Γ} → Γ ⊢ intacc → Γ ⊢ intexp → Γ ⊢ comm

    -- intexp
    Lit : ∀{Γ} → ℤ → Γ ⊢ intexp
    Neg : ∀{Γ} → Γ ⊢ intexp → Γ ⊢ intexp
    Plus : ∀{Γ} → Γ ⊢ intexp → Γ ⊢ intexp → Γ ⊢ intexp


-- Operational semantics
data Value : ∀{Γ A} → Γ ⊢ A → Set where
    V-Lambda : ∀{Γ A B} {F : Γ , A ⊢ B} → Value (Lambda {Γ} F)
    V-Lit : ∀{Γ} {i : ℤ} → Value (Lit {Γ} i)
    V-Skip : ∀{Γ} → Value (Skip {Γ})

-- Renaming
ext : ∀{Γ Δ} → (∀{A} → A ∈ Γ → A ∈ Δ)
             → (∀{A B} → B ∈ Γ , A → B ∈ Δ , A)
ext ρ Zero = Zero
ext ρ (Suc x) = Suc (ρ x)

rename : ∀{Γ Δ} → (∀{A} → A ∈ Γ → A ∈ Δ) 
                → (∀{A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (Var a) = Var (ρ a)
rename ρ (Lambda f) = Lambda (rename (ext ρ) f)
rename ρ (Sub a A≤:B) = Sub (rename ρ a) A≤:B
rename ρ (App f e) = App (rename ρ f) (rename ρ e)
rename ρ Skip = Skip
rename ρ (Seq c₁ c₂) = Seq (rename ρ c₁) (rename ρ c₂)
rename ρ (NewVar c) = NewVar (rename (ext ρ) c)
rename ρ (Assign a e) = Assign (rename ρ a) (rename ρ e)
rename ρ (Lit i) = Lit i
rename ρ (Neg e) = Neg (rename ρ e)
rename ρ (Plus e₁ e₂) = Plus (rename ρ e₁) (rename ρ e₂)

-- Simultaneous substitution
exts : ∀{Γ Δ} → (∀{A} → A ∈ Γ → Δ ⊢ A) 
              → (∀{A B} → B ∈ Γ , A → Δ , A ⊢ B)
exts σ Zero = Var Zero
exts σ (Suc x) = rename Suc (σ x)

subst : ∀{Γ Δ} → (∀{A} → A ∈ Γ → Δ ⊢ A)
               → (∀{A} → Γ ⊢ A → Δ ⊢ A)
subst σ (Var a) = σ a
subst σ (Sub a A≤:B) = Sub (subst σ a) A≤:B
subst σ (Lambda f) = Lambda (subst (exts σ) f)
subst σ (App f e) = App (subst σ f) (subst σ e)
subst σ Skip = Skip
subst σ (Seq c₁ c₂) = Seq (subst σ c₁) (subst σ c₂)
subst σ (NewVar c) = NewVar (subst (exts σ) c)
subst σ (Assign a e) = Assign (subst σ a) (subst σ e)
subst σ (Lit i) = Lit i
subst σ (Neg e) = Neg (subst σ e)
subst σ (Plus e₁ e₂) = Plus (subst σ e₁) (subst σ e₂)

-- Single substitution
_[_] : ∀{Γ A B} → Γ , B ⊢ A → Γ ⊢ B → Γ ⊢ A
_[_] {Γ} {A} {B} N M = subst {Γ , B} {Γ} σ {A} N
    where
    σ : ∀ {A} → A ∈ Γ , B → Γ ⊢ A
    σ Zero = M
    σ (Suc x) = Var x

-- Reduction
data _⟶_ : ∀{Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
    App-cong₁ : ∀{Γ A B} {F F′ : Γ ⊢ A ⇒ B} {E : Γ ⊢ A} 
                    → F ⟶ F′ → App F E ⟶ App F′ E
    App-cong₂ : ∀{Γ A B} {V : Γ ⊢ A ⇒ B} {E E′ : Γ ⊢ A} 
                    → Value V → E ⟶ E′ → App V E ⟶ App V E′
    Lambda-β : ∀{Γ A B} {F : Γ , A ⊢ B} {V : Γ ⊢ A}
                    → Value V → App (Lambda F) V ⟶ F [ V ]
```
