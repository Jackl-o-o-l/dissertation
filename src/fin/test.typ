#import "@preview/color-my-agda:0.1.0": init-color-my-agda
#show: init-color-my-agda

    ```agda
module test where

open import lib
open import source
open import target
open import compiler

compile-closed : · ⊢ comm → I ⟨ 0 , 0 ⟩
compile-closed t = ⟦ t ⟧ ⟨ 0 , 0 ⟩ unit ≤ₛ-refl stop

-- term1 : · ⊢ comm
-- term1 = Plus (Lit (pos 1)) (Lit (pos 2))
-- result = compile-closed term1
```
