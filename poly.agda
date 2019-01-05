open import Algebra
open import Agda.Primitive
open import Data.Nat using (ℕ)
open import Data.List hiding (sum)

sum : {c ℓ : Level} {A : CommutativeRing c ℓ} → List (CommutativeRing.Carrier A) → CommutativeRing.Carrier A
sum {c} {ℓ} {A} [] = 0# where open CommutativeRing A
sum {c} {ℓ} {A} (x ∷ xs) = x + sum xs where open CommutativeRing A

Powerseries : {c ℓ : Level} → CommutativeRing c ℓ → CommutativeRing c ℓ
Powerseries A = record
  { Carrier = ℕ → CommutativeRing.Carrier A
  ; _≈_ = λ f g → (n : ℕ) → f n ≈ g n
  ; _+_ = λ f g n → f n + g n
  ; _*_ = λ f g n → sum (map (λ i → f i * g (n Data.Nat.∸ i)) (upTo (ℕ.suc n)))
  ; -_ = λ f n → - (f n)
  ; 0# = λ n → 0#
  ; 1# = λ { ℕ.zero → 1# ; (ℕ.suc n) → 0# }
  ; isCommutativeRing = record
    { isRing = record
      { +-isAbelianGroup = record
        { isGroup = record
          { isMonoid = record
            { isSemigroup = record
              { isEquivalence = {!!}
              ; assoc = λ f g h n → Algebra.Semigroup.assoc (Algebra.Monoid.semigroup (Algebra.Group.monoid (Algebra.AbelianGroup.group (Algebra.Ring.+-abelianGroup (Algebra.CommutativeRing.ring A))))) (f n) (g n) (h n)
              ; ∙-cong = {!!} }
            ; identity = {!!} }
          ; inverse = {!!}
          ; ⁻¹-cong = {!!} }
        ; comm = {!!}
        }
      ; *-isMonoid = {!!}
      ; distrib = {!!}
      }
    ; *-comm = {!!}
    }
  }
  where
  open CommutativeRing A
