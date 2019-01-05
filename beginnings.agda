open import Algebra
open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Algebra.Morphism

CRing : Set (lsuc lzero)
CRing = CommutativeRing lzero lzero

record Alg (Base : CRing) : Set (lsuc lzero) where
  field
    Carrier : CRing
    ι       : CommutativeRing.Carrier Base → CommutativeRing.Carrier Carrier
    isHomo  : IsRingMorphism (CommutativeRing.ring Base) (CommutativeRing.ring Carrier) ι

∥_∥ : {A : CRing} → Alg A → Set
∥ R ∥ = CommutativeRing.Carrier (Alg.Carrier R)

alg : (A : CRing) → Alg A
alg A = record
  { Carrier = A
  ; ι       = λ x → x
  ; isHomo  = {!!}
  }

IsInvertible : {A : CRing} → (x : ∥ alg A ∥) → Set
IsInvertible {A} x = ∃ (λ y → x * y ≈ 1#)
  where
  open CommutativeRing A

IsLocalRing : (A : CRing) → Set
IsLocalRing A = ¬(1# ≈ 0#) × ((x y : ∥ alg A ∥) → IsInvertible {A} (x + y) → (IsInvertible {A} x) ⊎ (IsInvertible {A} y))
  where
  open CommutativeRing A

record Spec {A : CRing} (R : Alg A) : Set where
  field
    point  : ∥ R ∥ → ∥ alg A ∥
    isHomo : IsRingMorphism (CommutativeRing.ring (Alg.Carrier R)) (CommutativeRing.ring A) point

canonicalMorphism : {A : CRing} → (R : Alg A) → ∥ R ∥ → (Spec R → ∥ alg A ∥)
canonicalMorphism R x p = Spec.point p x

IsQuasicoherentRing : (A : CRing) → Set
IsQuasicoherentRing A = {!!}
