{-# OPTIONS --type-in-type #-}

open import Data.Container
open import Level
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Product hiding (map)

open import Free

module FreeIsDioid where

-- Probaremos aquí las leyes de dioide que deben cumplir las operaciones
-- definidas en Free.agda
-- Notar que hemos optado por usar el planteo de definir un functor monoidal 
-- laxo junto con una operación suma, que en conjunto satisfacen las leyes
-- dioidales.

  -- ⊕ left identity
  ⊕F-left-zero : {C : Cont}{X : Set} (x : TF C X) →  z' ⊕F x ≡ x
  ⊕F-left-zero tf = refl

  -- ⊕ right identity
  ⊕v-right-zero : {C : Cont}{X : Set} (x : TW C X) →  x ⊕v z' ≡ x 
  ⊕v-right-zero (a' x) = refl
  ⊕v-right-zero (suma1 (a' x) x₁) = refl
  ⊕v-right-zero (suma1 (prod1 x) x₁) = refl
  ⊕v-right-zero (suma1 (prod2 x x₁) x₂) = refl
  ⊕v-right-zero (suma2 x tw) = cong (λ x₁ → suma2 x x₁) (⊕v-right-zero tw)
  ⊕v-right-zero (prod1 x) = refl
  ⊕v-right-zero (prod2 x tw) = refl

  ⊕F-right-zero : {C : Cont}{X : Set} (x : TF C X) →  x ⊕F z' ≡ x
  ⊕F-right-zero z' = refl
  ⊕F-right-zero (o' x) = refl
  ⊕F-right-zero (w' x) = cong w' (⊕v-right-zero x)

  -- ⊕ assoc
  ⊕v-assoc : {C : Cont}{X : Set} (x : TW C X)(y z : TF C X) → x ⊕v (y ⊕F z) ≡ (x ⊕v y) ⊕v z
  ⊕v-assoc (a' x) z' z = refl
  ⊕v-assoc (a' x) (o' x₁) z = refl
  ⊕v-assoc (a' x) (w' x₁) z = refl
  ⊕v-assoc (suma1 (a' x) x₁) y z = refl
  ⊕v-assoc (suma1 (prod1 x) x₁) y z = refl
  ⊕v-assoc (suma1 (prod2 x x₁) x₂) y z = refl
  ⊕v-assoc (suma2 x x₁) y z = cong (λ x₂ → suma2 x x₂) (⊕v-assoc x₁ y z)
  ⊕v-assoc (prod1 x) z' z = refl
  ⊕v-assoc (prod1 x) (o' x₁) z = refl
  ⊕v-assoc (prod1 x) (w' x₁) z = refl
  ⊕v-assoc (prod2 x x₁) z' z = refl
  ⊕v-assoc (prod2 x x₁) (o' x₂) z = refl
  ⊕v-assoc (prod2 x x₁) (w' x₂) z = refl

  ⊕F-assoc : {C : Cont}{X : Set} (x y z : TF C X) → x ⊕F (y ⊕F z) ≡ (x ⊕F y) ⊕F z
  ⊕F-assoc z' y z = refl
  ⊕F-assoc (o' x) y z = refl
  ⊕F-assoc (w' x) y z = cong w' (⊕v-assoc x y z)

  -- ⊕ abs element
  ⊕F-abs : {C : Cont} {X : Set} (y : X) (x : TF C X) → 
             fmapf (λ _ → y) (o' tt) ⊕F x ≡ fmapf (λ _ → y) (o' tt)
  ⊕F-abs y tf = refl

  open ≡-Reasoning

  -- ⊗ left identity
  ⊗v-left-iden : {C : Cont}{X : Set} (x : TW C X) → fmapw proj₂ (fmapw (_,_ tt) x) ≡ x
  ⊗v-left-iden (a' x) = cong a' (lemma-id x)
  ⊗v-left-iden (suma1 x x₁) = cong₂ suma1 (trans (sym (fmaps-∘ (λ r → proj₂ r) (_,_ tt) x)) (fmaps-id x)) refl
  ⊗v-left-iden (suma2 x tw) = begin
                               suma2 (fmaps (λ r → proj₂ r) (fmaps (_,_ tt) x)) (fmapw (λ r → proj₂ r) (fmapw (_,_ tt) tw))
                              ≡⟨ cong₂ suma2 (sym (fmaps-∘ (λ r → proj₂ r) (_,_ tt) x)) (sym (fmapw-∘ (λ r → proj₂ r) (_,_ tt) tw)) ⟩
                               suma2 (fmaps (λ z → z) x) (fmapw (λ z → z) tw)
                              ≡⟨ cong₂ suma2 (fmaps-id x) (fmapw-id tw) ⟩
                               suma2 x tw
                              ∎
  ⊗v-left-iden (prod1 x) = begin
                            prod1 (fmapp (λ g z → proj₂ (g z)) (fmapp (λ g z → tt , g z) x))
                           ≡⟨  cong prod1 (sym (fmapp-∘ (λ g z → proj₂ (g z)) (λ z z₁ → tt , z z₁) x)) ⟩
                            prod1 (fmapp (λ z → z) x)
                           ≡⟨ cong prod1 (fmapp-id x) ⟩
                             prod1 x
                           ∎
  ⊗v-left-iden (prod2 x tw) = begin 
                                prod2 (fmapp (λ g z → proj₂ (g z)) (fmapp (λ g z → tt , g z) x)) tw
                              ≡⟨ cong (λ z → prod2 z tw) (sym (fmapp-∘ (λ g z → proj₂ (g z)) (λ z z₁ → tt , z z₁) x)) ⟩
                                prod2 (fmapp (λ z → z) x) tw
                              ≡⟨ cong (λ z → prod2 z tw) (fmapp-id x) ⟩
                                prod2 x tw
                              ∎
      
  ⊗F-left-iden : {C : Cont}{X : Set} (x : TF C X) → fmapf proj₂ (o' tt ⊗F x) ≡ x
  ⊗F-left-iden z' = refl
  ⊗F-left-iden (o' x) = refl
  ⊗F-left-iden (w' x) = cong w' (⊗v-left-iden x)

  -- ⊗ right identity
  ⋆E-right-iden : {C : Cont}{X : Set} (x : TW C X) → fmapw proj₁ (x ⋆E o' tt) ≡ x
  ⋆E-right-iden (a' x) = cong a' (lemma-id x)
  ⋆E-right-iden (suma1 x x₁) =
    begin
      suma1 (fmaps (λ r → proj₁ r) (fmaps (λ z → z , tt) x)) x₁ 
    ≡⟨ cong (λ z → suma1 z x₁) (sym (fmaps-∘ (λ r → proj₁ r) (λ z → z , tt) x)) ⟩
      suma1 (fmaps (λ z → z) x) x₁
    ≡⟨ cong (λ z → suma1 z x₁) (fmaps-id x) ⟩
      suma1 x x₁
    ∎ 
  ⋆E-right-iden (suma2 x tw) = --{!!}
    begin
      suma2 (fmaps (λ r → proj₁ r) (fmaps (λ z → z , tt) x))
            (fmapw (λ r → proj₁ r) (fmapw (λ z → z , tt) tw))
    ≡⟨ cong₂ suma2 (sym (fmaps-∘ (λ r → proj₁ r) (λ z → z , tt) x))
                   (sym (fmapw-∘ (λ r → proj₁ r) (λ z → z , tt) tw)) ⟩
      suma2 (fmaps (λ z → z) x) (fmapw (λ z → z) tw)
    ≡⟨ cong₂ suma2 (fmaps-id x) (fmapw-id tw) ⟩
     suma2 x tw
    ∎
  ⋆E-right-iden (prod1 x) = 
    begin
      prod1 (fmapp (λ g z → proj₁ (g z))
            (fmapp (λ f p → f (proj₁ p) , proj₂ p) x))
     ≡⟨ cong prod1 (sym (fmapp-∘ (λ e r → proj₁ (e r)) (λ e r → e (proj₁ r) , proj₂ r) x)) ⟩
      prod1 (fmapp (λ d → (λ g z → proj₁ (g z)) ((λ f p → f (proj₁ p) , proj₂ p) d))
             x)
    ≡⟨ sym (prod1-nat (λ x₁ → proj₁ x₁) x) ⟩
      prod1 x
    ∎ 
      
  ⋆E-right-iden (prod2 x tw) = 
   begin
    prod2 (fmapp (λ g z → proj₁ (g z))
          (fmapp (λ f p → f (proj₁ p) , proj₂ p) x))
          (tw ⋆E o' tt)
   ≡⟨ cong₂ prod2 (sym (fmapp-∘ (λ g z → proj₁ (g z)) (λ f p → f (proj₁ p) , proj₂ p) x)) refl ⟩
     prod2 (fmapp (λ d → (λ g z → proj₁ (g z)) ((λ f p → f (proj₁ p) , proj₂ p) d)) x) (tw ⋆E o' tt) 
   ≡⟨ sym (prod2-nat (λ x₁ → proj₁ x₁) x (tw ⋆E o' tt)) ⟩
     prod2 x (fmapw (λ x₁ → proj₁ x₁) (tw ⋆E o' tt))
   ≡⟨ cong (λ x₁ → prod2 x x₁) (⋆E-right-iden tw) ⟩
     prod2 x tw
   ∎

  ⊗F-right-iden : {C : Cont}{X : Set} (x : TF C X) → fmapf proj₁ (x ⊗F o' tt) ≡ x
  ⊗F-right-iden z' = refl
  ⊗F-right-iden (o' x) = refl
  ⊗F-right-iden (w' x) = cong w' (⋆E-right-iden x)


  -- ⊗ assoc
  ⋆E-assoc : {C : Cont}{X Y Z : Set} (x : TW C X) (y : TF C Y) (z : TF C Z) 
              → fmapw (λ x → proj₁ (proj₁ x) , (proj₂ (proj₁ x)) , (proj₂ x)) ((x ⋆E y) ⋆E z) ≡ x ⋆E (y ⊗F z)
  ⋆E-assoc (a' x) z' z = cong prod1 (cong a' refl)
  ⋆E-assoc (a' x) (o' x₁) z = begin
     fmapw (λ x₂ → proj₁ (proj₁ x₂) , proj₂ (proj₁ x₂) , proj₂ x₂) (a' (map (λ x₂ → x₂ , x₁) x) ⋆E z)
   ≡⟨ refl ⟩
     fmapw (λ x₂ → proj₁ (proj₁ x₂) , proj₂ (proj₁ x₂) , proj₂ x₂) (fmapw (λ x₂ → x₂ , x₁) (a' x) ⋆E z)
   ≡⟨ cong
        (fmapw (λ x₂ → proj₁ (proj₁ x₂) , proj₂ (proj₁ x₂) , proj₂ x₂))
        (cong (λ v → fmapw (λ x₂ → x₂ , x₁) (a' x) ⋆E v) (sym (fmapf-id z))) ⟩
     fmapw (λ x₂ → proj₁ (proj₁ x₂) , proj₂ (proj₁ x₂) , proj₂ x₂) (fmapw (λ x₂ → x₂ , x₁) (a' x) ⋆E fmapf (λ e → e) z)
   ≡⟨  cong (fmapw (λ x₂ → proj₁ (proj₁ x₂) , proj₂ (proj₁ x₂) , proj₂ x₂)) (sym (e-nat (a' x) z (λ z₁ → z₁ , x₁) (λ z₁ → z₁)))  ⟩
     fmapw (λ x₂ → proj₁ (proj₁ x₂) , proj₂ (proj₁ x₂) , proj₂ x₂) (fmapw (λ x₂ → (proj₁ x₂ , x₁) , proj₂ x₂) ((a' x) ⋆E z))
   ≡⟨ sym (fmapw-∘ (λ x₂ → proj₁ (proj₁ x₂) , (proj₂ (proj₁ x₂) , proj₂ x₂)) (λ x₂ → ((proj₁ x₂) , x₁) , (proj₂ x₂)) (a' x ⋆E z)) ⟩
     fmapw (λ p → proj₁ p , x₁ , (proj₂ p)) (a' x ⋆E z)
   ≡⟨ e-nat (a' x) z (λ z → z) (_,_ x₁) ⟩
     fmapw (λ z → z) (a' x) ⋆E fmapf (_,_ x₁) z
   ≡⟨ cong (λ w → w ⋆E fmapf (_,_ x₁) z) (fmapw-id (a' x)) ⟩
     a' x ⋆E fmapf (_,_ x₁) z
   ∎
  ⋆E-assoc (a' x) (w' x₁) z = cong₂ prod2 (cong a' refl) refl
  ⋆E-assoc (suma1 x r₁) z' z = 
   begin
    prod1
      (suma1
       (fmaps
        (λ g z₁ →
           proj₁ (proj₁ (g z₁)) , proj₂ (proj₁ (g z₁)) , proj₂ (g z₁))
        (fmaps (λ f p → f (proj₁ p) , proj₂ p) (fmaps _,_ x)))
       (_,_ r₁))
   ≡⟨ cong prod1 (cong (λ q → suma1 q (λ d → r₁ , d)) (sym (fmaps-∘ ((λ g z₁ → proj₁ (proj₁ (g z₁)) , proj₂ (proj₁ (g z₁)) , proj₂ (g z₁))) ((λ f p → f (proj₁ p) , proj₂ p)) (fmaps _,_ x)))) ⟩
    prod1 (suma1 (fmaps (λ e t → ((proj₁ (e (proj₁ t)))) , ((proj₂ (e (proj₁ t))) , (proj₂ t))) (fmaps _,_ x)) (_,_ r₁))
   ≡⟨ cong prod1 (cong (λ q → suma1 q (λ d → r₁ , d)) (sym (fmaps-∘ ((λ e t → ((proj₁ (e (proj₁ t)))) , ((proj₂ (e (proj₁ t))) , (proj₂ t)))) (λ e d → e , d) x))) ⟩
    prod1 (suma1 (fmaps _,_ x) (_,_ r₁))
   ∎ 
  ⋆E-assoc (suma1 x r₁) (o' x₁) z = 
   begin
    fmapw (λ x₂ → proj₁ (proj₁ x₂) , (proj₂ (proj₁ x₂) , proj₂ x₂))
           ((suma1 (fmaps (λ z₁ → z₁ , x₁) x) (r₁ , x₁)) ⋆E z)
   ≡⟨ refl ⟩
    fmapw (λ x₂ → proj₁ (proj₁ x₂) , (proj₂ (proj₁ x₂) , proj₂ x₂))
           ((fmapw (λ z₁ → z₁ , x₁) (suma1 x r₁)) ⋆E z)
   ≡⟨ cong (λ q → fmapw (λ x₂ → proj₁ (proj₁ x₂) , (proj₂ (proj₁ x₂) , proj₂ x₂)) ((fmapw (λ z₁ → z₁ , x₁) (suma1 x r₁)) ⋆E q)) (sym (fmapf-id z) ) ⟩
    fmapw (λ x₂ → proj₁ (proj₁ x₂) , (proj₂ (proj₁ x₂) , proj₂ x₂))
           ((fmapw (λ z₁ → z₁ , x₁) (suma1 x r₁)) ⋆E (fmapf (λ e → e) z))
   ≡⟨ cong (fmapw (λ x₂ → proj₁ (proj₁ x₂) , (proj₂ (proj₁ x₂) , proj₂ x₂))) (sym (e-nat (suma1 x r₁) z ((λ z₁ → z₁ , x₁)) (λ e → e ))) ⟩
      fmapw (λ x₂ → proj₁ (proj₁ x₂) , proj₂ (proj₁ x₂) , proj₂ x₂) (fmapw (λ e → ((proj₁ e) , x₁) , (proj₂ e)) (suma1 x r₁ ⋆E z))
   ≡⟨ sym (fmapw-∘ ((λ x₂ → proj₁ (proj₁ x₂) , proj₂ (proj₁ x₂) , proj₂ x₂)) ( (λ e → ((proj₁ e) , x₁) , (proj₂ e))) (suma1 x r₁ ⋆E z)) ⟩
    fmapw (λ p → proj₁ p ,  (_,_ x₁) (proj₂ p)) (suma1 x r₁ ⋆E z)
   ≡⟨ e-nat (suma1 x r₁) z (λ e → e) (_,_ x₁)  ⟩
    suma1 (fmaps (λ e → e) x) r₁ ⋆E fmapf (_,_ x₁) z
   ≡⟨ cong (λ d → suma1 d r₁ ⋆E fmapf (_,_ x₁) z) (fmaps-id x) ⟩
    suma1 x r₁ ⋆E fmapf (_,_ x₁) z
   ∎ 
  ⋆E-assoc (suma1 x r₁) (w' x₁) z = 
    begin 
     prod2
      (suma1
       (fmaps
        (λ g z₁ →
           proj₁ (proj₁ (g z₁)) , proj₂ (proj₁ (g z₁)) , proj₂ (g z₁))
        (fmaps (λ f p → f (proj₁ p) , proj₂ p) (fmaps _,_ x)))
       (λ z₁ → r₁ , proj₁ z₁ , proj₂ z₁))
      (x₁ ⋆E z)
    ≡⟨ cong (λ a → prod2 (suma1 a  (λ z₁ → r₁ , proj₁ z₁ , proj₂ z₁)) (x₁ ⋆E z)) (sym (fmaps-∘ ((λ g z₁ → proj₁ (proj₁ (g z₁)) , proj₂ (proj₁ (g z₁)) , proj₂ (g z₁))) ((λ f p → f (proj₁ p) , proj₂ p)) (fmaps _,_ x))) ⟩
      prod2 (suma1 (fmaps (λ e d → proj₁ (e (proj₁ d)) , ((proj₂ (e (proj₁ d)))) , (proj₂ d)) ((fmaps _,_ x))) ((λ z₁ → r₁ , proj₁ z₁ , proj₂ z₁))) (x₁ ⋆E z)
    ≡⟨ cong
         (λ a → prod2 (suma1 a (λ z₁ → r₁ , proj₁ z₁ , proj₂ z₁)) (x₁ ⋆E z))
         (sym (fmaps-∘ ((λ e d → proj₁ (e (proj₁ d)) , ((proj₂ (e (proj₁ d)))) , (proj₂ d))) _,_ x)) ⟩
       prod2 (suma1 (fmaps _,_ x) (_,_ r₁)) (x₁ ⋆E z)
    ∎ 
  ⋆E-assoc (suma2 x x₁) z' z = 
    begin
      prod1
      (suma2
       (fmaps
        (λ g z₁ →
           proj₁ (proj₁ (g z₁)) , proj₂ (proj₁ (g z₁)) , proj₂ (g z₁))
        (fmaps (λ f p → f (proj₁ p) , proj₂ p) (fmaps _,_ x)))
       (fmapw
        (λ g z₁ →
           proj₁ (proj₁ (g z₁)) , proj₂ (proj₁ (g z₁)) , proj₂ (g z₁))
        (fmapw (λ f p → f (proj₁ p) , proj₂ p) (fmapw _,_ x₁))))
    ≡⟨ cong prod1 (cong₂ suma2
        (sym (fmaps-∘ ((λ g z₁ → proj₁ (proj₁ (g z₁)) , proj₂ (proj₁ (g z₁)) , proj₂ (g z₁))) ((λ f p → f (proj₁ p) , proj₂ p)) (fmaps _,_ x)))
        (sym (fmapw-∘ ((λ g z₁ → proj₁ (proj₁ (g z₁)) , proj₂ (proj₁ (g z₁)) , proj₂ (g z₁))) ((λ f p → f (proj₁ p) , proj₂ p)) (fmapw _,_ x₁))) ) ⟩
      prod1 (suma2 (fmaps (λ e d → (proj₁ (e (proj₁ d))) , ((proj₂ (e (proj₁ d))) , (proj₂ d))) (fmaps _,_ x))
                   (fmapw ((λ e d → (proj₁ (e (proj₁ d))) , ((proj₂ (e (proj₁ d))) , (proj₂ d)))) (fmapw _,_ x₁)))
    ≡⟨ refl ⟩
     prod1 (fmapp (((λ e d → (proj₁ (e (proj₁ d))) , ((proj₂ (e (proj₁ d))) , (proj₂ d))))) (suma2 (fmaps _,_ x) (fmapw _,_ x₁)))
    ≡⟨ refl ⟩
      prod1 (fmapp (((λ e d → (proj₁ (e (proj₁ d))) , ((proj₂ (e (proj₁ d))) , (proj₂ d))))) ((fmapp _,_) (suma2 x x₁)))
    ≡⟨ cong prod1 (sym (fmapp-∘ ((λ e d → (proj₁ (e (proj₁ d))) , ((proj₂ (e (proj₁ d))) , (proj₂ d)))) _,_ (suma2 x x₁))) ⟩
       prod1 (suma2 (fmaps _,_ x) (fmapw _,_ x₁))
    ∎
  ⋆E-assoc (suma2 x x₁) (o' x₂) z = -- {!!}
    begin
      fmapw (λ x₃ → proj₁ (proj₁ x₃) , proj₂ (proj₁ x₃) , proj₂ x₃)
      (suma2 (fmaps (λ z₁ → z₁ , x₂) x) (fmapw (λ z₁ → z₁ , x₂) x₁) ⋆E z)
    ≡⟨ refl ⟩
      fmapw (λ x₃ → proj₁ (proj₁ x₃) , proj₂ (proj₁ x₃) , proj₂ x₃)
      ((fmapw (λ z₁ → z₁ , x₂) (suma2 x x₁)) ⋆E z)
    ≡⟨ cong ((λ q → (fmapw (λ x₃ → proj₁ (proj₁ x₃) , proj₂ (proj₁ x₃) , proj₂ x₃)
      ((fmapw (λ z₁ → z₁ , x₂) (suma2 x x₁)) ⋆E q)))) (sym (fmapf-id z)) ⟩
      fmapw (λ x₃ → proj₁ (proj₁ x₃) , proj₂ (proj₁ x₃) , proj₂ x₃)
        (fmapw (λ z₁ → z₁ , x₂) (suma2 x x₁) ⋆E fmapf (λ s → s) z) 
    ≡⟨ cong (fmapw (λ x₃ → proj₁ (proj₁ x₃) , proj₂ (proj₁ x₃) , proj₂ x₃))
         (sym (e-nat (suma2 x x₁) z ((λ z₁ → z₁ , x₂)) (λ e → e))) ⟩
     fmapw (λ x₃ → proj₁ (proj₁ x₃) , proj₂ (proj₁ x₃) , proj₂ x₃)
       (fmapw (λ e → ((proj₁ e) , x₂) , (proj₂ e)) ((suma2 x x₁ ⋆E z))) 
    ≡⟨ sym (fmapw-∘ ((λ x₃ → proj₁ (proj₁ x₃) , proj₂ (proj₁ x₃) , proj₂ x₃)) ((λ e → ((proj₁ e) , x₂) , (proj₂ e))) ((suma2 x x₁ ⋆E z))) ⟩
      fmapw (λ e → (proj₁ e) , (x₂ , (proj₂ e))) (suma2 x x₁ ⋆E z)
    ≡⟨(e-nat (suma2 x x₁) z (λ e → e) (_,_ x₂)) ⟩
     (fmapw (λ e → e) (suma2 x x₁)) ⋆E fmapf (_,_ x₂) z
    ≡⟨ cong (λ e → e ⋆E (fmapf (_,_ x₂) z)) (fmapw-id (suma2 x x₁)) ⟩
      suma2 x x₁ ⋆E fmapf (_,_ x₂) z
    ∎

  ⋆E-assoc {C} {X} {Y} {Z} (suma2 x x₁) (w' x₂) z = 
    begin
      prod2 (suma2 (fmaps (λ g z₁ → proj₁ (proj₁ (g z₁)) , proj₂ (proj₁ (g z₁)) , proj₂ (g z₁)) (fmaps (λ f p → f (proj₁ p) , proj₂ p) (fmaps _,_ x))) (fmapw (λ g z₁ → proj₁ (proj₁ (g z₁)) , proj₂ (proj₁ (g z₁)) , proj₂ (g z₁)) (fmapw (λ f p → f (proj₁ p) , proj₂ p) (fmapw _,_ x₁)))) (x₂ ⋆E z)
    ≡⟨ cong₂ prod2 (cong₂ suma2 (sym (fmaps-∘ (λ x₃ x₄ → (proj₁ (proj₁ (x₃ x₄))) , ((proj₂ (proj₁ (x₃ x₄))) , (proj₂ (x₃ x₄)))) (λ x₃ x₄ → ((proj₁ (x₃ (proj₁ x₄))) , proj₂ (x₃ (proj₁ x₄))) , proj₂ x₄) (fmaps _,_ x))) ((sym (fmapw-∘ (λ x₃ x₄ → (proj₁ (proj₁ (x₃ x₄))) , ((proj₂ (proj₁ (x₃ x₄))) , (proj₂ (x₃ x₄)))) (λ x₃ x₄ → ((proj₁ (x₃ (proj₁ x₄))) , proj₂ (x₃ (proj₁ x₄))) , proj₂ x₄) (fmapw _,_ x₁))))) refl ⟩
     prod2 (suma2 (fmaps (λ x₃ x₄ → (proj₁ (x₃ (proj₁ x₄))) , (proj₂ (x₃ (proj₁ x₄))) , proj₂ x₄) (fmaps _,_ x)) (fmapw (λ x₃ x₄ → (proj₁ (x₃ (proj₁ x₄))) , (proj₂ (x₃ (proj₁ x₄))) , proj₂ x₄) (fmapw _,_ x₁))) (x₂ ⋆E z)
    ≡⟨ cong₂ prod2 (cong₂ suma2 (sym (fmaps-∘ (λ x₃ x₄ → (proj₁ (x₃ (proj₁ x₄))) , (proj₂ (x₃ (proj₁ x₄))) , proj₂ x₄) _,_ x)) ((sym (fmapw-∘ (λ x₃ x₄ → (proj₁ (x₃ (proj₁ x₄))) , (proj₂ (x₃ (proj₁ x₄))) , proj₂ x₄) _,_ x₁)))) refl ⟩
     prod2 (suma2 (fmaps _,_ x) (fmapw _,_ x₁)) (x₂ ⋆E z)
    ∎
  ⋆E-assoc (prod1 x) y z = 
   begin
    prod1
      (fmapp
       (λ g z₁ →
          proj₁ (proj₁ (g z₁)) , proj₂ (proj₁ (g z₁)) , proj₂ (g z₁))
       (fmapp (λ f p → f (proj₁ p) , proj₂ p)
        (fmapp (λ f p → f (proj₁ p) , proj₂ p) x)))
   ≡⟨ cong prod1 (sym (fmapp-∘ (λ g z₁ → proj₁ (proj₁ (g z₁)) , proj₂ (proj₁ (g z₁)) , proj₂ (g z₁)) (λ f p → f (proj₁ p) , proj₂ p) (fmapp (λ f p → f (proj₁ p) , proj₂ p) x))) ⟩
    prod1 (fmapp (λ e d → (proj₁ (e (proj₁ d))) , ((proj₂ (e (proj₁ d))) , (proj₂ d))) (fmapp (λ f p → f (proj₁ p) , proj₂ p) x))
   ≡⟨ cong prod1 (sym (fmapp-∘ (λ e d → (proj₁ (e (proj₁ d))) , ((proj₂ (e (proj₁ d))) , (proj₂ d))) (λ f p → f (proj₁ p) , proj₂ p) x)) ⟩
    prod1 (fmapp (λ f p → (f (proj₁ (proj₁ p))) , ((proj₂ (proj₁ p)) , (proj₂ p))) x) 
   ≡⟨ cong prod1 (fmapp-∘ (λ q d →
      proj₁ (q ((proj₁ (proj₁ d)) ,
        (proj₂ (proj₁ d) , proj₂ d)))
      , (proj₁ (proj₂ (q (proj₁ (proj₁ d) , proj₂ (proj₁ d) , proj₂ d))) ,
      proj₂ (proj₂ (q (proj₁ (proj₁ d) , proj₂ (proj₁ d) , proj₂ d))))) ((λ f p → f (proj₁ p) , proj₂ p)) x) ⟩
    prod1 (fmapp (λ q d →
      proj₁ (q ((proj₁ (proj₁ d)) ,
        (proj₂ (proj₁ d) , proj₂ d)))
      , (proj₁ (proj₂ (q (proj₁ (proj₁ d) , proj₂ (proj₁ d) , proj₂ d))) ,
      proj₂ (proj₂ (q (proj₁ (proj₁ d) , proj₂ (proj₁ d) , proj₂ d))))) (fmapp (λ f p → f (proj₁ p) , proj₂ p) x)) 
   ≡⟨ sym (prod1-nat (λ e → (proj₁ (proj₁ e)) , (proj₂ (proj₁ e) , proj₂ e)) (fmapp (λ f p → f (proj₁ p) , proj₂ p) x)) ⟩
    prod1 (fmapp (λ f p → f (proj₁ p) , proj₂ p) x)
   ∎
  ⋆E-assoc (prod2 x x₁) y z = -- {!!}
   begin
    prod2
      (fmapp
       (λ g z₁ →
          proj₁ (proj₁ (g z₁)) , proj₂ (proj₁ (g z₁)) , proj₂ (g z₁))
       (fmapp (λ f p → f (proj₁ p) , proj₂ p)
        (fmapp (λ f p → f (proj₁ p) , proj₂ p) x)))
      ((x₁ ⋆E y) ⋆E z)
   ≡⟨ cong (λ q → prod2 q ((x₁ ⋆E y) ⋆E z) ) (sym (fmapp-∘ (λ g z₁ →
          proj₁ (proj₁ (g z₁)) , proj₂ (proj₁ (g z₁)) , proj₂ (g z₁)) (λ f p → f (proj₁ p) , proj₂ p) (fmapp (λ f p → f (proj₁ p) , proj₂ p) x))) ⟩
    prod2 (fmapp (λ e d → (proj₁ (e (proj₁ d))) , ((proj₂ (e (proj₁ d))) , (proj₂ d))) (fmapp (λ f p → f (proj₁ p) , proj₂ p) x)) ((x₁ ⋆E y) ⋆E z) 
   ≡⟨ cong (λ q → prod2 q ((x₁ ⋆E y) ⋆E z)) (sym (fmapp-∘ (λ e d → (proj₁ (e (proj₁ d))) , ((proj₂ (e (proj₁ d))) , (proj₂ d))) (λ f p → f (proj₁ p) , proj₂ p) x)) ⟩
    prod2 (fmapp (λ e d → (e (proj₁ (proj₁ d))) , ((proj₂ (proj₁ d)) , (proj₂ d))) x) ((x₁ ⋆E y) ⋆E z)
   ≡⟨ cong (λ q → prod2 q ((x₁ ⋆E y) ⋆E z))
   (fmapp-∘ (λ e d → (proj₁ (e (proj₁ d))) , ((proj₂ (proj₁ d)) , (proj₂ d)))
            (λ f p → f (proj₁ p) , proj₂ p)
            x) ⟩
   prod2 (fmapp (λ e d → (proj₁ (e (proj₁ d))) , ((proj₂ (proj₁ d)) , (proj₂ d))) (fmapp (λ f p → f (proj₁ p) , proj₂ p) x)) ((x₁ ⋆E y) ⋆E z)
   ≡⟨ cong (λ q → prod2 q ((x₁ ⋆E y) ⋆E z)) (sym (fmapp-∘ (λ e d → (proj₁ (e (proj₁ d))) , ((proj₂ (proj₁ d)) , (proj₂ d))) (λ f p → f (proj₁ p) , proj₂ p) x)) ⟩
     prod2 (fmapp (λ e d → (e (proj₁ (proj₁ d))) , ((proj₂ (proj₁ d)) , (proj₂ d))) x) ((x₁ ⋆E y) ⋆E z)
   ≡⟨ refl ⟩
     prod2 (fmapp (λ e d → e (proj₁ (proj₁ d)) , (proj₂ (proj₁ d) , proj₂ d)) x) ((x₁ ⋆E y) ⋆E z)
   ≡⟨ cong ((λ q → prod2 q ((x₁ ⋆E y) ⋆E z))) (fmapp-∘ (λ e d → (proj₁ (e ((proj₁ (proj₁ d)) , ((proj₂ (proj₁ d)) , (proj₂ d))))) , (((proj₁ (proj₂ (e (proj₁ (proj₁ d) , proj₂ (proj₁ d) , proj₂ d))))) , ((proj₂ (proj₂ (e (proj₁ (proj₁ d) , proj₂ (proj₁ d) , proj₂ d))))))) (λ f p → f (proj₁ p) , proj₂ p) x) ⟩
     prod2 (fmapp (λ e d → (proj₁ (e ((proj₁ (proj₁ d)) , ((proj₂ (proj₁ d)) , (proj₂ d))))) , (((proj₁ (proj₂ (e (proj₁ (proj₁ d) , proj₂ (proj₁ d) , proj₂ d))))) , ((proj₂ (proj₂ (e (proj₁ (proj₁ d) , proj₂ (proj₁ d) , proj₂ d))))))) (fmapp (λ f p → f (proj₁ p) , proj₂ p) x)) ((x₁ ⋆E y) ⋆E  z)
   ≡⟨ sym (prod2-nat (λ e → proj₁ (proj₁ e) , (proj₂ (proj₁ e)) , (proj₂ e)) (fmapp (λ f p → f (proj₁ p) , proj₂ p) x) ((x₁ ⋆E y) ⋆E  z)) ⟩
     prod2 (fmapp (λ f p → f (proj₁ p) , proj₂ p) x) (fmapw ((λ x → proj₁ (proj₁ x) , (proj₂ (proj₁ x)) , (proj₂ x))) ((x₁ ⋆E y) ⋆E  z))
   ≡⟨ cong (λ q → prod2 (fmapp (λ f p → f (proj₁ p) , proj₂ p) x) q) (⋆E-assoc x₁ y z) ⟩
    prod2 (fmapp (λ f p → f (proj₁ p) , proj₂ p) x) (x₁ ⋆E (y ⊗F z))
   ∎

  ⊗F-assoc : {C : Cont}{X Y Z : Set} (x : TF C X) (y : TF C Y) (z : TF C Z) 
              → fmapf (λ x → proj₁ (proj₁ x) , (proj₂ (proj₁ x)) , (proj₂ x)) ((x ⊗F y) ⊗F z) ≡ x ⊗F (y ⊗F z)
  ⊗F-assoc z' y z = refl
  ⊗F-assoc (o' x) y z = 
    begin
     fmapf (λ x₁ → proj₁ (proj₁ x₁) , proj₂ (proj₁ x₁) , proj₂ x₁)
                       (fmapf (_,_ x) y ⊗F z)
    ≡⟨ cong (fmapf (λ x₁ → proj₁ (proj₁ x₁) , proj₂ (proj₁ x₁) , proj₂ x₁)) (cong (λ e → fmapf (_,_ x) y ⊗F e) (sym (fmapf-id z))) ⟩
     fmapf (λ x₁ → proj₁ (proj₁ x₁) , proj₂ (proj₁ x₁) , proj₂ x₁)
                       (fmapf (_,_ x) y ⊗F fmapf (λ e → e) z)
    ≡⟨ cong (fmapf (λ x₁ → proj₁ (proj₁ x₁) , proj₂ (proj₁ x₁) , proj₂ x₁)) (sym (⊗F-nat y z (λ x₁ → x , x₁) (λ x₁ → x₁))) ⟩
     fmapf (λ x₁ → proj₁ (proj₁ x₁) , proj₂ (proj₁ x₁) , proj₂ x₁)
                       (fmapf (λ x₁ → (x , (proj₁ x₁)) , (proj₂ x₁)) (y ⊗F z))
    ≡⟨  sym (fmapf-∘ ((λ x₁ → proj₁ (proj₁ x₁) , proj₂ (proj₁ x₁) , proj₂ x₁)) ((λ x₁ → (x , (proj₁ x₁)) , (proj₂ x₁))) (y ⊗F z))  ⟩
     fmapf (_,_ x) (y ⊗F z)
    ∎
  ⊗F-assoc (w' x) y z = cong w' (⋆E-assoc x y z)


  -- ⊗ abs element
  ⊗F-abs : {C : Cont}{X Y : Set}(x : TF C X) → z' {C}{Y} ⊗F x ≡ z'
  ⊗F-abs tf = refl

-- Hasta aquí hemos probado que nuestra construcción da origen a un dioide.
