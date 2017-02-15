{-# OPTIONS --type-in-type #-}

open import Data.Product hiding (map)
open import Data.Container
open import Level
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Free
open import FreeIsDioid

module Day where

-- Aquí probaremos la propiedad universal del dioide libre.

module FreeDioidForCont where


  -- Primero definimos la estructura de dioide.

  record IsDioid (M₀ : Set → Set)
                 (M₁ : {X Y : Set} → (X → Y) → M₀ X → M₀ Y)
                 (_⊗_ : {X Y : Set} → M₀ X → M₀ Y → M₀ (X × Y))
                 (_⊕_ : {X : Set} → M₀ X → M₀ X → M₀ X)
                 (unit : M₀ ⊤)
                 (empty : {X : Set} → M₀ X) : Set₁ where
         field
           M₁-id : {X : Set} (x : M₀ X) → M₁ (λ z → z) x ≡ x
           M₁-∘ : {X Y Z : Set} (f : Y → Z) (g : X → Y) (x : M₀ X)
             → M₁ (λ z → f (g z)) x ≡ M₁ f (M₁ g x)
           ⊕-left-zero : {X : Set} (x : M₀ X) → empty ⊕ x ≡ x
           ⊕-right-zero : {X : Set} (x : M₀ X) → x ⊕ empty ≡ x
           ⊕-assoc : {X : Set} (x y z : M₀ X) → x ⊕ (y ⊕ z) ≡ (x ⊕ y) ⊕ z
           ⊗-left-iden : {X : Set} (x : M₀ X) → M₁ proj₂ (unit ⊗ x) ≡ x
           ⊗-right-iden : {X : Set} (x : M₀ X) → M₁ proj₁ (x ⊗ unit) ≡ x
           ⊗-assoc :  {X Y Z : Set} (x : M₀ X) (y : M₀ Y) (z : M₀ Z) → M₁ (λ x → proj₁ (proj₁ x) , (proj₂ (proj₁ x)) , (proj₂ x)) ((x ⊗ y) ⊗ z) ≡ x ⊗ (y ⊗ z)
           ⊗-abs : {X Y : Set} (x : M₀ X) → (empty {Y} ⊗ x) ≡ empty
           ⊕-abs : {X : Set} (y : X) (x : M₀ X) → M₁ (λ _ → y) unit ⊕ x ≡ M₁ (λ _ → y) unit
          -- Naturalidades
           ⊗-nat : {X Y W Z : Set} (f : X → W) (g : Y → Z) → (x : M₀ X) (y : M₀ Y) →  M₁ (λ p → f (proj₁ p) , g (proj₂ p)) (x ⊗ y) ≡ M₁ f x ⊗ M₁ g y 
           ⊕-nat : {X Y : Set} (f : X → Y) → (x y : M₀ X) →  M₁ f (x ⊕ y) ≡ M₁ f x ⊕ M₁ f y 
           empty-nat : {X Y : Set} (f : X → Y) → M₁ f empty ≡ empty

  record Dioid : Set₁ where
    field
      M₀ : Set → Set
      M₁ : {X Y : Set} → (X → Y) → M₀ X → M₀ Y
      _⊗_ : {X Y : Set} → M₀ X → M₀ Y → M₀ (X × Y)
      _⊕_ : {X : Set} → M₀ X → M₀ X → M₀ X
      unit : M₀ ⊤
      empty : {X : Set} → M₀ X
      M-IsDioid : IsDioid M₀ M₁ _⊗_ _⊕_ unit empty


  -- A partir de la estructura de dioide podemos definir la de homomorfismo de 
  -- dioides
  record DioidMorphism (M N : Dioid) : Set₁ where
    open Dioid M renaming (
      M₀ to M₀;
      M₁ to M₁;
      _⊗_ to _⊗M_;
      _⊕_ to _⊕M_;
      unit to unitM;
      empty to emptyM)
    open Dioid N renaming (
      M₀ to N₀;
      M₁ to N₁;
      _⊗_ to _⊗N_;
      _⊕_ to _⊕N_;
      unit to unitN;
      empty to emptyN)
    field
      fun : ∀ {X} → M₀ X → N₀ X
      fun-nat : ∀ {X Y} (f : X → Y) (x : M₀ X) → fun (M₁ f x) ≡ N₁ f (fun x)
      preserves-+ : {X : Set} (x y : M₀ X) → fun {X} (x ⊕M y) ≡ fun x ⊕N fun y
      preserves-* : {X Y : Set} (x : M₀ X) (y : M₀ Y) → fun (x ⊗M y) ≡ fun x ⊗N fun y
      preserves-0 : {X : Set} → fun {X} emptyM ≡ emptyN
      preserves-1 : fun unitM ≡ unitN

  open DioidMorphism
 
  -- A partir de las definiciones de Free.agda y FreeIsDioid.agda, establecemos
  -- que el tipo TF es un dioide.
  TF-is-Dioid : {C : Cont} → IsDioid (TF C) fmapf _⊗F_ _⊕F_ (o' tt)  z'
  TF-is-Dioid {C} = record
                      { M₁-id = fmapf-id
                      ; M₁-∘ = fmapf-∘
                      ; ⊕-left-zero = ⊕F-left-zero
                      ; ⊕-right-zero = ⊕F-right-zero
                      ; ⊕-assoc = ⊕F-assoc
                      ; ⊗-left-iden = ⊗F-left-iden
                      ; ⊗-right-iden = ⊗F-right-iden
                      ; ⊗-assoc = ⊗F-assoc
                      ; ⊗-abs = ⊗F-abs
                      ; ⊕-abs = ⊕F-abs
                      ; ⊗-nat = λ f g x y → ⊗F-nat x y f g
                      ; ⊕-nat = λ f x y → ⊕F-nat f x y
                      ; empty-nat = z-nat
                      }

  TF-Dioid : (C : Cont) → Dioid
  TF-Dioid C = record
                    { M₀ = TF C
                    ; M₁ = fmapf 
                    ; _⊗_ = _⊗F_ {C}
                    ; _⊕_ = _⊕F_ {C}
                    ; unit = o' tt
                    ; empty = z'
                    ; M-IsDioid = TF-is-Dioid
                    }

  module Universal {D : Dioid} where
    open Dioid D

    open IsDioid M-IsDioid

    open ≡-Reasoning

    -- Definimos la función que liftea transformaciones naturales que 
    -- llegan a un functor, a transformaciones naturales que salen del libre.
    univ : {C : Cont} → (∀ {X} → ⟦ C ⟧ X → M₀ X) → ∀ {X} → TF C X → M₀ X
    univ f z' = empty
    univ f (o' x) = M₁ (λ _ → x) unit
    univ f (w' (a' x)) = f x
    univ f (w' (suma1 (a' x) y)) = f x ⊕ M₁ (λ _ → y) unit
    univ f (w' (suma1 (prod1 x) y)) = univ f (w' (prod1 x)) ⊕ M₁ (λ _ → y) unit
    univ f (w' (suma1 (prod2 x x₁) y)) = univ f (w' (prod2 x x₁)) ⊕ (M₁ (λ _ → y) unit)
    univ f (w' (suma2 (a' x) y)) = _⊕_ (f x) (univ f (w' y))
    univ f (w' (suma2 (prod1 x) y)) = _⊕_ (univ f (w' (prod1 x))) (univ f (w' y))
    univ f (w' (suma2 (prod2 x x₁) y)) = _⊕_ (univ f (w' (prod2 x x₁))) (univ f (w' y))
    univ f (w' (prod1 (a' x))) = M₁ (λ p → proj₁ p (proj₂ p)) (f x ⊗ empty)
    univ f (w' (prod1 (suma1 x y))) = M₁ (λ p → proj₁ p (proj₂ p)) ((univ f (w' (suma1 x y))) ⊗ empty)
    univ f (w' (prod1 (suma2 x y))) = M₁ (λ p → proj₁ p (proj₂ p)) (univ f (w' (suma2 x y)) ⊗ empty)
    univ f (w' (prod2 (a' x) y)) = M₁ (λ p → proj₁ p (proj₂ p)) (f x ⊗ univ f (w' y))
    univ f (w' (prod2 (suma1 x x₁) y)) = M₁ (λ p → proj₁ p (proj₂ p)) (univ f (w' (suma1 x x₁)) ⊗ univ f (w' y))
    univ f (w' (prod2 (suma2 x x₁) y)) = M₁ (λ p → proj₁ p (proj₂ p)) (univ f (w' (suma2 x x₁)) ⊗ univ f (w' y))


    -- Mostraremos que univ f es un homomorfismo de dioides.
                 
    lemma-assoc : {X : Set} (x : X) (a b : M₀ X) → 
                   a ⊕ M₁ (λ _ → x) unit ≡ (a  ⊕ M₁ (λ _ → x) unit) ⊕ b
    lemma-assoc x a b = begin 
                         a ⊕ M₁ (λ _ → x) unit
                        ≡⟨ cong (λ s → a ⊕ s) (sym (⊕-abs x b)) ⟩
                          a  ⊕ (M₁ (λ _ → x) unit ⊕ b)
                        ≡⟨ ⊕-assoc a (M₁ (λ _ → x) unit) b ⟩
                         (a  ⊕ M₁ (λ _ → x) unit) ⊕ b
                        ∎

    -- Preserva el 0
    univ-preserves-0 : {C : Cont} (f : ∀ {X} → ⟦ C ⟧ X → M₀ X) → {X : Set} → univ f {X} z' ≡ empty
    univ-preserves-0 f = refl

    -- Preserva el 1
    univ-preserves-1 : {C : Cont} (f : ∀ {X} → ⟦ C ⟧ X → M₀ X) → univ f (o' tt) ≡ unit
    univ-preserves-1 f = M₁-id unit

    -- Preserva la suma
    univ-preserves-+ : {C : Cont} (f : ∀ {X} → ⟦ C ⟧ X → M₀ X) → {X : Set} (x y : TF C X) → univ f {X} (x ⊕F y) ≡ univ f x ⊕ univ f y
    univ-preserves-+ f z' y = sym (⊕-left-zero (univ f y)) 
    univ-preserves-+ f (o' x) y = sym (⊕-abs x (univ f y))
    univ-preserves-+ f (w' (a' x)) z' = sym (⊕-right-zero (f x))
    univ-preserves-+ f (w' (a' x)) (o' x₁) = refl
    univ-preserves-+ f (w' (a' x)) (w' x₁) = refl
    univ-preserves-+ f (w' (suma1 (a' x) x₁)) y = lemma-assoc x₁ (f x) (univ f y)
    univ-preserves-+ f (w' (suma1 (prod1 x) x₁)) y = lemma-assoc x₁ (univ f (w' (prod1 x))) (univ f y)
    univ-preserves-+ f (w' (suma1 (prod2 x x₁) x₂)) y = lemma-assoc x₂ (univ f (w' (prod2 x x₁))) (univ f y)
    univ-preserves-+ f (w' (suma2 (a' x) x₁)) y =
                            begin
                              f x ⊕ univ f (w' (x₁ ⊕v y))
                            ≡⟨ refl ⟩
                              f x ⊕ univ f ((w' x₁) ⊕F y)
                            ≡⟨ cong (λ s → f x ⊕ s) (univ-preserves-+ f (w' x₁) y) ⟩
                              f x ⊕ (univ f (w' x₁) ⊕ univ f y)
                            ≡⟨ ⊕-assoc (f x) (univ f (w' x₁)) (univ f y) ⟩
                              (f x ⊕ univ f (w' x₁)) ⊕ univ f y
                            ∎
    univ-preserves-+ f (w' (suma2 (prod1 x) x₁)) y = 
         begin
           univ f (w' (prod1 x)) ⊕ univ f (w' (x₁ ⊕v y)) 
         ≡⟨ refl ⟩
           univ f (w' (prod1 x)) ⊕ univ f ((w' x₁) ⊕F y) 
         ≡⟨ cong (λ s → univ f (w' (prod1 x)) ⊕ s) (univ-preserves-+ f (w' x₁) y) ⟩
           univ f (w' (prod1 x)) ⊕ (univ f (w' x₁) ⊕ univ f y)
         ≡⟨ ⊕-assoc (univ f (w' (prod1 x))) (univ f (w' x₁)) (univ f y) ⟩
           (univ f (w' (prod1 x)) ⊕ univ f (w' x₁)) ⊕ univ f y
         ∎
    univ-preserves-+ f (w' (suma2 (prod2 x x₁) x₂)) y = --{!!}
         begin
           univ f (w' (prod2 x x₁)) ⊕ univ f (w' (x₂ ⊕v y)) 
         ≡⟨ refl ⟩
           univ f (w' (prod2 x x₁)) ⊕ univ f ((w' x₂) ⊕F y) 
         ≡⟨ cong (λ s → univ f (w' (prod2 x x₁)) ⊕ s) (univ-preserves-+ f (w' x₂) y) ⟩
           univ f (w' (prod2 x x₁)) ⊕ (univ f (w' x₂) ⊕ univ f y)
         ≡⟨ ⊕-assoc (univ f (w' (prod2 x x₁))) (univ f (w' x₂)) (univ f y) ⟩
           (univ f (w' (prod2 x x₁)) ⊕ univ f (w' x₂)) ⊕ univ f y
         ∎
    univ-preserves-+ f (w' (prod1 x)) z' = sym (⊕-right-zero (univ f (w' (prod1 x))))
    univ-preserves-+ f (w' (prod1 x)) (o' x₁) = refl
    univ-preserves-+ f (w' (prod1 x)) (w' x₁) = refl
    univ-preserves-+ f (w' (prod2 x x₁)) z' = sym (⊕-right-zero (univ f (w' (prod2 x x₁)) ))
    univ-preserves-+ f (w' (prod2 x x₁)) (o' x₂) = refl
    univ-preserves-+ f (w' (prod2 x x₁)) (w' x₂) = refl

    -- Requerimos de este predicado para usar la hipótesis de que el argumento
    -- de univ es una transformación natural.
    postulate is-nat : {C : Cont} (f : ∀ {X} → ⟦ C ⟧ X → M₀ X) 
                       {X Y : Set} (g : X → Y) (x : ⟦ C ⟧ X) → 
                       f (map g x) ≡ M₁ g (f x)

    -- Vemos que univ f genera una transformación natural.
    univ-nat : {C : Cont} {Y Z : Set} (f : ∀ {X} → ⟦ C ⟧ X → M₀ X)
               → (g : Y → Z) {y : TF C Y} → M₁ g (univ f y) ≡ univ f (fmapf g y)
    univ-nat f g {z'} = empty-nat g
    univ-nat f g {o' x} = sym (IsDioid.M₁-∘ M-IsDioid g (λ _ → x) unit)
    univ-nat f g {w' (a' x)} = sym (is-nat f g (proj₁ x , proj₂ x))
    univ-nat f g {w' (suma1 (a' x) x₁)} = 
     begin
      M₁ g (f x ⊕ M₁ (λ _ → x₁) unit) 
     ≡⟨ ⊕-nat g (f x) (M₁ (λ _ → x₁) unit) ⟩ 
        M₁ g (univ f (w' (a' x))) ⊕ M₁ g (M₁ (λ _ → x₁) unit)
     ≡⟨ cong (λ s → s ⊕ M₁ g (M₁ (λ _ → x₁) unit)) (univ-nat f g {w' (a' x)}) ⟩
        univ f (fmapf g (w' (a' x))) ⊕ M₁ g (M₁ (λ _ → x₁) unit)
     ≡⟨ cong (λ s → univ f (fmapf (λ x₂ → g x₂) (w' (a' x))) ⊕ s) (sym (M₁-∘ g (λ _ → x₁) unit)) ⟩
      univ f (fmapf g  (w' (a' x))) ⊕ M₁ (λ _ → g x₁) unit
     ≡⟨ refl ⟩
      f (proj₁ x , (λ x₂ → g (proj₂ x x₂))) ⊕ M₁ (λ _ → g x₁) unit
     ∎
    univ-nat f g {w' (suma1 (prod1 x) x₁)} =
     begin
      M₁ g (univ f (w' (prod1 x)) ⊕ M₁ (λ _ → x₁) unit) 
     ≡⟨ ⊕-nat g (univ f (w' (prod1 x))) (M₁ (λ _ → x₁) unit) ⟩
        M₁ g (univ f (w' (prod1 x))) ⊕ M₁ g (M₁ (λ _ → x₁) unit)
     ≡⟨ cong (λ s → s ⊕ M₁ g (M₁ (λ _ → x₁) unit)) (univ-nat f g {w' (prod1 x)}) ⟩
        univ f (fmapf g (w' (prod1 x))) ⊕ M₁ g (M₁ (λ _ → x₁) unit)
     ≡⟨ cong (λ s → univ f (fmapf g (w' (prod1 x))) ⊕ s) (sym (M₁-∘ g (λ _ → x₁) unit)) ⟩
      univ f (w' (prod1 (fmapp (λ g₁ z → g (g₁ z)) x))) ⊕
      M₁ (λ _ → g x₁) unit
     ∎
    univ-nat f g {w' (suma1 (prod2 x x₁) x₂)} = 
     begin
      M₁ g (univ f (w' (prod2 x x₁)) ⊕ M₁ (λ _ → x₂) unit) 
     ≡⟨ ⊕-nat g (univ f (w' (prod2 x x₁))) (M₁ (λ _ → x₂) unit) ⟩
        M₁ g (univ f (w' (prod2 x x₁))) ⊕ M₁ g (M₁ (λ _ → x₂) unit)
     ≡⟨ cong (λ s → s ⊕ M₁ g (M₁ (λ _ → x₂) unit)) (univ-nat f g {w' (prod2 x x₁)}) ⟩
         univ f (fmapf g (w' (prod2 x x₁))) ⊕ M₁ g (M₁ (λ _ → x₂) unit)
     ≡⟨ cong (λ s → univ f (fmapf g (w' (prod2 x x₁))) ⊕ s) (sym (M₁-∘ g (λ _ → x₂) unit)) ⟩
      univ f (w' (prod2 (fmapp (λ g₁ z → g (g₁ z)) x) x₁)) ⊕
      M₁ (λ _ → g x₂) unit
     ∎
    univ-nat f g {w' (suma2 (a' x) x₁)} = 
     begin
      M₁ g (univ f (w' (a' x)) ⊕ univ f (w' x₁)) 
     ≡⟨ ⊕-nat g (univ f (w' (a' x))) (univ f (w' x₁)) ⟩
       M₁ g (univ f (w' (a' x))) ⊕ M₁ g (univ f (w' x₁))
     ≡⟨ cong₂ _⊕_ (univ-nat f g {w' (a' x)}) (univ-nat f g {w' x₁}) ⟩
      univ f (fmapf g (w' (a' x))) ⊕ univ f (w' (fmapw g x₁))
     ∎
    univ-nat f g {w' (suma2 (prod1 x) x₁)} = 
     begin
      M₁ g (univ f (w' (prod1 x)) ⊕ univ f (w' x₁)) 
     ≡⟨ ⊕-nat g (univ f (w' (prod1 x))) (univ f (w' x₁)) ⟩
        M₁ g (univ f (w' (prod1 x))) ⊕ M₁ g (univ f (w' x₁))
     ≡⟨ cong₂ _⊕_ (univ-nat f g {w' (prod1 x)}) (univ-nat f g {w' x₁}) ⟩
      univ f (w' (prod1 (fmapp (λ g₁ z → g (g₁ z)) x))) ⊕
      univ f (w' (fmapw g x₁))
     ∎
    univ-nat f g {w' (suma2 (prod2 x x₁) x₂)} =
     begin
      M₁ g (univ f (w' (prod2 x x₁)) ⊕ univ f (w' x₂)) 
     ≡⟨ ⊕-nat g (univ f (w' (prod2 x x₁))) (univ f (w' x₂)) ⟩
        M₁ g (univ f (w' (prod2 x x₁))) ⊕ M₁ g (univ f (w' x₂))
     ≡⟨ cong₂ _⊕_ (univ-nat f g {w' (prod2 x x₁)}) (univ-nat f g {w' x₂}) ⟩
      univ f (w' (prod2 (fmapp (λ g₁ z → g (g₁ z)) x) x₁)) ⊕
      univ f (w' (fmapw g x₂))
     ∎
    univ-nat f g {w' (prod1 (a' x))} = 
     begin
       M₁ g (M₁ (λ p → proj₁ p (proj₂ p)) (f x ⊗ empty)) 
     ≡⟨ sym (M₁-∘ g (λ p → proj₁ p (proj₂ p)) (f x ⊗ empty)) ⟩
        M₁ (λ z → g (proj₁ z (proj₂ z))) (f x ⊗ empty)
     ≡⟨ M₁-∘ (λ p → proj₁ p (proj₂ p)) (λ p → (λ v₁ → g (proj₁ p v₁)) , proj₂ p) (f x ⊗ empty) ⟩
         M₁ (λ p → proj₁ p (proj₂ p))
           (M₁ (λ p → (λ v₁ → g (proj₁ p v₁)) , proj₂ p)
            (univ f (w' (a' x)) ⊗ empty))
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) s) (⊗-nat (λ v v₁ → g (v v₁)) (λ z → z) (univ f (w' (a' x))) empty) ⟩
        M₁ (λ p → proj₁ p (proj₂ p))
          (M₁ (λ v v₁ → g (v v₁)) (univ f (w' (a' x))) ⊗ M₁ (λ z → z) empty)
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p))
         (s ⊗ M₁ (λ z → z) empty)) (univ-nat f (λ x₁ x₂ → g (x₁ x₂)) {w' (a' x)}) ⟩
       M₁ (λ p → proj₁ p (proj₂ p))
         (univ f (fmapf (λ x₁ x₂ → g (x₁ x₂)) (w' (a' x))) ⊗
          M₁ (λ z → z) empty)
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p))
        (univ f (fmapf (λ x₁ x₂ → g (x₁ x₂)) (w' (a' x))) ⊗ s)) (M₁-id empty) ⟩
      M₁ (λ p → proj₁ p (proj₂ p))
        (univ f (fmapf (λ x₁ x₂ → g (x₁ x₂)) (w' (a' x))) ⊗ empty)
     ∎
    univ-nat f g {w' (prod1 (suma1 x x₁))} = --{!!}
     begin
      M₁ g (M₁ (λ p → proj₁ p (proj₂ p)) (univ f (w' (suma1 x x₁)) ⊗ empty))
     ≡⟨ (sym (M₁-∘ g (λ p → proj₁ p (proj₂ p)) (univ f (w' (suma1 x x₁)) ⊗ empty))) ⟩
        M₁ (λ z → g (proj₁ z (proj₂ z)))
          (univ f (w' (suma1 x x₁)) ⊗ empty)
     ≡⟨ M₁-∘ (λ p → proj₁ p (proj₂ p)) (λ p → (λ z → g (proj₁ p z)) , proj₂ p) (univ f (w' (suma1 x x₁)) ⊗ empty) ⟩
        M₁ (λ p → proj₁ p (proj₂ p))
          (M₁ (λ p → (λ z → g (proj₁ p z)) , proj₂ p)
           (univ f (w' (suma1 x x₁)) ⊗ empty))
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) s) (⊗-nat (λ g₁ z → g (g₁ z)) (λ z → z) (univ f (w' (suma1 x x₁))) empty) ⟩
       M₁ (λ p → proj₁ p (proj₂ p))
         (M₁ (λ g₁ z → g (g₁ z)) (univ f (w' (suma1 x x₁))) ⊗ M₁ (λ z → z) empty)
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p))
          (M₁ (λ g₁ z → g (g₁ z)) (univ f (w' (suma1 x x₁))) ⊗ s)) (M₁-id empty) ⟩
        M₁ (λ p → proj₁ p (proj₂ p))
          (M₁ (λ g₁ z → g (g₁ z)) (univ f (w' (suma1 x x₁))) ⊗
           empty)
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) (s ⊗ empty)) (univ-nat f (λ g₁ z → g (g₁ z)) {w' (suma1 x x₁)}) ⟩
      M₁ (λ p → proj₁ p (proj₂ p))
      (univ f (fmapf (λ g₁ z → g (g₁ z)) (w' (suma1 x x₁)))
       ⊗ empty)
     ∎
    univ-nat f g {w' (prod1 (suma2 x x₁))} = -- {!!}
     begin
       M₁ g (M₁ (λ p → proj₁ p (proj₂ p)) (univ f (w' (suma2 x x₁)) ⊗ empty))
     ≡⟨ sym (M₁-∘ g (λ p → proj₁ p (proj₂ p)) (univ f (w' (suma2 x x₁)) ⊗ empty)) ⟩
       M₁ (λ z → g (proj₁ z (proj₂ z)))
         (univ f (w' (suma2 x x₁)) ⊗ empty)
     ≡⟨ M₁-∘ (λ p → proj₁ p (proj₂ p)) (λ p → (λ z → g (proj₁ p z)) , proj₂ p) (univ f (w' (suma2 x x₁)) ⊗ empty) ⟩
        M₁ (λ p → proj₁ p (proj₂ p))
          (M₁ (λ p → (λ z → g (proj₁ p z)) , proj₂ p)
           (univ f (w' (suma2 x x₁)) ⊗ empty))
     ≡⟨ cong (λ s →  M₁ (λ p → proj₁ p (proj₂ p)) s) (⊗-nat (λ g₁ z → g (g₁ z)) (λ z → z) (univ f (w' (suma2 x x₁))) empty) ⟩
       M₁ (λ p → proj₁ p (proj₂ p))
         (M₁ (λ g₁ z → g (g₁ z)) (univ f (w' (suma2 x x₁))) ⊗ M₁ (λ z → z) empty)
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) (M₁ (λ g₁ z → g (g₁ z)) (univ f (w' (suma2 x x₁))) ⊗ s)) (M₁-id empty) ⟩
       M₁ (λ p → proj₁ p (proj₂ p))
         (M₁ (λ g₁ z → g (g₁ z)) (univ f (w' (suma2 x x₁))) ⊗ empty)
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) (s ⊗ empty)) (univ-nat f (λ g₁ z → g (g₁ z)) {w' (suma2 x x₁)}) ⟩
      M₁ (λ p → proj₁ p (proj₂ p))
      (univ f (fmapf (λ g₁ z → g (g₁ z)) (w' (suma2 x x₁)))
       ⊗ empty)
     ∎
    univ-nat f g {w' (prod2 (a' x) x₁)} =
     begin
      M₁ g (M₁ (λ p → proj₁ p (proj₂ p)) (f x ⊗ univ f (w' x₁))) 
     ≡⟨ sym (M₁-∘ g (λ p → proj₁ p (proj₂ p)) (f x ⊗ univ f (w' x₁))) ⟩
        M₁ (λ z → g (proj₁ z (proj₂ z))) (f x ⊗ univ f (w' x₁))
     ≡⟨ M₁-∘ (λ p → proj₁ p (proj₂ p)) (λ p → (λ x₃ → g (proj₁ p x₃)) , proj₂ p) (f x ⊗ univ f (w' x₁)) ⟩
        M₁ (λ p → proj₁ p (proj₂ p))
          (M₁ (λ p → (λ x₃ → g (proj₁ p x₃)) , proj₂ p)
           (univ f (w' (a' x)) ⊗ univ f (w' x₁)))
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) s) (⊗-nat (λ x₂ x₃ → g (x₂ x₃)) (λ s → s) (univ f (w' (a' x))) (univ f (w' x₁))) ⟩
        M₁ (λ p → proj₁ p (proj₂ p))
          (M₁ (λ x₂ x₃ → g (x₂ x₃)) (univ f (w' (a' x))) ⊗
           M₁ (λ s → s) (univ f (w' x₁)))
     ≡⟨ cong (λ d → M₁ (λ p → proj₁ p (proj₂ p))
      (d ⊗ M₁ (λ s → s) (univ f (w' x₁)))) (univ-nat f (λ x₂ x₃ → g (x₂ x₃)) {w' (a' x)}) ⟩
       M₁ (λ p → proj₁ p (proj₂ p))
      ((univ f (fmapf (λ x₂ x₃ → g (x₂ x₃)) (w' (a' x)))) ⊗ M₁ (λ s → s) (univ f (w' x₁)))
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p))
          (univ f (fmapf (λ x₂ x₃ → g (x₂ x₃)) (w' (a' x))) ⊗ s))
          (M₁-id (univ f (w' x₁))) ⟩
      M₁ (λ p → proj₁ p (proj₂ p))
      ((univ f (fmapf (λ x₂ x₃ → g (x₂ x₃)) (w' (a' x)))) ⊗ univ f (w' x₁))
     ∎
    univ-nat f g {w' (prod2 (suma1 x x₁) x₂)} =
     begin
      M₁ g
      (M₁ (λ p → proj₁ p (proj₂ p))
       (univ f (w' (suma1 x x₁)) ⊗ univ f (w' x₂)))
     ≡⟨ sym (M₁-∘ g (λ p → proj₁ p (proj₂ p)) (univ f (w' (suma1 x x₁)) ⊗ univ f (w' x₂))) ⟩
       M₁ (λ z → g (proj₁ z (proj₂ z)))
         (univ f (w' (suma1 x x₁)) ⊗ univ f (w' x₂))
     ≡⟨ M₁-∘ (λ p → proj₁ p (proj₂ p)) (λ p → (λ z → g (proj₁ p z)) , proj₂ p) (univ f(w' (suma1 x x₁)) ⊗ univ f (w' x₂)) ⟩
       M₁ (λ p → proj₁ p (proj₂ p))
         (M₁ (λ p → (λ z → g (proj₁ p z)) , proj₂ p)
          (univ f (w' (suma1 x x₁)) ⊗ univ f (w' x₂)))
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) s) (⊗-nat (λ g₁ z → g (g₁ z)) (λ z → z) (univ f (w' (suma1 x x₁))) (univ f (w' x₂))) ⟩
       M₁ (λ p → proj₁ p (proj₂ p))
         (M₁ (λ g₁ z → g (g₁ z)) (univ f (w' (suma1 x x₁))) ⊗ M₁ (λ z → z) (univ f (w' x₂)))
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p))
         (M₁ (λ g₁ z → g (g₁ z)) (univ f (w' (suma1 x x₁))) ⊗ s)) (M₁-id (univ f (w' x₂))) ⟩
       M₁ (λ p → proj₁ p (proj₂ p))
         (M₁ (λ g₁ z → g (g₁ z)) (univ f (w' (suma1 x x₁))) ⊗ univ f (w' x₂))
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) (s ⊗ univ f (w' x₂))) (univ-nat f (λ g₁ z → g (g₁ z)) {w' (suma1 x x₁)}) ⟩
      M₁ (λ p → proj₁ p (proj₂ p))
      (univ f (fmapf (λ g₁ z → g (g₁ z)) (w' (suma1 x x₁)))
       ⊗ univ f (w' x₂))
     ∎
    univ-nat f g {w' (prod2 (suma2 x x₁) x₂)} =
     begin
       M₁ g (M₁ (λ p → proj₁ p (proj₂ p)) (univ f (w' (suma2 x x₁)) ⊗ univ f (w' x₂)))
     ≡⟨ sym (M₁-∘ g (λ p → proj₁ p (proj₂ p)) (univ f (w' (suma2 x x₁)) ⊗ univ f (w' x₂))) ⟩
       M₁ (λ z → g (proj₁ z (proj₂ z)))
         (univ f (w' (suma2 x x₁)) ⊗ univ f (w' x₂))
     ≡⟨ M₁-∘ (λ p → proj₁ p (proj₂ p)) (λ p → (λ z → g (proj₁ p z)) , proj₂ p) (univ f (w' (suma2 x x₁)) ⊗ univ f (w' x₂)) ⟩
       M₁ (λ p → proj₁ p (proj₂ p)) (M₁ (λ p → (λ z → g (proj₁ p z)) , proj₂ p)
          (univ f (w' (suma2 x x₁)) ⊗ univ f (w' x₂)))
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) s) (⊗-nat (λ g₁ z → g (g₁ z)) (λ z → z) (univ f (w' (suma2 x x₁))) (univ f (w' x₂))) ⟩
       M₁ (λ p → proj₁ p (proj₂ p)) (M₁ (λ g₁ z → g (g₁ z)) (univ f (w' (suma2 x x₁))) ⊗ M₁ (λ z → z) (univ f (w' x₂)))
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) (M₁ (λ g₁ z → g (g₁ z)) (univ f (w' (suma2 x x₁))) ⊗ s)) (M₁-id (univ f (w' x₂))) ⟩
       M₁ (λ p → proj₁ p (proj₂ p)) (M₁ (λ g₁ z → g (g₁ z)) (univ f (w' (suma2 x x₁))) ⊗ univ f (w' x₂))
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) (s ⊗ univ f (w' x₂))) (univ-nat f (λ g₁ z → g (g₁ z)) {w' (suma2 x x₁)}) ⟩
       M₁ (λ p → proj₁ p (proj₂ p)) (univ f (fmapf (λ g₁ z → g (g₁ z)) (w' (suma2 x x₁))) ⊗ univ f (w' x₂))
     ∎

           
    -- Finalmente veamos que univ f preserva el producto.
    univ-preserves-* : {C : Cont} (f : ∀ {X} → ⟦ C ⟧ X → M₀ X) → {X Y : Set} (x : TF C X) (y : TF C Y) → univ f (x ⊗F y) ≡ univ f x ⊗ univ f y
    univ-preserves-* f z' y = sym (⊗-abs (univ f y))
    univ-preserves-* f {X} {Y} (o' x) y =
       begin
         univ f (o' x ⊗F y)
       ≡⟨ refl ⟩ 
          univ f (fmapf (_,_ x) y)
       ≡⟨ sym (univ-nat f ((_,_ x)) {y}) ⟩ 
          M₁ (_,_ x) (univ f y)
       ≡⟨ cong (M₁ (_,_ x)) (sym (⊗-left-iden (univ f y))) ⟩
         M₁ (_,_ x) (M₁ proj₂ (unit ⊗ univ f y))
       ≡⟨ sym (M₁-∘ (_,_ x) proj₂ (unit ⊗ univ f y)) ⟩
         M₁ (λ p → x , proj₂ p) (unit ⊗ univ f y)
       ≡⟨ ⊗-nat (λ _ → x) (λ x₁ → x₁) unit (univ f y) ⟩
         M₁ (λ _ → x) unit ⊗ M₁ (λ x → x) (univ f y)
       ≡⟨ cong (λ s → M₁ (λ _ → x) unit ⊗ s) ((M₁-id (univ f y))) ⟩
         M₁ (λ _ → x) unit ⊗ univ f y
       ≡⟨ refl ⟩ 
         univ f (o' x) ⊗ univ f y
       ∎
    univ-preserves-* f (w' (a' x)) z' =
      begin
       univ f (w' (a' x) ⊗F z')
      ≡⟨ refl ⟩
       M₁ (λ p → proj₁ p (proj₂ p))  
          (f (proj₁ x , (λ x₁ → _,_ (proj₂ x x₁))) ⊗ empty)
      ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) (f (proj₁ x , (λ x₁ → _,_ (proj₂ x x₁))) ⊗ s)) (sym (M₁-id empty)) ⟩
      M₁ (λ p → proj₁ p (proj₂ p))  
         (f (proj₁ x , (λ x₁ → _,_ (proj₂ x x₁))) ⊗ (M₁ (λ s → s) empty))
      ≡⟨ refl ⟩
      M₁ (λ p → proj₁ p (proj₂ p)) 
         (f (map _,_ x) ⊗ (M₁ (λ s → s) empty))
      ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) (s ⊗ M₁ (λ s → s) empty)) (is-nat f _,_ x) ⟩
        M₁ (λ p → proj₁ p (proj₂ p)) (M₁ _,_ (f x) ⊗ M₁ (λ s → s) empty)
      ≡⟨ cong (M₁ (λ p → proj₁ p (proj₂ p))) (sym (⊗-nat _,_ (λ s → s) (f  x) empty)) ⟩
        M₁ (λ p → proj₁ p (proj₂ p))
          (M₁ (λ p → _,_ (proj₁ p) , proj₂ p) (f x ⊗ empty))
      ≡⟨ sym (M₁-∘ (λ p → proj₁ p (proj₂ p)) (λ p → _,_ (proj₁ p) , proj₂ p) (f x ⊗ empty)) ⟩
         M₁ (λ z → z) (f x ⊗ empty)
      ≡⟨ M₁-id (f x ⊗ empty)  ⟩
       f x ⊗ empty
      ≡⟨ refl ⟩
       univ f (w' (a' x)) ⊗ univ f z'
      ∎
    univ-preserves-* f (w' (a' x)) (o' x₁) = -- {!!}
       begin
        univ f (w' (a' x) ⊗F o' x₁)
       ≡⟨ refl ⟩
        f (proj₁ x , (λ x₂ → proj₂ x x₂ , x₁))
       ≡⟨ refl ⟩
         f (map (λ s → s , x₁) x)
       ≡⟨ is-nat f (λ s → s , x₁) x ⟩
           M₁ (λ s → s , x₁) (f x)
       ≡⟨ cong (M₁ (λ s → s , x₁)) (sym (⊗-right-iden (f x))) ⟩
          M₁ (λ s → s , x₁) (M₁ proj₁ (f x ⊗ unit))
       ≡⟨ sym (M₁-∘ (λ s → s , x₁) proj₁ (f x ⊗ unit)) ⟩
        M₁ (λ p → proj₁ p , x₁) (f x ⊗ unit)
       ≡⟨ ⊗-nat (λ z → z) (λ v → x₁) (f x) unit ⟩
        M₁ (λ z → z) (f x) ⊗ M₁ (λ v → x₁) unit
       ≡⟨ cong (λ s → s ⊗ M₁ (λ v → x₁) unit) (M₁-id (f x)) ⟩
        f x ⊗ M₁ (λ _ → x₁) unit
       ≡⟨ refl ⟩
        univ f (w' (a' x)) ⊗ univ f (o' x₁)
       ∎
    univ-preserves-* f (w' (a' x)) (w' x₁) = -- {!!}
      begin
       M₁ (λ p → proj₁ p (proj₂ p))
          (f (proj₁ x , (λ x₂ → _,_ (proj₂ x x₂))) ⊗ univ f (w' x₁))
      ≡⟨ refl ⟩
         M₁ (λ p → proj₁ p (proj₂ p)) 
            (f (map _,_ x) ⊗ univ f (w' x₁))
      ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) (f (map _,_ x) ⊗ s)) (sym (M₁-id (univ f (w' x₁)))) ⟩
         M₁ (λ p → proj₁ p (proj₂ p))
           (f (map _,_ x) ⊗ M₁ (λ z → z) (univ f (w' x₁)))
      ≡⟨ cong (λ s →  M₁ (λ p → proj₁ p (proj₂ p)) (s ⊗ M₁ (λ z → z) (univ f (w' x₁))) ) (is-nat f _,_ x) ⟩
        M₁ (λ p → proj₁ p (proj₂ p))
          (M₁ _,_ (f x) ⊗ M₁ (λ z → z) (univ f (w' x₁)))
      ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) s) (sym (⊗-nat _,_ (λ z → z) (f x) (univ f (w' x₁)))) ⟩
         M₁ (λ p → proj₁ p (proj₂ p))
           (M₁ (λ p → _,_ (proj₁ p) , proj₂ p) (f x ⊗ univ f (w' x₁)))
      ≡⟨ sym (M₁-∘ (λ p → proj₁ p (proj₂ p)) (λ p → _,_ (proj₁ p) , proj₂ p) (f x ⊗ univ f (w' x₁))) ⟩
         M₁ (λ s → s) (f x ⊗ univ f (w' x₁))
      ≡⟨ M₁-id (f x ⊗ univ f (w' x₁)) ⟩
        f x ⊗ univ f (w' x₁)
      ∎
    univ-preserves-* f (w' (suma1 x x₁)) z' = -- {!!}
     begin
      M₁ (λ p → proj₁ p (proj₂ p))
         (univ f (w' (suma1 (fmaps _,_ x) (_,_ x₁))) ⊗ empty)
     ≡⟨ refl ⟩ 
        M₁ (λ p → proj₁ p (proj₂ p))
           (univ f (fmapf _,_ (w' (suma1 x x₁))) ⊗ empty)
     ≡⟨ cong (λ s →  M₁ (λ p → proj₁ p (proj₂ p)) (s ⊗ empty)) (sym (univ-nat f _,_ {w' (suma1 x x₁)})) ⟩
        M₁ (λ p → proj₁ p (proj₂ p)) (M₁ _,_ (univ f (w' (suma1 x x₁))) ⊗ empty)
     ≡⟨ cong (λ s →  M₁ (λ p → proj₁ p (proj₂ p)) (M₁ _,_ (univ f (w' (suma1 x x₁))) ⊗ s )) (sym (M₁-id empty)) ⟩
        M₁ (λ p → proj₁ p (proj₂ p)) (M₁ _,_ (univ f (w' (suma1 x x₁))) ⊗ (M₁ (λ s → s) empty))
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) s) (sym (⊗-nat _,_ (λ s → s) (univ f (w' (suma1 x x₁))) empty)) ⟩
        M₁ (λ p → proj₁ p (proj₂ p))
          (M₁ (λ p → _,_ (proj₁ p) , proj₂ p)
           (univ f (w' (suma1 x x₁)) ⊗ empty))
     ≡⟨ sym (M₁-∘ (λ p → proj₁ p (proj₂ p)) (λ p → _,_ (proj₁ p) , proj₂ p) (univ f (w' (suma1 x x₁)) ⊗ empty)) ⟩
        M₁ (λ s → s) (univ f (w' (suma1 x x₁)) ⊗ empty)
     ≡⟨ M₁-id (univ f (w' (suma1 x x₁)) ⊗ empty) ⟩
       univ f (w' (suma1 x x₁)) ⊗ empty
     ∎
    univ-preserves-* f (w' (suma1 x x₁)) (o' x₂) = -- {!!}
     begin
      univ f (w' (suma1 (fmaps (λ z → z , x₂) x) (x₁ , x₂))) 
     ≡⟨ refl ⟩
      univ f (fmapf (λ z → z , x₂) (w' (suma1 x x₁)))
     ≡⟨ sym (univ-nat f (λ z → z , x₂) {w' (suma1 x x₁)}) ⟩
      M₁ (λ z → z , x₂) (univ f (w' (suma1 x x₁)))
     ≡⟨ cong (λ s → M₁ (λ z → z , x₂) s) (sym (⊗-right-iden (univ f (w' (suma1 x x₁))))) ⟩
        M₁ (λ z → z , x₂) (M₁ proj₁ (univ f (w' (suma1 x x₁)) ⊗ unit))
     ≡⟨ sym (M₁-∘ (λ z → z , x₂) proj₁ (univ f (w' (suma1 x x₁)) ⊗ unit)) ⟩
      M₁ (λ p → proj₁ p , x₂) (univ f (w' (suma1 x x₁)) ⊗ unit)
     ≡⟨ ⊗-nat (λ z → z) (λ _ → x₂) (univ f (w' (suma1 x x₁))) unit ⟩
       M₁ (λ z → z) (univ f (w' (suma1 x x₁))) ⊗ M₁ (λ _ → x₂) unit
     ≡⟨ cong (λ s → s ⊗  M₁ (λ _ → x₂) unit) (M₁-id (univ f (w' (suma1 x x₁)))) ⟩
      univ f (w' (suma1 x x₁)) ⊗ M₁ (λ _ → x₂) unit
     ∎
    univ-preserves-* f (w' (suma1 x x₁)) (w' x₂) = --{!!}
     begin
      M₁ (λ p → proj₁ p (proj₂ p))
         (univ f (w' (suma1 (fmaps _,_ x) (_,_ x₁))) ⊗ univ f (w' x₂))
     ≡⟨ refl ⟩
       M₁ (λ p → proj₁ p (proj₂ p))
         (univ f (fmapf _,_ (w' (suma1 x x₁))) ⊗ univ f (w' x₂))
     ≡⟨ cong₂ (λ s d → M₁ (λ p → proj₁ p (proj₂ p)) (s ⊗ d)) (sym (univ-nat f _,_ {w' (suma1 x x₁)})) (sym (M₁-id (univ f (w' x₂)))) ⟩
        M₁ (λ p → proj₁ p (proj₂ p))
          (M₁ _,_ (univ f (w' (suma1 x x₁))) ⊗ M₁ (λ z → z) (univ f (w' x₂)))
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) s) (sym (⊗-nat _,_ (λ z → z) (univ f (w' (suma1 x x₁))) (univ f (w' x₂)))) ⟩
        M₁ (λ p → proj₁ p (proj₂ p))
          (M₁ (λ p → _,_ (proj₁ p) , proj₂ p)
           (univ f (w' (suma1 x x₁)) ⊗ univ f (w' x₂)))
     ≡⟨ sym (M₁-∘ (λ p → proj₁ p (proj₂ p)) (λ p → _,_ (proj₁ p) , proj₂ p) (univ f (w' (suma1 x x₁)) ⊗ univ f (w' x₂))) ⟩
         M₁ (λ z → z) (univ f (w' (suma1 x x₁)) ⊗ univ f (w' x₂))
     ≡⟨ M₁-id (univ f (w' (suma1 x x₁)) ⊗ univ f (w' x₂)) ⟩
      univ f (w' (suma1 x x₁)) ⊗ univ f (w' x₂)
     ∎
    univ-preserves-* f (w' (suma2 x x₁)) z' = --  {! !}
     begin
      M₁ (λ p → proj₁ p (proj₂ p))
         (univ f (w' (suma2 (fmaps _,_ x) (fmapw _,_ x₁))) ⊗ empty)
     ≡⟨ refl ⟩
       M₁ (λ p → proj₁ p (proj₂ p))
         (univ f (fmapf _,_ (w' (suma2 x x₁))) ⊗ empty)
     ≡⟨ cong₂ (λ s d →  M₁ (λ p → proj₁ p (proj₂ p)) (s ⊗ d)) (sym (univ-nat f _,_ {w' (suma2 x x₁)})) (sym (M₁-id empty)) ⟩
        M₁ (λ p → proj₁ p (proj₂ p))
          (M₁ _,_ (univ f (w' (suma2 x x₁))) ⊗ M₁ (λ z → z) empty)
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) s) (sym (⊗-nat _,_ (λ z → z) (univ f (w' (suma2 x x₁))) empty)) ⟩
       M₁ (λ p → proj₁ p (proj₂ p))
         (M₁ (λ p → _,_ (proj₁ p) , proj₂ p)
          (univ f (w' (suma2 x x₁)) ⊗ empty))
     ≡⟨ sym (M₁-∘ (λ p → proj₁ p (proj₂ p)) (λ p → _,_ (proj₁ p) , proj₂ p) (univ f (w' (suma2 x x₁)) ⊗ empty)) ⟩
       M₁ (λ z → z) (univ f (w' (suma2 x x₁)) ⊗ empty)
     ≡⟨ M₁-id (univ f (w' (suma2 x x₁)) ⊗ empty) ⟩
      univ f (w' (suma2 x x₁)) ⊗ empty
     ∎
    univ-preserves-* f (w' (suma2 x x₁)) (o' x₂) = -- {!!}
     begin
      univ f  (w' (suma2 (fmaps (λ z → z , x₂) x) (fmapw (λ z → z , x₂) x₁)))
     ≡⟨ refl ⟩
       univ f  (fmapf (λ z → z , x₂) (w' (suma2 x x₁)))
     ≡⟨ sym (univ-nat f (λ z → z , x₂) {w' (suma2 x x₁)}) ⟩
       M₁ (λ z → z , x₂) (univ f (w' (suma2 x x₁)))
     ≡⟨ cong (λ s → M₁ (λ z → z , x₂) s) (sym (⊗-right-iden (univ f (w' (suma2 x x₁))))) ⟩
       M₁ (λ z → z , x₂) (M₁ proj₁ (univ f (w' (suma2 x x₁)) ⊗ unit))
     ≡⟨ sym (M₁-∘ (λ z → z , x₂) proj₁ (univ f (w' (suma2 x x₁)) ⊗ unit)) ⟩
       M₁ (λ z → proj₁ z , x₂) (univ f (w' (suma2 x x₁)) ⊗ unit)
     ≡⟨ ⊗-nat (λ v → v) (λ v → x₂) (univ f (w' (suma2 x x₁))) unit ⟩
       M₁ (λ v → v) (univ f (w' (suma2 x x₁))) ⊗ M₁ (λ v → x₂) unit
     ≡⟨ cong (λ s → s ⊗ M₁ (λ v → x₂) unit) (M₁-id (univ f (w' (suma2 x x₁)))) ⟩
      univ f (w' (suma2 x x₁)) ⊗ M₁ (λ _ → x₂) unit
     ∎
    univ-preserves-* f (w' (suma2 x x₁)) (w' x₂) = 
     begin
      M₁ (λ p → proj₁ p (proj₂ p))
         (univ f (w' (suma2 (fmaps _,_ x) (fmapw _,_ x₁))) ⊗ univ f (w' x₂))
     ≡⟨ refl ⟩ 
      M₁ (λ p → proj₁ p (proj₂ p))
         (univ f (fmapf _,_ (w' (suma2 x x₁))) ⊗ univ f (w' x₂))
     ≡⟨ cong₂ (λ s d →  M₁ (λ p → proj₁ p (proj₂ p)) (s ⊗ d)) (sym (univ-nat f _,_ {w' (suma2 x x₁)})) (sym (M₁-id (univ f (w' x₂)))) ⟩
       M₁ (λ p → proj₁ p (proj₂ p))
         (M₁ _,_ (univ f (w' (suma2 x x₁))) ⊗ M₁ (λ z → z) (univ f (w' x₂)))
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) s) (sym (⊗-nat _,_ (λ z → z) (univ f (w' (suma2 x x₁))) (univ f (w' x₂)))) ⟩
        M₁ (λ p → proj₁ p (proj₂ p))
          (M₁ (λ p → _,_ (proj₁ p) , proj₂ p)
           (univ f (w' (suma2 x x₁)) ⊗ univ f (w' x₂)))
     ≡⟨ sym (M₁-∘ (λ p → proj₁ p (proj₂ p)) (λ p → _,_ (proj₁ p) , proj₂ p) (univ f (w' (suma2 x x₁)) ⊗ univ f (w' x₂))) ⟩
      M₁ (λ s → s) (univ f (w' (suma2 x x₁)) ⊗ univ f (w' x₂))
     ≡⟨ M₁-id (univ f (w' (suma2 x x₁)) ⊗ univ f (w' x₂)) ⟩
      univ f (w' (suma2 x x₁)) ⊗ univ f (w' x₂)
     ∎
    univ-preserves-* f (w' (prod1 (a' x))) y = -- {!!}
      begin
       M₁ (λ p → proj₁ p (proj₂ p))
           (f (proj₁ x , (λ x₁ p → proj₂ x x₁ (proj₁ p) , proj₂ p)) ⊗ empty)
      ≡⟨ refl ⟩
       M₁ (λ p → proj₁ p (proj₂ p)) 
           (univ f (fmapf (λ x₁ p → x₁ (proj₁ p) , (proj₂ p)) (w' (a' x))) ⊗ empty)
      ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) (s ⊗ empty)) (sym (univ-nat f (λ x₁ p → x₁ (proj₁ p) , (proj₂ p)) {w' (a' x)})) ⟩
         M₁ (λ p → proj₁ p (proj₂ p))
           (M₁ (λ x₁ p → x₁ (proj₁ p) , proj₂ p) (univ f (w' (a' x))) ⊗ empty)
      ≡⟨ cong (λ s →  M₁ (λ p → proj₁ p (proj₂ p))
           (M₁ (λ x₁ p → x₁ (proj₁ p) , proj₂ p) (univ f (w' (a' x))) ⊗ s)) (sym (M₁-id empty)) ⟩
         M₁ (λ p → proj₁ p (proj₂ p))
           (M₁ (λ x₁ p → x₁ (proj₁ p) , proj₂ p) (univ f (w' (a' x))) ⊗
            M₁ (λ z → z) empty)
      ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) s) (sym (⊗-nat (λ x₁ p → x₁ (proj₁ p) , proj₂ p) (λ z → z) (univ f (w' (a' x))) empty)) ⟩
        M₁ (λ p → proj₁ p (proj₂ p))
          (M₁ (λ p → (λ p₁ → proj₁ p (proj₁ p₁) , proj₂ p₁) , proj₂ p)
           (univ f (w' (a' x)) ⊗ empty))
      ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p))
          (M₁ (λ p → (λ p₁ → proj₁ p (proj₁ p₁) , proj₂ p₁) , proj₂ p)
           (univ f (w' (a' x)) ⊗ s))) (sym (⊗-abs (univ f y))) ⟩
         M₁ (λ p → proj₁ p (proj₂ p))
           (M₁ (λ p → (λ p₁ → proj₁ p (proj₁ p₁) , proj₂ p₁) , proj₂ p)
            (univ f (w' (a' x)) ⊗ (empty ⊗ univ f y))) 
      ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p))
           (M₁ (λ p → (λ p₁ → proj₁ p (proj₁ p₁) , proj₂ p₁) , proj₂ p) s)) (sym (⊗-assoc (univ f (w' (a' x))) empty (univ f y))) ⟩
         M₁ (λ p → proj₁ p (proj₂ p))
           (M₁ (λ p → (λ p₁ → proj₁ p (proj₁ p₁) , proj₂ p₁) , proj₂ p)
            (M₁ (λ x₁ → proj₁ (proj₁ x₁) , proj₂ (proj₁ x₁) , proj₂ x₁)
             ((univ f (w' (a' x)) ⊗ empty) ⊗ univ f y)))
      ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) s) (sym (M₁-∘ (λ p → (λ p₁ → proj₁ p (proj₁ p₁) , proj₂ p₁) , proj₂ p) ((λ x₁ → proj₁ (proj₁ x₁) , proj₂ (proj₁ x₁) , proj₂ x₁)) ((univ f (w' (a' x)) ⊗ empty) ⊗ univ f y))) ⟩
         M₁ (λ p → proj₁ p (proj₂ p))
           (M₁
            (λ z →
               (λ p₁ →
                  proj₁ (proj₁ (proj₁ z) , proj₂ (proj₁ z) , proj₂ z) (proj₁ p₁) ,
                  proj₂ p₁)
               , proj₂ (proj₁ (proj₁ z) , proj₂ (proj₁ z) , proj₂ z))
            ((univ f (w' (a' x)) ⊗ empty) ⊗ univ f y))
      ≡⟨ sym (M₁-∘ (λ p → proj₁ p (proj₂ p)) (λ z →
                                                 (λ p₁ →
                                                    proj₁ (proj₁ (proj₁ z) , proj₂ (proj₁ z) , proj₂ z) (proj₁ p₁) ,
                                                    proj₂ p₁)
                                                 , proj₂ (proj₁ (proj₁ z) , proj₂ (proj₁ z) , proj₂ z)) ((univ f (w' (a' x)) ⊗ empty) ⊗ univ f y)) ⟩
       M₁ (λ p → proj₁ (proj₁ p) (proj₂ (proj₁ p)) , proj₂ p) ((f x ⊗ empty) ⊗ univ f y)
      ≡⟨ ⊗-nat (λ p → proj₁ p (proj₂ p)) (λ s → s) (f x ⊗ empty) (univ f y) ⟩
       M₁ (λ p → proj₁ p (proj₂ p)) (f x ⊗ empty) ⊗ M₁ (λ s → s) (univ f y)
      ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) (f x ⊗ empty) ⊗ s) (M₁-id (univ f y)) ⟩
       M₁ (λ p → proj₁ p (proj₂ p)) (f x ⊗ empty) ⊗ univ f y
      ∎
    univ-preserves-* f (w' (prod1 (suma1 x x₁))) y = -- {!!}
      begin 
       univ f (w' (prod1 (suma1 x x₁)) ⊗F y)
      ≡⟨ refl ⟩
       M₁ (λ p → proj₁ p (proj₂ p)) (univ f (fmapf ((λ f₁ p → f₁ (proj₁ p) , proj₂ p)) (w' (suma1 x x₁))) ⊗ univ f z')
      ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) (s ⊗ univ f z')) (sym (univ-nat f (λ f₁ p → f₁ (proj₁ p) , proj₂ p) {w' (suma1 x x₁)})) ⟩
         M₁ (λ p → proj₁ p (proj₂ p))
           (M₁ (λ f₁ p → f₁ (proj₁ p) , proj₂ p) (univ f (w' (suma1 x x₁))) ⊗
            univ f z')
      ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p))
           (M₁ (λ f₁ p → f₁ (proj₁ p) , proj₂ p) (univ f (w' (suma1 x x₁))) ⊗ s)) (sym (M₁-id (univ f z'))) ⟩
        M₁ (λ p → proj₁ p (proj₂ p))
          (M₁ (λ f₁ p → f₁ (proj₁ p) , proj₂ p) (univ f (w' (suma1 x x₁))) ⊗ M₁ (λ z → z) (univ f z'))
      ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) s) (sym (⊗-nat (λ f₁ p → f₁ (proj₁ p) , proj₂ p) (λ z → z) (univ f (w' (suma1 x x₁))) (univ f z'))) ⟩
         M₁ (λ p → proj₁ p (proj₂ p))
           (M₁ (λ p → (λ p₁ → proj₁ p (proj₁ p₁) , proj₂ p₁) , proj₂ p)
            (univ f (w' (suma1 x x₁)) ⊗ univ f z'))
      ≡⟨ sym (M₁-∘ ((λ p → proj₁ p (proj₂ p))) ((λ p → (λ p₁ → proj₁ p (proj₁ p₁) , proj₂ p₁) , proj₂ p)) (univ f (w' (suma1 x x₁)) ⊗ univ f z')) ⟩
         M₁ (λ z → proj₁ z (proj₁ (proj₂ z)) , proj₂ (proj₂ z)) (univ f (w' (suma1 x x₁)) ⊗ empty)
      ≡⟨ cong (λ s →  M₁ (λ z → proj₁ z (proj₁ (proj₂ z)) , proj₂ (proj₂ z)) (univ f (w' (suma1 x x₁)) ⊗ s)) (sym (⊗-abs (univ f y))) ⟩
          M₁ (λ z → proj₁ z (proj₁ (proj₂ z)) , proj₂ (proj₂ z))
            (univ f (w' (suma1 x x₁)) ⊗ (empty ⊗ univ f y))
      ≡⟨ cong (λ s → M₁ (λ z → proj₁ z (proj₁ (proj₂ z)) , proj₂ (proj₂ z)) s) (sym (⊗-assoc (univ f (w' (suma1 x x₁))) empty (univ f y))) ⟩
         M₁ (λ z → proj₁ z (proj₁ (proj₂ z)) , proj₂ (proj₂ z))
           (M₁ (λ x₂ → proj₁ (proj₁ x₂) , proj₂ (proj₁ x₂) , proj₂ x₂)
            ((univ f (w' (suma1 x x₁)) ⊗ empty) ⊗ univ f y))
      ≡⟨ sym (M₁-∘ (λ z → proj₁ z (proj₁ (proj₂ z)) , proj₂ (proj₂ z)) (λ x₂ → proj₁ (proj₁ x₂) , proj₂ (proj₁ x₂) , proj₂ x₂) ((univ f (w' (suma1 x x₁)) ⊗ empty) ⊗ univ f y)) ⟩
         M₁ (λ p → proj₁ (proj₁ p) (proj₂ (proj₁ p)) , proj₂ p)
           ((univ f (w' (suma1 x x₁)) ⊗ empty) ⊗ univ f y)
      ≡⟨ ⊗-nat (λ p → proj₁ p (proj₂ p)) (λ z → z) (univ f (w' (suma1 x x₁)) ⊗ empty) (univ f y) ⟩
        M₁ (λ p → proj₁ p (proj₂ p)) (univ f (w' (suma1 x x₁)) ⊗ empty) ⊗ M₁ (λ z → z) (univ f y)
      ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) (univ f (w' (suma1 x x₁)) ⊗ empty) ⊗ s) (M₁-id (univ f y)) ⟩
       M₁ (λ p → proj₁ p (proj₂ p)) (univ f (w' (suma1 x x₁)) ⊗ empty) ⊗ univ f y
      ∎
    univ-preserves-* f (w' (prod1 (suma2 x x₁))) y = -- {!!}
     begin
      M₁ (λ p → proj₁ p (proj₂ p))
      (univ f (fmapf (λ f₁ p → f₁ (proj₁ p) , proj₂ p) (w' (suma2 x x₁))) ⊗ empty)
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) (univ f (fmapf (λ f₁ p → f₁ (proj₁ p) , proj₂ p) (w' (suma2 x x₁))) ⊗ s)) (sym (M₁-id empty)) ⟩
      M₁ (λ p → proj₁ p (proj₂ p))
      (univ f (fmapf (λ f₁ p → f₁ (proj₁ p) , proj₂ p) (w' (suma2 x x₁))) ⊗ M₁ (λ s → s) empty)
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) (s ⊗ M₁ (λ s → s) empty)) (sym (univ-nat f (λ f₁ p → f₁ (proj₁ p) , proj₂ p) {w' (suma2 x x₁)})) ⟩ 
        M₁ (λ p → proj₁ p (proj₂ p))
          (M₁ (λ f₁ p → f₁ (proj₁ p) , proj₂ p) (univ f (w' (suma2 x x₁))) ⊗
           M₁ (λ s → s) empty)
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) s) (sym (⊗-nat (λ f₁ p → f₁ (proj₁ p) , proj₂ p) (λ s → s) (univ f (w' (suma2 x x₁))) empty)) ⟩
         M₁ (λ p → proj₁ p (proj₂ p))
           (M₁ (λ p → (λ p₁ → proj₁ p (proj₁ p₁) , proj₂ p₁) , proj₂ p)
            (univ f (w' (suma2 x x₁)) ⊗ empty))
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p))
           (M₁ (λ p → (λ p₁ → proj₁ p (proj₁ p₁) , proj₂ p₁) , proj₂ p)
            (univ f (w' (suma2 x x₁)) ⊗ s))) (sym (⊗-abs (univ f y))) ⟩
        M₁ (λ p → proj₁ p (proj₂ p))
          (M₁ (λ p → (λ p₁ → proj₁ p (proj₁ p₁) , proj₂ p₁) , proj₂ p)
           (univ f (w' (suma2 x x₁)) ⊗ (empty ⊗ univ f y)))
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p))
          (M₁ (λ p → (λ p₁ → proj₁ p (proj₁ p₁) , proj₂ p₁) , proj₂ p) s)) (sym (⊗-assoc (univ f (w' (suma2 x x₁))) empty (univ f y))) ⟩
       M₁ (λ p → proj₁ p (proj₂ p))
         (M₁ (λ p → (λ p₁ → proj₁ p (proj₁ p₁) , proj₂ p₁) , proj₂ p)
          (M₁ (λ x₂ → proj₁ (proj₁ x₂) , proj₂ (proj₁ x₂) , proj₂ x₂)
           ((univ f (w' (suma2 x x₁)) ⊗ empty) ⊗ univ f y)))
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) s) (sym (M₁-∘ (λ p → (λ p₁ → proj₁ p (proj₁ p₁) , proj₂ p₁) , proj₂ p) (λ x₂ → proj₁ (proj₁ x₂) , proj₂ (proj₁ x₂) , proj₂ x₂) ((univ f (w' (suma2 x x₁)) ⊗ empty) ⊗ univ f y))) ⟩
       M₁ (λ p → proj₁ p (proj₂ p))
         (M₁
          (λ z →
             (λ p₁ →
                proj₁ (proj₁ (proj₁ z) , proj₂ (proj₁ z) , proj₂ z) (proj₁ p₁) ,
                proj₂ p₁)
             , proj₂ (proj₁ (proj₁ z) , proj₂ (proj₁ z) , proj₂ z))
          ((univ f (w' (suma2 x x₁)) ⊗ empty) ⊗ univ f y))
     ≡⟨ sym (M₁-∘ (λ p → proj₁ p (proj₂ p)) (λ z →
                                                (λ p₁ →
                                                   proj₁ (proj₁ (proj₁ z) , proj₂ (proj₁ z) , proj₂ z) (proj₁ p₁) ,
                                                   proj₂ p₁)
                                                , proj₂ (proj₁ (proj₁ z) , proj₂ (proj₁ z) , proj₂ z)) ((univ f (w' (suma2 x x₁)) ⊗ empty) ⊗ univ f y)) ⟩
       M₁ (λ p → proj₁ (proj₁ p) (proj₂ (proj₁ p)) , proj₂ p)
         ((univ f (w' (suma2 x x₁)) ⊗ empty) ⊗ univ f y)
     ≡⟨ ⊗-nat (λ p → proj₁ p (proj₂ p)) (λ s → s) (univ f (w' (suma2 x x₁)) ⊗ empty) (univ f y) ⟩
      M₁ (λ p → proj₁ p (proj₂ p)) (univ f (w' (suma2 x x₁)) ⊗ empty) ⊗ M₁ (λ s → s) (univ f y)
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) (univ f (w' (suma2 x x₁)) ⊗ empty) ⊗ s) (M₁-id (univ f y)) ⟩
      M₁ (λ p → proj₁ p (proj₂ p)) (univ f (w' (suma2 x x₁)) ⊗ empty) ⊗ univ f y
     ∎

    univ-preserves-* f (w' (prod2 (a' x) x₁)) y = 
     begin
      univ f (w' (prod2 (a' x) x₁) ⊗F y)
     ≡⟨ refl ⟩ 
      univ f (w' (prod2 (fmapp ((λ f p → (f (proj₁ p)) , (proj₂ p))) (a' x)) (x₁ ⋆E y)))
     ≡⟨ refl ⟩
       M₁ (λ p → proj₁ p (proj₂ p))
       (f (proj₁ x , (λ x₂ p → proj₂ x x₂ (proj₁ p) , proj₂ p)) ⊗
       univ f (w' (x₁ ⋆E y)))
     ≡⟨ refl ⟩ 
       M₁ (λ p → proj₁ p (proj₂ p))
       (univ f (fmapf (λ x₂ p → (x₂ (proj₁ p)) , (proj₂ p)) (w' (a' x))) ⊗ univ f (w' (x₁ ⋆E y)))
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p))
       (s ⊗ univ f (w' (x₁ ⋆E y)))) (sym (univ-nat f (λ x₂ p → (x₂ (proj₁ p)) , (proj₂ p)) {w' (a' x)})) ⟩
        M₁ (λ p → proj₁ p (proj₂ p))
          (M₁ (λ v v₁ → v (proj₁ v₁) , proj₂ v₁) (univ f (w' (a' x))) ⊗
           univ f (w' (x₁ ⋆E y)))
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p))
      (M₁ (λ v v₁ → v (proj₁ v₁) , proj₂ v₁) (univ f (w' (a' x))) ⊗ s)) (sym (M₁-id (univ f (w' (x₁ ⋆E y))))) ⟩
         M₁ (λ p → proj₁ p (proj₂ p))
           (M₁ (λ v v₁ → v (proj₁ v₁) , proj₂ v₁)
            (univ f (w' (a' x)))
            ⊗ M₁ (λ z → z) (univ f (w' (x₁ ⋆E y))))
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) s) (sym (⊗-nat (λ v v₁ → v (proj₁ v₁) , proj₂ v₁) (λ z → z) (univ f (w' (a' x))) (univ f (w' (x₁ ⋆E y))))) ⟩
        M₁ (λ p → proj₁ p (proj₂ p))
          (M₁ (λ p → (λ v₁ → proj₁ p (proj₁ v₁) , proj₂ v₁) , proj₂ p)
           (univ f (w' (a' x)) ⊗ univ f (w' (x₁ ⋆E y))))
     ≡⟨ sym (M₁-∘ (λ p → proj₁ p (proj₂ p)) (λ p → (λ v₁ → proj₁ p (proj₁ v₁) , proj₂ v₁) , proj₂ p) (univ f (w' (a' x)) ⊗ univ f (w' (x₁ ⋆E y)))) ⟩
        M₁ (λ x₂ → proj₁ x₂ (proj₁ (proj₂ x₂)) , proj₂ (proj₂ x₂))
          (univ f (w' (a' x)) ⊗ univ f (w' x₁ ⊗F y))
     ≡⟨ refl ⟩ 
        M₁ (λ x₂ → proj₁ x₂ (proj₁ (proj₂ x₂)) , proj₂ (proj₂ x₂))
          (f x ⊗ univ f (w' x₁ ⊗F y))
     ≡⟨ cong (λ s → M₁ (λ x₂ → proj₁ x₂ (proj₁ (proj₂ x₂)) , proj₂ (proj₂ x₂))
         (f x ⊗ s)) (univ-preserves-* f (w' x₁) y) ⟩
       M₁ (λ x₂ → proj₁ x₂ (proj₁ (proj₂ x₂)) , proj₂ (proj₂ x₂))
         (f x ⊗ (univ f (w' x₁) ⊗ univ f y))
     ≡⟨ cong (λ s → M₁ (λ x₂ → proj₁ x₂ (proj₁ (proj₂ x₂)) , (proj₂ (proj₂ x₂))) s) (sym (⊗-assoc (f x) (univ f (w' x₁)) (univ f y))) ⟩
       M₁ (λ x₂ → proj₁ x₂ (proj₁ (proj₂ x₂)) , (proj₂ (proj₂ x₂))) (M₁ ((λ x₃ → proj₁ (proj₁ x₃) , proj₂ (proj₁ x₃) , proj₂ x₃)) ((f x ⊗ univ f (w' x₁)) ⊗ univ f y))
     ≡⟨ sym (M₁-∘ (λ x₂ → proj₁ x₂ (proj₁ (proj₂ x₂)) , proj₂ (proj₂ x₂)) (λ x₃ → proj₁ (proj₁ x₃) , proj₂ (proj₁ x₃) , proj₂ x₃) ((f x ⊗ univ f (w' x₁)) ⊗ univ f y)) ⟩
       M₁ (λ p → proj₁ (proj₁ p) (proj₂ (proj₁ p)) , proj₂ p)
         ((f x ⊗ univ f (w' x₁)) ⊗ univ f y)
     ≡⟨ ⊗-nat (λ p → proj₁ p (proj₂ p)) (λ s → s) (f x ⊗ univ f (w' x₁)) (univ f y) ⟩
       M₁ (λ p → proj₁ p (proj₂ p)) (f x ⊗ univ f (w' x₁)) ⊗ M₁ (λ s → s) (univ f y)
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) (f x ⊗ univ f (w' x₁)) ⊗ s) (M₁-id (univ f y)) ⟩
       M₁ (λ p → proj₁ p (proj₂ p)) (f x ⊗ univ f (w' x₁)) ⊗ univ f y
     ∎
    univ-preserves-* f (w' (prod2 (suma1 x x₁) x₂)) y = 
     begin
      M₁ (λ p → proj₁ p (proj₂ p))
      (univ f (fmapf (λ f₁ p → f₁ (proj₁ p) , proj₂ p)
       (w' (suma1 x x₁))) ⊗ univ f (w' (x₂ ⋆E y)))
      ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p))
      (univ f (fmapf (λ f₁ p → f₁ (proj₁ p) , proj₂ p)
       (w' (suma1 x x₁))) ⊗ s)) (sym (M₁-id (univ f (w' (x₂ ⋆E y))))) ⟩
          M₁ (λ p → proj₁ p (proj₂ p))
            (univ f 
             (fmapf (λ f₁ p → f₁ (proj₁ p) , proj₂ p) (w' (suma1 x x₁)))
             ⊗ M₁ (λ z → z) (univ f (w' (x₂ ⋆E y))))
      ≡⟨ cong (λ d → M₁ (λ p → proj₁ p (proj₂ p))
            (d ⊗ M₁ (λ z → z) (univ f (w' (x₂ ⋆E y))))) (sym (univ-nat f (λ f₁ p → f₁ (proj₁ p) , proj₂ p) {w' (suma1 x x₁)})) ⟩
          M₁ (λ p → proj₁ p (proj₂ p))
            (M₁ (λ f₁ p → f₁ (proj₁ p) , proj₂ p) 
             (univ f (w' (suma1 x x₁)))
             ⊗ M₁ (λ z → z) (univ f (w' (x₂ ⋆E y))))
      ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) s) (sym (⊗-nat (λ f₁ p → f₁ (proj₁ p) , proj₂ p) (λ z → z) (univ f (w' (suma1 x x₁))) (univ f (w' (x₂ ⋆E y))))) ⟩
         M₁ (λ p → proj₁ p (proj₂ p))
           (M₁ (λ p → (λ p₁ → proj₁ p (proj₁ p₁) , proj₂ p₁) , proj₂ p)
            (univ f (w' (suma1 x x₁)) ⊗ univ f (w' (x₂ ⋆E y))))
      ≡⟨ sym (M₁-∘ (λ p → proj₁ p (proj₂ p)) (λ p → (λ p₁ → proj₁ p (proj₁ p₁) , proj₂ p₁) , proj₂ p) (univ f (w' (suma1 x x₁)) ⊗ univ f (w' (x₂ ⋆E y)))) ⟩
         M₁ (λ x₃ → proj₁ x₃ (proj₁ (proj₂ x₃)) , proj₂ (proj₂ x₃))
           (univ f (w' (suma1 x x₁)) ⊗ (univ f (w' (x₂ ⋆E y))))
      ≡⟨ cong (λ s → M₁ (λ x₃ → proj₁ x₃ (proj₁ (proj₂ x₃)) , proj₂ (proj₂ x₃)) (univ f (w' (suma1 x x₁)) ⊗ s)) (univ-preserves-* f (w' x₂) y) ⟩
         M₁ (λ x₃ → proj₁ x₃ (proj₁ (proj₂ x₃)) , proj₂ (proj₂ x₃))
           (univ f (w' (suma1 x x₁)) ⊗ (univ f (w' x₂) ⊗ univ f y))
      ≡⟨ cong (λ s → M₁ (λ x₃ → (proj₁ x₃ (proj₁ (proj₂ x₃))) , (proj₂ (proj₂ x₃))) s) (sym (⊗-assoc (univ f (w' (suma1 x x₁))) (univ f (w' x₂)) (univ f y))) ⟩
          M₁ (λ x₃ → (proj₁ x₃ (proj₁ (proj₂ x₃))) , (proj₂ (proj₂ x₃)))
            (M₁ (λ x₄ → proj₁ (proj₁ x₄) , proj₂ (proj₁ x₄) , proj₂ x₄)
             ((univ f (w' (suma1 x x₁)) ⊗ univ f (w' x₂)) ⊗ univ f y))
      ≡⟨ sym (M₁-∘ (λ x₃ → proj₁ x₃ (proj₁ (proj₂ x₃)) , proj₂ (proj₂ x₃)) (λ x₄ → proj₁ (proj₁ x₄) , proj₂ (proj₁ x₄) , proj₂ x₄) ((univ f (w' (suma1 x x₁)) ⊗ univ f (w' x₂)) ⊗ univ f y)) ⟩
         M₁ (λ p → proj₁ (proj₁ p) (proj₂ (proj₁ p)) , proj₂ p)
           ((univ f (w' (suma1 x x₁)) ⊗ univ f (w' x₂)) ⊗ univ f y)
      ≡⟨ ⊗-nat (λ p → proj₁ p (proj₂ p)) (λ s → s) (univ f (w' (suma1 x x₁)) ⊗ univ f (w' x₂)) (univ f y) ⟩
       M₁ (λ p → proj₁ p (proj₂ p))
      (univ f (w' (suma1 x x₁)) ⊗ univ f (w' x₂))
      ⊗ M₁ (λ s → s) (univ f y)
      ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p))
      (univ f (w' (suma1 x x₁)) ⊗ univ f (w' x₂)) ⊗ s) (M₁-id (univ f y)) ⟩
      M₁ (λ p → proj₁ p (proj₂ p))
      (univ f (w' (suma1 x x₁)) ⊗ univ f (w' x₂))
      ⊗ univ f y
     ∎
    univ-preserves-* f (w' (prod2 (suma2 x x₁) x₂)) y = 
     begin
      M₁ (λ p → proj₁ p (proj₂ p))
       (univ f (fmapf (λ f₁ p → f₁ (proj₁ p) , proj₂ p) 
                 (w' (suma2 x x₁))) ⊗ univ f (w' (x₂ ⋆E y)))
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p))
       (univ f (fmapf (λ f₁ p → f₁ (proj₁ p) , proj₂ p) 
                 (w' (suma2 x x₁))) ⊗ s)) (sym (M₁-id (univ f (w' (x₂ ⋆E y))))) ⟩ 
        M₁ (λ p → proj₁ p (proj₂ p))
       (univ f (fmapf (λ f₁ p → f₁ (proj₁ p) , proj₂ p) 
                 (w' (suma2 x x₁))) ⊗ M₁ (λ s → s) (univ f (w' (x₂ ⋆E y))))
     ≡⟨ cong (λ d → M₁ (λ p → proj₁ p (proj₂ p))
          (d ⊗ M₁ (λ s → s) (univ f (w' (x₂ ⋆E y))))) (sym (univ-nat f (λ f₁ p → f₁ (proj₁ p) , proj₂ p) {w' (suma2 x x₁)})) ⟩
        M₁ (λ p → proj₁ p (proj₂ p))
          (M₁ (λ f₁ p → f₁ (proj₁ p) , proj₂ p) (univ f (w' (suma2 x x₁))) ⊗ M₁ (λ s → s) (univ f (w' (x₂ ⋆E y))))
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p)) s) (sym (⊗-nat (λ f₁ p → f₁ (proj₁ p) , proj₂ p) (λ s → s) (univ f (w' (suma2 x x₁))) (univ f (w' (x₂ ⋆E y))))) ⟩
        M₁ (λ p → proj₁ p (proj₂ p))
          (M₁ (λ p → (λ p₁ → proj₁ p (proj₁ p₁) , proj₂ p₁) , proj₂ p)
           (univ f (w' (suma2 x x₁)) ⊗ univ f (w' (x₂ ⋆E y))))
     ≡⟨ sym (M₁-∘ (λ p → proj₁ p (proj₂ p)) (λ p → (λ p₁ → proj₁ p (proj₁ p₁) , proj₂ p₁) , proj₂ p) (univ f (w' (suma2 x x₁)) ⊗ univ f (w' (x₂ ⋆E y)))) ⟩
       M₁ (λ x₃ → proj₁ x₃ (proj₁ (proj₂ x₃)) , proj₂ (proj₂ x₃))
             (univ f (w' (suma2 x x₁)) ⊗ univ f (w' (x₂ ⋆E y)))
     ≡⟨ cong (λ s → M₁ (λ x₃ → proj₁ x₃ (proj₁ (proj₂ x₃)) , proj₂ (proj₂ x₃)) (univ f (w' (suma2 x x₁)) ⊗ s)) (univ-preserves-* f (w' x₂)  y) ⟩
         M₁ (λ x₃ → proj₁ x₃ (proj₁ (proj₂ x₃)) , proj₂ (proj₂ x₃)) (univ f (w' (suma2 x x₁)) ⊗ (univ f (w' x₂) ⊗ univ f y))
     ≡⟨ cong (λ s → M₁ (λ x₃ → (proj₁ x₃ (proj₁ (proj₂ x₃))) , proj₂ (proj₂ x₃)) s) (sym (⊗-assoc (univ f (w' (suma2 x x₁))) (univ f (w' x₂) ) (univ f y))) ⟩
         M₁ (λ x₃ → (proj₁ x₃ (proj₁ (proj₂ x₃))) , proj₂ (proj₂ x₃)) (M₁ ((λ x₄ → proj₁ (proj₁ x₄) , proj₂ (proj₁ x₄) , proj₂ x₄)) ((univ f (w' (suma2 x x₁)) ⊗ univ f (w' x₂)) ⊗ univ f y))
     ≡⟨ sym (M₁-∘ (λ x₃ → proj₁ x₃ (proj₁ (proj₂ x₃)) , proj₂ (proj₂ x₃)) (λ x₄ → proj₁ (proj₁ x₄) , proj₂ (proj₁ x₄) , proj₂ x₄) ((univ f (w' (suma2 x x₁)) ⊗ univ f (w' x₂)) ⊗ univ f y)) ⟩
        M₁ (λ p → proj₁ (proj₁ p) (proj₂ (proj₁ p)) , proj₂ p)
          ((univ f (w' (suma2 x x₁)) ⊗ univ f (w' x₂)) ⊗ univ f y)
     ≡⟨ ⊗-nat (λ p → proj₁ p (proj₂ p)) (λ s → s) (univ f (w' (suma2 x x₁)) ⊗ univ f (w' x₂)) (univ f y) ⟩
       M₁ (λ p → proj₁ p (proj₂ p))
      (univ f (w' (suma2 x x₁)) ⊗ univ f (w' x₂))
        ⊗ M₁ (λ s → s) (univ f y)
     ≡⟨ cong (λ s → M₁ (λ p → proj₁ p (proj₂ p))
      (univ f (w' (suma2 x x₁)) ⊗ univ f (w' x₂)) ⊗ s) (M₁-id (univ f y)) ⟩
      M₁ (λ p → proj₁ p (proj₂ p))
      (univ f (w' (suma2 x x₁)) ⊗ univ f (w' x₂))
      ⊗ univ f y
     ∎ 
   
    -- De todo lo anterior, tenemos que univ f es un homomorfismo de dioides.
    univ-homo : {C : Cont} → (∀ {X} → ⟦ C ⟧ X → M₀ X) → DioidMorphism (TF-Dioid C) D
    univ-homo {C} f = record
                    { fun = univ f
                    ; fun-nat = λ g x → sym (univ-nat {C} f g {x})
                    ; preserves-+ = univ-preserves-+ f
                    ; preserves-* = univ-preserves-* f
                    ; preserves-0 = univ-preserves-0 f 
                    ; preserves-1 = univ-preserves-1 f
                    }


    -- Definimos entonces, la función que inyecta elementos en el libre.
    F-lift : {C : Cont} {X : Set} (x : ⟦ C ⟧ X) → TF C X
    F-lift v = w' (a' v)

    -- Probamos la correlación entre univ f y f
    univ-prop : {C : Cont} {X : Set} (f : ∀ {X} → ⟦ C ⟧ X → M₀ X) (x : ⟦ C ⟧ X) → univ f (F-lift x) ≡ f x
    univ-prop f x = refl

    -- Finalmente, mostramos que univ f es el único homomorfismo que satisface la 
    -- propiedad anterior
    univ-unique : {C : Cont} (f : ∀ {X} → ⟦ C ⟧ X → M₀ X) (g : DioidMorphism (TF-Dioid C) D) → (∀ {X} {x} → fun g {X} (F-lift x) ≡ f x) → ∀ {X} x → fun g {X} x ≡ univ f x
    univ-unique f g p z' = preserves-0 g
    univ-unique f g p (o' x) =
      begin
        fun g (o' x)
      ≡⟨ refl ⟩
        fun g (fmapf (λ _ → x) (o' tt))
      ≡⟨ fun-nat g (λ _ → x) (o' tt) ⟩
        M₁ (λ _ → x) (fun g (o' tt))
      ≡⟨ cong (M₁ (λ _ → x)) (preserves-1 g) ⟩
        M₁ (λ _ → x) unit
      ∎
    univ-unique f g p (w' (a' x)) = p
    univ-unique f g p (w' (suma1 (a' x) y)) =
      begin
        fun g (w' (suma1 (a' x) y))
      ≡⟨ refl ⟩
        (fun g ((F-lift x) ⊕F (o' y)))
      ≡⟨ preserves-+ g (w' (a' x)) (o' y) ⟩
        (fun g (F-lift x) ⊕ fun g (o' y))
      ≡⟨ cong₂ _⊕_ refl (univ-unique f g p (o' y)) ⟩
        (fun g (F-lift x) ⊕ M₁ (λ _ → y) unit)
      ≡⟨ cong₂ _⊕_ p refl ⟩
        (f x ⊕ M₁ (λ _ → y) unit)
      ∎
    univ-unique f g p (w' (suma1 (prod1 x) y)) = 
       begin
         fun g (w' (suma1 (prod1 x) y)) 
       ≡⟨ refl ⟩
         fun g ((w'(prod1 x)) ⊕F (o' y))
       ≡⟨ preserves-+ g (w' (prod1 x)) (o' y ) ⟩
         fun g (w'(prod1 x)) ⊕ fun g (o' y)
       ≡⟨ cong₂ _⊕_ (univ-unique f g p (w' (prod1 x))) (univ-unique f g p (o' y)) ⟩
         univ f (w' (prod1 x)) ⊕ M₁ (λ _ → y) unit
       ∎
    univ-unique f g p (w' (suma1 (prod2 x x₁) y)) = --  {!!}
       begin
        fun g (w' (suma1 (prod2 x x₁) y)) 
       ≡⟨ refl ⟩
        fun g ((w' (prod2 x x₁)) ⊕F (o' y))
       ≡⟨ preserves-+ g (w' (prod2 x x₁)) (o' y)  ⟩
        fun g (w' (prod2 x x₁)) ⊕ fun g (o' y)
       ≡⟨ cong₂ _⊕_ (univ-unique f g p (w' (prod2 x x₁))) (univ-unique f g p (o' y)) ⟩
        univ f (w' (prod2 x x₁)) ⊕ M₁ (λ _ → y) unit
       ∎
    univ-unique f g p (w' (suma2 (a' x) x₁)) = 
        begin 
          fun g (w' (suma2 (a' x) x₁))
        ≡⟨ refl ⟩
          fun g (w' (a' x) ⊕F (w' x₁))
        ≡⟨ preserves-+ g (w' (a' x)) (w' x₁) ⟩
           fun g (w' (a' x)) ⊕ fun g (w' x₁)
        ≡⟨ cong₂ _⊕_ (univ-unique f g p (w' (a' x))) (univ-unique f g p (w' x₁)) ⟩
           f x ⊕ univ f (w' x₁)
        ≡⟨ sym (univ-preserves-+ f (w' (a' x)) (w' x₁)) ⟩
          univ f ((w' (a' x)) ⊕F (w' x₁))
        ≡⟨ refl ⟩
          univ f (w' (suma2 (a' x) x₁))
        ∎
    univ-unique f g p (w' (suma2 (prod1 x) x₁)) = 
       begin
         fun g (w' (suma2 (prod1 x) x₁))
       ≡⟨ refl ⟩
         fun g ((w' (prod1 x)) ⊕F (w' x₁))
       ≡⟨ preserves-+ g (w' (prod1 x)) (w' x₁) ⟩
         fun g (w' (prod1 x)) ⊕ fun g (w' x₁)
       ≡⟨ cong₂ _⊕_ (univ-unique f g p (w' (prod1 x))) (univ-unique f g p (w' x₁)) ⟩
          univ f (w' (prod1 x)) ⊕ univ f (w' x₁)
       ≡⟨ sym (univ-preserves-+ f (w' (prod1 x)) (w' x₁)) ⟩
         univ f ((w' (prod1 x)) ⊕F (w' x₁))
       ≡⟨ refl ⟩
         univ f (w' (suma2 (prod1 x) x₁))
       ∎
    univ-unique f g p (w' (suma2 (prod2 x x₁) x₂)) = -- {!!} 
       begin
         fun g (w' (suma2 (prod2 x x₁) x₂))
       ≡⟨ refl ⟩
          fun g ((w' (prod2 x x₁)) ⊕F (w' x₂))
       ≡⟨ preserves-+ g (w' (prod2 x x₁)) (w' x₂) ⟩
          fun g (w' (prod2 x x₁)) ⊕ fun g (w' x₂)
       ≡⟨ cong₂ _⊕_ (univ-unique f g p (w' (prod2 x x₁))) (univ-unique f g p (w' x₂)) ⟩
          univ f (w' (prod2 x x₁)) ⊕ univ f (w' x₂)
       ≡⟨ sym (univ-preserves-+ f (w' (prod2 x x₁)) (w' x₂)) ⟩
         univ f ((w' (prod2 x x₁)) ⊕F (w' x₂))          
       ≡⟨ refl ⟩
         univ f (w' (suma2 (prod2 x x₁) x₂))
       ∎
    univ-unique f g p (w' (prod1 (a' x))) = 
       begin
         fun g (w' (prod1 (a' x)))
       ≡⟨ refl ⟩
          fun g (fmapf (λ p₁ → proj₁ p₁ (proj₂ p₁)) (w' (a' x) ⊗F z'))
       ≡⟨ fun-nat g (λ p₁ → proj₁ p₁ (proj₂ p₁)) (w' (a' x) ⊗F z') ⟩
         M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁)) (fun g (w' (a' x) ⊗F z'))
       ≡⟨ cong (λ s → M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁)) s) (preserves-* g (w' (a' x)) z') ⟩
         M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁)) (fun g (w' (a' x)) ⊗ fun g z')
       ≡⟨ cong₂ (λ s d → M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁)) (s ⊗ d)) (univ-unique f g p (w' (a' x))) (univ-unique f g p z') ⟩
         M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁)) (univ f (w' (a' x)) ⊗ univ f z')
       ≡⟨ refl ⟩
         univ f (w' (prod1 (a' x)))
       ∎
    univ-unique f g p (w' (prod1 (suma1 x x₁))) = 
       begin
         fun g (w' (prod1 (suma1 x x₁)))
       ≡⟨ sym (cong (λ s → fun g (w' (prod1 (suma1 s x₁)))) (fmaps-id x)) ⟩
         fun g (w' (prod1 (suma1 (fmaps (λ z  → z) x) x₁)))
       ≡⟨ refl ⟩
         fun g
           (w'
            (prod1
             (suma1 (fmaps (λ z z₁ → proj₁ (z , z₁) (proj₂ (z , z₁))) x)
              (λ z → x₁ z))))
       ≡⟨ cong (λ s → fun g (w' (prod1 (suma1 s (λ z → x₁ z))))) (fmaps-∘ ((λ g₁ z → proj₁ (g₁ z) (proj₂ (g₁ z)))) _,_ x) ⟩
         fun g
      (w'
       (prod1
        (suma1 (fmaps (λ g₁ z → proj₁ (g₁ z) (proj₂ (g₁ z))) (fmaps _,_ x))
         (λ z → x₁ z))))
       ≡⟨ refl ⟩
          fun g (fmapf (λ p₁ → proj₁ p₁ (proj₂ p₁)) (w' (suma1 x x₁) ⊗F z'))
       ≡⟨ fun-nat g (λ p₁ → proj₁ p₁ (proj₂ p₁)) (w' (suma1 x x₁) ⊗F z') ⟩
         M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁)) (fun g (w' (suma1 x x₁) ⊗F z'))
       ≡⟨ cong (λ s → M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁)) s) (preserves-* g (w' (suma1 x x₁)) z') ⟩
         M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁)) (fun g (w' (suma1 x x₁)) ⊗ fun g z')
       ≡⟨ cong₂ (λ s d → M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁)) (s ⊗ d)) (univ-unique f g p (w' (suma1 x x₁))) (univ-unique f g p z') ⟩
         M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁)) (univ f (w' (suma1 x x₁)) ⊗ univ f z')
       ≡⟨ refl ⟩
         univ f (w' (prod1 (suma1 x x₁)))
       ∎
    univ-unique f g p (w' (prod1 (suma2 x x₁))) = 
       begin
         fun g (w' (prod1 (suma2 x x₁)))
       ≡⟨ cong₂ (λ s d →  fun g (w' (prod1 (suma2 s d))) ) (sym (fmaps-id x)) (sym (fmapw-id x₁)) ⟩
        fun g (w' (prod1 (suma2 (fmaps (λ z → z) x) (fmapw (λ z → z) x₁))))
       ≡⟨ refl ⟩ 
         fun g
           (w'
            (prod1
             (suma2 (fmaps (λ z z₁ → proj₁ (z , z₁) (proj₂ (z , z₁))) x)
              (fmapw (λ z z₁ → proj₁ (z , z₁) (proj₂ (z , z₁))) x₁))))
       ≡⟨ cong₂ (λ s d → fun g (w' (prod1 (suma2 s d)))) (fmaps-∘ ((λ g₁ z → proj₁ (g₁ z) (proj₂ (g₁ z)))) _,_ x) (fmapw-∘ (λ g₁ z → proj₁ (g₁ z) (proj₂ (g₁ z))) _,_ x₁) ⟩
         fun g
      (w'
       (prod1
        (suma2 (fmaps (λ g₁ z → proj₁ (g₁ z) (proj₂ (g₁ z))) (fmaps _,_ x))
         (fmapw (λ g₁ z → proj₁ (g₁ z) (proj₂ (g₁ z))) (fmapw _,_ x₁)))))
       ≡⟨ refl ⟩
          fun g (fmapf (λ p₁ → proj₁ p₁ (proj₂ p₁)) (w' (suma2 x x₁) ⊗F z'))
       ≡⟨ fun-nat g (λ p₁ → proj₁ p₁ (proj₂ p₁)) (w' (suma2 x x₁) ⊗F z') ⟩
         M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁)) (fun g (w' (suma2 x x₁) ⊗F z'))
       ≡⟨ cong (λ s → M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁)) s) (preserves-* g (w' (suma2 x x₁)) z') ⟩
         M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁)) (fun g (w' (suma2 x x₁)) ⊗ fun g z')
       ≡⟨ cong₂ (λ s d → M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁)) (s ⊗ d)) (univ-unique f g p (w' (suma2 x x₁))) (univ-unique f g p z') ⟩
         M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁)) (univ f (w' (suma2 x x₁)) ⊗ univ f z')
       ≡⟨ refl ⟩
         univ f (w' (prod1 (suma2 x x₁)))
       ∎
    univ-unique f g p (w' (prod2 (a' x) x₁)) = -- {!!}
     begin
       fun g (w' (prod2 (a' x) x₁)) 
     ≡⟨ refl ⟩ 
       fun g (fmapf (λ p₁ → proj₁ p₁ (proj₂ p₁)) (w' (a' x) ⊗F w' x₁))
     ≡⟨ fun-nat g (λ p₁ → proj₁ p₁ (proj₂ p₁)) (w' (a' x) ⊗F (w' x₁)) ⟩
      M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁)) (fun g (w' (a' x) ⊗F (w' x₁))) 
     ≡⟨ cong (λ s → M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁)) s) (preserves-* g (w' (a' x)) (w' x₁)) ⟩
      M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁)) (fun g (w' (a' x)) ⊗ fun g (w' x₁)) 
     ≡⟨ cong₂ (λ s d → M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁)) (s ⊗ d)) (univ-unique f g p (w' (a' x))) (univ-unique f g p (w' x₁)) ⟩
      M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁)) (univ f (w' (a' x)) ⊗ univ f (w' x₁))
     ∎
    univ-unique f g p (w' (prod2 (suma1 x x₁) x₂)) = 
     begin
      fun g (w' (prod2 (suma1 x x₁) x₂))
     ≡⟨ cong (λ s → fun g (w' (prod2 (suma1 s x₁) x₂))) (sym (fmaps-id x)) ⟩
      fun g (w' (prod2 (suma1 (fmaps (λ s → s) x) x₁) x₂))
     ≡⟨ cong (λ s → fun g (w' (prod2 (suma1 s x₁) x₂))) (fmaps-∘ (λ g₁ z → proj₁ (g₁ z) (proj₂ (g₁ z))) _,_ x) ⟩
      fun g (w' (prod2
            (suma1 (fmaps (λ g₁ z → proj₁ (g₁ z) (proj₂ (g₁ z))) 
                                                   (fmaps _,_ x)) 
                   (λ z → x₁ z))
                 x₂))
     ≡⟨ refl ⟩ 
      fun g (fmapf (λ p₁ → proj₁ p₁ (proj₂ p₁)) (w' (suma1 x x₁) ⊗F w' x₂))
     ≡⟨ fun-nat g (λ p₁ → proj₁ p₁ (proj₂ p₁)) (w' (suma1 x x₁) ⊗F w' x₂) ⟩
      M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁)) (fun g (w' (suma1 x x₁) ⊗F w' x₂))
     ≡⟨ cong (λ s → M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁)) s) (preserves-* g (w' (suma1 x x₁)) (w' x₂)) ⟩
         M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁)) (fun g (w' (suma1 x x₁)) ⊗ fun g (w' x₂))
     ≡⟨ cong₂ (λ s d → M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁)) (s ⊗ d)) (univ-unique f g p (w' (suma1 x x₁))) (univ-unique f g p (w' x₂)) ⟩ 
      M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁))
      (univ f (w' (suma1 x x₁)) ⊗ univ f (w' x₂))
     ∎
    univ-unique f g p (w' (prod2 (suma2 x x₁) x₂)) =
     begin
       fun g (w' (prod2 (suma2 x x₁) x₂))
     ≡⟨ cong₂ (λ s d → fun g ((w' (prod2 (suma2 s d) x₂)))) (sym (fmaps-id x)) (sym (fmapw-id x₁)) ⟩
       fun g
      (w' (prod2 (suma2 (fmaps (λ s → s) x)
                        (fmapw (λ s → s) x₁)) x₂))
     ≡⟨ cong₂ (λ s d → fun g ((w' (prod2 (suma2 s d) x₂)))) (fmaps-∘ (λ g₁ z → proj₁ (g₁ z) (proj₂ (g₁ z))) _,_ x) (fmapw-∘ (λ g₁ z → proj₁ (g₁ z) (proj₂ (g₁ z))) _,_ x₁) ⟩
       fun g
      (w'
       (prod2
        (suma2 (fmaps (λ g₁ z → proj₁ (g₁ z) (proj₂ (g₁ z))) (fmaps _,_ x))
         (fmapw (λ g₁ z → proj₁ (g₁ z) (proj₂ (g₁ z))) (fmapw _,_ x₁))) x₂))
     ≡⟨ refl ⟩
        fun g (fmapf (λ p₁ → proj₁ p₁ (proj₂ p₁)) (w' (suma2 x x₁) ⊗F w' x₂))
     ≡⟨ (fun-nat g (λ p₁ → proj₁ p₁ (proj₂ p₁)) (w' (suma2 x x₁) ⊗F w' x₂)) ⟩
       M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁))
        (fun g (w' (suma2 x x₁) ⊗F (w' x₂)))
     ≡⟨ cong (λ s → M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁)) s) (preserves-* g (w' (suma2 x x₁)) (w' x₂)) ⟩
       M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁))
        (fun g (w' (suma2 x x₁)) ⊗ fun g (w' x₂))
     ≡⟨ cong₂ (λ s d → M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁)) (s ⊗ d)) (univ-unique f g p (w' (suma2 x x₁))) (univ-unique f g p (w' x₂)) ⟩
       M₁ (λ p₁ → proj₁ p₁ (proj₂ p₁))
        (univ f (w' (suma2 x x₁)) ⊗ univ f (w' x₂))
     ∎

-- De todo lo anterior, tenemos que TF C es el dioide libre definido sobre un
-- container C.
