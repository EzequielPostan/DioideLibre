{-# OPTIONS --type-in-type #-}

open import Data.Container
open import Level
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (map)

-- Aquí definiremos la estructura de dioide libre sobre un container.
-- Definiremos el tipo de datos sostén, las operaciones y demostraremos
-- la naturalidad de las mismas.

module Free where

  Cont = Container Level.zero

  -- Primero construiremos el tipo de datos que representa a la construcción libre
  -- sobre un container C.
  mutual
    data TF (C : Cont) (X : Set) : Set where
      z' : TF C X
      o' : X → TF C X
      w' : TW C X → TF C X
    data TW (C : Cont) (X : Set) : Set where
      a' : ⟦ C ⟧ X → TW C X
      suma1 : IS C X → X → TW C X
      suma2 : IS C X → TW C X → TW C X
      prod1 : ∀ {A} → IP C (A → X) → TW C X
      prod2 : ∀ {A} → IP C (A → X) → TW C A → TW C X
    data IS (C : Cont) (X : Set) : Set where
      a' : ⟦ C ⟧ X → IS C X
      prod1 : ∀ {A} → IP C (A → X) → IS C X
      prod2 : ∀ {A} → IP C (A → X) → TW C A → IS C X
    data IP (C : Cont) (X : Set) : Set where
      a' : ⟦ C ⟧ X → IP C X
      suma1 : IS C X → X → IP C X
      suma2 : IS C X → TW C X → IP C X


-- Definimos ahora la instancia de fmap para este tipo de datos.   
  mutual
    fmapf : ∀ {C X Y} -> (X -> Y) -> TF C X -> TF C Y
    fmapf f z' = z'
    fmapf f (o' x) = o' (f x)
    fmapf f (w' x) = w' (fmapw f x)

    fmapw : ∀ {C X Y} -> (X -> Y) -> TW C X -> TW C Y
    fmapw f (a' x) = a' (map f x)
    fmapw f (suma1 x y) = suma1 (fmaps f x) (f y)
    fmapw f (suma2 x tw) = suma2 (fmaps f x) (fmapw f tw)
    fmapw f (prod1 x) = prod1 (fmapp (λ g z → f (g z)) x)
    fmapw f (prod2 x tw) = prod2 (fmapp (λ g z → f (g z)) x) tw

    fmaps : ∀ {C X Y} -> (X -> Y) -> IS C X -> IS C Y
    fmaps f (a' x) = a' (map f x)
    fmaps f (prod1 x) = prod1 (fmapp (λ g z → f (g z)) x)
    fmaps f (prod2 x y) = prod2 (fmapp (λ g z → f (g z)) x) y

    fmapp : ∀ {C X Y} -> (X -> Y) -> IP C X -> IP C Y
    fmapp f (a' x) = a' (map f x)
    fmapp f (suma1 x y) = suma1 (fmaps f x) (f y)
    fmapp f (suma2 x y) = suma2 (fmaps f x) (fmapw f y)

  -- La parametrización sobre A de los constructores prod1 y prod2 nos garantiza 
  -- estas dos propiedades de dinaturalidad.
  postulate prod1-nat : ∀ {C : Cont} {A B X : Set} (f : A → B) (v : IP C (B → X)) → _≡_ {A = TW C X} (prod1 v) (prod1 {A = A} (fmapp (λ x x₁ → x (f x₁)) v))
  postulate prod2-nat : ∀ {C : Cont} {A B X : Set} (f : A → B) (v1 : IP C (B → X)) (v2 : TW C A) → _≡_ {A = TW C X} (prod2 v1 (fmapw f v2)) (prod2 {A = A} (fmapp (λ x x₁ → x (f x₁)) v1) v2)

  open  ≡-Reasoning

  lemma-id : ∀ {C : Cont} {X : Set} (x : ⟦ C ⟧ X) → map (λ z → z) x ≡ x
  lemma-id v = refl

  lemma-∘ : ∀ {C : Cont}{X Y Z : Set} (f : Y → Z) (g : X → Y) (x : ⟦ C ⟧ X)
                              → map (λ z → f (g z)) x ≡ map f (map g x)
  lemma-∘ f g (proj₁,proj₂) = refl

-- Demostramos ahora las leyes de fmap
-- Primero, la ley que vincula a fmap y a la función identidad
  mutual
    fmapf-id : {C : Cont} {X : Set} (x : TF C X) → fmapf (λ z → z) x ≡ x
    fmapf-id z' = refl
    fmapf-id (o' x) = refl
    fmapf-id (w' x) = cong (λ z → w' z) (fmapw-id x)
    fmapw-id : {C : Cont} {X : Set} (x : TW C X) → fmapw (λ z → z) x ≡ x
    fmapw-id (a' x) = cong (λ z → a' z) (lemma-id x)
    fmapw-id (suma1 x x₁) = cong (λ z → suma1 z x₁) (fmaps-id x)
    fmapw-id (suma2 x tw) = cong₂ suma2 (fmaps-id x) (fmapw-id tw) 
    fmapw-id (prod1 x) = cong (λ x₁ → prod1 x₁) (fmapp-id x)
    fmapw-id (prod2 x tw) = cong₂ prod2 (fmapp-id x) refl 
    fmaps-id : {C : Cont} {X : Set} (x : IS C X) → fmaps (λ z → z) x ≡ x
    fmaps-id (a' x) = cong a' (lemma-id x)
    fmaps-id (prod1 x) = cong prod1 (fmapp-id x)
    fmaps-id (prod2 x x₁) = cong₂ prod2 (fmapp-id x) refl
    fmapp-id : {C : Cont} {X : Set} (x : IP C X) → fmapp (λ z → z) x ≡ x 
    fmapp-id (a' x) = cong a' (lemma-id x)
    fmapp-id (suma1 x x₁) = cong₂ suma1 (fmaps-id x) refl
    fmapp-id (suma2 x x₁) = cong₂ suma2 (fmaps-id x) (fmapw-id x₁)

-- Luego, la relación entre fmap y la composición
  mutual
    fmapf-∘ : {C : Cont}{X Y Z : Set} (f : Y → Z) (g : X → Y) (x : TF C X)
                              → fmapf (λ z → f (g z)) x ≡ fmapf f (fmapf g x)
    fmapf-∘ f g z' = refl
    fmapf-∘ f g (o' x) = refl
    fmapf-∘ f g (w' x) = cong w' (fmapw-∘ f g x)
    fmapw-∘ : {C : Cont}{X Y Z : Set} (f : Y → Z) (g : X → Y) (x : TW C X)
                              → fmapw (λ z → f (g z)) x ≡ fmapw f (fmapw g x)
    fmapw-∘ f g (a' x) = cong a' (lemma-∘ f g x)
    fmapw-∘ f g (suma1 x x₁) = cong₂ suma1 (fmaps-∘ f g x) refl
    fmapw-∘ f g (suma2 x tw) = cong₂ suma2 (fmaps-∘ f g x) (fmapw-∘ f g tw)
    fmapw-∘ f g (prod1 x) = cong prod1 (fmapp-∘ (λ z z₁ → f (z z₁)) (λ z z₁ → g (z z₁)) x)
    fmapw-∘ f g (prod2 x tw) = cong₂ prod2 (fmapp-∘ (λ z z₁ → f (z z₁)) (λ z z₁ → g (z z₁)) x) refl
    fmaps-∘ : {C : Cont}{X Y Z : Set} (f : Y → Z) (g : X → Y) (x : IS C X)
                              → fmaps (λ z → f (g z)) x ≡ fmaps f (fmaps g x)
    fmaps-∘ f g (a' x) = cong a' (lemma-∘ f g x)
    fmaps-∘ f g (prod1 x) = cong prod1 (fmapp-∘ (λ z z₁ → f (z z₁)) (λ z z₁ → g (z z₁)) x)
    fmaps-∘ f g (prod2 x x₁) = cong₂ prod2 (fmapp-∘ (λ z z₁ → f (z z₁)) (λ z z₁ → g (z z₁)) x) refl
    fmapp-∘ : {C : Cont}{X Y Z : Set} (f : Y → Z) (g : X → Y) (x : IP C X)
                              → fmapp (λ z → f (g z)) x ≡ fmapp f (fmapp g x)
    fmapp-∘ f g (a' x) = cong a' (lemma-∘ f g x)
    fmapp-∘ f g (suma1 x x₁) = cong₂ suma1 (fmaps-∘ f g x) refl
    fmapp-∘ f g (suma2 x x₁) = cong₂ suma2 (fmaps-∘ f g x) (fmapw-∘ f g x₁)

  -- Pasamos a definir las operaciones de suma y producto
  -- Al igual que en el caso de Set, debemos recurrir a funciones
  -- auxiliares por la restricción de Agda al uso de funciones totales

  -- Suma (auxiliar)
  _⊕v_ :  ∀ {C X} → TW C X → TF C X → TW C X
  a' x ⊕v z' = a' x
  a' x ⊕v o' y = suma1 (a' x) y
  a' x ⊕v w' y = suma2 (a' x) y
  suma1 (a' x) y ⊕v tf = suma1 (a' x) y
  suma1 (prod1 x) y ⊕v tf = suma1 (prod1 x) y
  suma1 (prod2 x y) z ⊕v tf = suma1 (prod2 x y) z
  suma2 x tw ⊕v tf = suma2 x (tw ⊕v tf)
  prod1 x ⊕v z' = prod1 x
  prod1 x ⊕v o' y = suma1 (prod1 x) y
  prod1 x ⊕v w' y = suma2 (prod1 x) y
  prod2 x tw ⊕v z' = prod2 x tw
  prod2 x tw ⊕v o' y = suma1 (prod2 x tw) y
  prod2 x tw ⊕v w' y = suma2 (prod2 x tw) y

  -- Suma
  _⊕F_ : ∀ {C X} → TF C X → TF C X → TF C X
  z' ⊕F tw' = tw'
  o' x ⊕F tw' = o' x
  w' x ⊕F tw' = w' (x ⊕v tw')

  -- Producto (auxiliar)
  _⋆E_ : ∀ {C X Y} -> TW C X -> TF C Y -> TW C (X × Y)
  a' x ⋆E z' = prod1 (a' (map _,_ x))
  a' x ⋆E o' y = a' (map (λ x → x , y) x)
  a' x ⋆E w' y = prod2 (a' (map _,_ x)) y
  suma1 x x₁ ⋆E z' = prod1 (suma1 (fmaps _,_ x) (_,_ x₁))
  suma1 x x₁ ⋆E o' x₂ = suma1 (fmaps (λ z → z , x₂) x) (x₁ , x₂)
  suma1 x x₁ ⋆E w' x₂ = prod2 (suma1 (fmaps _,_ x) (_,_ x₁)) x₂
  suma2 x a ⋆E z' = prod1 (suma2 (fmaps _,_ x) (fmapw _,_ a))
  suma2 x a ⋆E o' x₁ = suma2 (fmaps (λ z → z , x₁) x) (fmapw (λ z → z , x₁) a)
  suma2 x a ⋆E w' x₁ = prod2 (suma2 (fmaps _,_ x) (fmapw _,_ a)) x₁
  _⋆E_ {X = X} {Y = Y} (prod1 {A = A} x) b = prod1 {A = A × Y} (fmapp (λ f p → f (proj₁ p) , proj₂ p) x)
  _⋆E_ {X = X} {Y = Y} (prod2 {A = A} x a) b = prod2 {A = A × Y}  (fmapp (λ f p → (f (proj₁ p)) , (proj₂ p)) x) (a ⋆E b)

  -- Producto
  _⊗F_ : ∀ {C X Y} → TF C X → TF C Y → TF C (X × Y)
  z' ⊗F tf = z'
  o' x ⊗F tf = fmapf (_,_ x) tf
  w' x ⊗F tf = w' (x ⋆E tf)

-- Mostramos ahora las naturalidades y dinaturalidades de estas operaciones
-- y del cero.

  -- Naturalidad de z'
  z-nat : {C : Cont} {X Y : Set} (f : X → Y) → fmapf {C} {X} {Y} f z' ≡ z'
  z-nat f = refl

  -- Naturalidad de la suma
  -- Primero sobre la operación auxiliar.
  ⊕v-nat : {C : Cont} {X Y : Set} (f : X → Y) (x : TW C X) (y : TF C X)
                 → fmapw f (x ⊕v y) ≡ fmapw f x ⊕v fmapf f y
  ⊕v-nat f (a' x) z' = refl
  ⊕v-nat f (a' x) (o' x₁) = refl
  ⊕v-nat f (a' x) (w' x₁) = refl
  ⊕v-nat f (suma1 (a' x) x₁) tf = refl
  ⊕v-nat f (suma1 (prod1 x) x₁) tf = refl
  ⊕v-nat f (suma1 (prod2 x x₁) x₂) tf = refl
  ⊕v-nat f (suma2 x x₁) z' = cong (suma2 (fmaps f x)) (⊕v-nat f x₁ z')
  ⊕v-nat f (suma2 x x₁) (o' x₂) = cong (suma2 (fmaps f x)) (⊕v-nat f x₁ (o' x₂))
  ⊕v-nat f (suma2 x x₁) (w' x₂) = cong (suma2 (fmaps f x)) (⊕v-nat f x₁ (w' x₂))
  ⊕v-nat f (prod1 x) z' = refl
  ⊕v-nat f (prod1 x) (o' x₁) = refl
  ⊕v-nat f (prod1 x) (w' x₁) = refl
  ⊕v-nat f (prod2 x x₁) z' = refl
  ⊕v-nat f (prod2 x x₁) (o' x₂) = refl
  ⊕v-nat f (prod2 x x₁) (w' x₂) = refl

  -- Luego, sobre la suma.
  ⊕F-nat : {C : Cont} {X Y : Set} (f : X → Y) → (x y : TF C X)
                 → fmapf f (x ⊕F y) ≡ fmapf f x ⊕F fmapf f y
  ⊕F-nat f z' y = refl
  ⊕F-nat f (o' x) y = refl
  ⊕F-nat f (w' x) y = cong w' (⊕v-nat f x y)


  -- Naturalidad del producto
  -- Primero sobre la operación auxiliar.
  e-nat : ∀ {C X Y V W} (v1 : TW C X) (v2 : TF C Y) (f : X → V) (g : Y → W) → fmapw (λ p → (f (proj₁ p)) , (g (proj₂ p))) (v1 ⋆E v2) ≡ fmapw f v1 ⋆E fmapf g v2
  e-nat (a' x) z' f g = sym (prod1-nat g (a' (map (λ x₁ x₂ → (f x₁) , x₂) x)))
  e-nat (a' x) (o' x₁) f g = cong a' refl
  e-nat (a' x) (w' x₁) f g = sym (prod2-nat g (a' (map (λ x₂ x₃ → (f x₂) , x₃) x)) x₁)
  e-nat {C} {X} {Y} {V} {W} (suma1 x x₁) z' f g =
    begin
      prod1 {A = Y} (suma1 (fmaps (λ g₁ z → f (proj₁ (g₁ z)) , g (proj₂ (g₁ z))) (fmaps _,_ x)) (λ z → f x₁ , g z))
    ≡⟨ cong prod1 (cong₂ suma1 (sym (fmaps-∘ (λ x₂ x₃ → f (proj₁ (x₂ x₃)) , g (proj₂ (x₂ x₃))) _,_ x)) refl) ⟩
      prod1 {A = Y} (suma1 (fmaps (λ z z₁ → f z , g z₁) x) (λ z → f x₁ , g z))
    ≡⟨ cong prod1 (cong₂ suma1 (fmaps-∘ (λ x₂ x₃ → x₂ , g x₃) f x) refl) ⟩
      prod1 {A = Y} (suma1 (fmaps (λ z z₁ → z , g z₁) (fmaps f x)) (λ x₂ → f x₁ , g x₂))
    ≡⟨ cong prod1 (cong₂ suma1 (fmaps-∘ (λ z z₁ → z (g z₁)) _,_ (fmaps f x)) refl) ⟩
      prod1 {A = Y} (suma1 (fmaps (λ z x₂ → z (g x₂)) (fmaps _,_ (fmaps f x))) (λ x₂ → f x₁ , g x₂))
    ≡⟨ sym (prod1-nat g (suma1 (fmaps _,_ (fmaps f x)) (_,_ (f x₁)))) ⟩
      prod1 {A = W} (suma1 (fmaps _,_ (fmaps f x)) (_,_ (f x₁)))
    ∎
  e-nat (suma1 x x₁) (o' x₂) f g = cong₂ suma1 (trans (sym (fmaps-∘ (λ x₃ → (f (proj₁ x₃)) , (g (proj₂ x₃))) (λ z → z , x₂) x)) (fmaps-∘ (λ x₃ → x₃ , g x₂) f x) ) refl
  e-nat {C} {X} {Y} {V} {W} (suma1 x x₁) (w' x₂) f g =
    begin
      prod2 {A = Y} (suma1 (fmaps (λ g₁ z → f (proj₁ (g₁ z)) , g (proj₂ (g₁ z))) (fmaps _,_ x)) (λ z → f x₁ , g z)) x₂
    ≡⟨ cong₂ prod2 (cong₂ suma1 (sym (fmaps-∘ (λ x₃ x₄ → f (proj₁ (x₃ x₄)) , g (proj₂ (x₃ x₄))) _,_ x)) refl) refl ⟩
      prod2 {A = Y} (suma1 (fmaps (λ x₃ x₄ → f x₃ , g x₄) x) (λ z → f x₁ , g z)) x₂
    ≡⟨ cong₂ prod2 (cong₂ suma1 (fmaps-∘ (λ x₃ x₄ → x₃ , g x₄) f x) refl) refl ⟩
      prod2 {A = Y} (suma1 (fmaps (λ z z₁ → z , g z₁) (fmaps f x)) (λ z → f x₁ , g z)) x₂
    ≡⟨ cong₂ prod2 (cong₂ suma1 (fmaps-∘ (λ z z₁ → z (g z₁)) _,_ (fmaps f x)) refl) refl ⟩
      prod2 {A = Y} (suma1 (fmaps (λ z x₃ → z (g x₃)) (fmaps _,_ (fmaps f x))) (λ x₃ → f x₁ , g x₃)) x₂
    ≡⟨ sym (prod2-nat g (suma1 (fmaps _,_ (fmaps f x)) (_,_ (f x₁))) x₂) ⟩
      prod2 {A = W} (suma1 (fmaps _,_ (fmaps f x)) (_,_ (f x₁))) (fmapw g x₂)
    ∎
  e-nat {C} {X} {Y} {V} {W} (suma2 x v1) z' f g =
    begin
      prod1 {A = Y} (suma2 (fmaps (λ g₁ z → f (proj₁ (g₁ z)) , g (proj₂ (g₁ z))) (fmaps _,_ x)) (fmapw (λ g₁ z → f (proj₁ (g₁ z)) , g (proj₂ (g₁ z))) (fmapw _,_ v1)))
    ≡⟨ cong prod1 (cong₂ suma2 (sym (fmaps-∘ (λ x₁ x₂ → (f (proj₁ (x₁ x₂))) , (g (proj₂ (x₁ x₂)))) _,_ x)) (sym (fmapw-∘ (λ x₁ x₂ → (f (proj₁ (x₁ x₂))) , (g (proj₂ (x₁ x₂)))) _,_ v1))) ⟩
      prod1 {A = Y} (suma2 (fmaps (λ z z₁ → f z , g z₁) x) (fmapw (λ z z₁ → f z , g z₁) v1))
    ≡⟨ cong prod1 (cong₂ suma2 (fmaps-∘ (λ z z₁ → z , g z₁) f x) (fmapw-∘ (λ z z₁ → z , g z₁) f v1)) ⟩
      prod1 {A = Y} (suma2 (fmaps (λ z z₁ → z , g z₁) (fmaps f x)) (fmapw (λ z z₁ → z , g z₁) (fmapw f v1)))
    ≡⟨ cong prod1 (cong₂ suma2 (fmaps-∘ (λ z z₁ → z (g z₁)) _,_ (fmaps f x)) (fmapw-∘ (λ z z₁ → z (g z₁)) _,_ (fmapw f v1))) ⟩
      prod1 {A = Y} (suma2 (fmaps (λ z x₁ → z (g x₁)) (fmaps _,_ (fmaps f x))) (fmapw (λ z x₁ → z (g x₁)) (fmapw _,_ (fmapw f v1))))
    ≡⟨ sym (prod1-nat g (suma2 (fmaps _,_ (fmaps f x)) (fmapw _,_ (fmapw f v1)))) ⟩
      prod1 {A = W} (suma2 (fmaps _,_ (fmaps f x)) (fmapw _,_ (fmapw f v1)))
    ∎
  e-nat (suma2 x v1) (o' x₁) f g = cong₂ suma2 (trans (sym (fmaps-∘ (λ x₂ → (f (proj₁ x₂)) , (g (proj₂ x₂))) (λ z → z , x₁) x)) (fmaps-∘ (λ z → z , g x₁) f x)) (trans (sym (fmapw-∘ (λ x₂ → (f (proj₁ x₂)) , (g (proj₂ x₂))) (λ z → z , x₁) v1)) (fmapw-∘ (λ z → z , g x₁) f v1))
  e-nat (suma2 x v1) (w' x₁) f g = -- {!!}
   begin
    prod2
      (suma2
       (fmaps (λ g₁ z → f (proj₁ (g₁ z)) , g (proj₂ (g₁ z)))
        (fmaps _,_ x))
       (fmapw (λ g₁ z → f (proj₁ (g₁ z)) , g (proj₂ (g₁ z)))
        (fmapw _,_ v1)))
      x₁
   ≡⟨ cong₂ (λ s d → prod2 (suma2 s d) x₁) (sym (fmaps-∘ (λ g₁ z → f (proj₁ (g₁ z)) , g (proj₂ (g₁ z))) _,_ x)) (sym (fmapw-∘ (λ g₁ z → f (proj₁ (g₁ z)) , g (proj₂ (g₁ z))) _,_ v1)) ⟩
     prod2
       (suma2 (fmaps (λ z z₁ → f z , g z₁) x)
       (fmapw (λ z z₁ → f z , g z₁) v1))
        x₁
   ≡⟨ cong₂ (λ s d → prod2 (suma2 s d) x₁) (fmaps-∘ (λ x₂ x₃ → x₂ (g x₃)) (λ z → _,_ (f z)) x) (fmapw-∘ (λ x₂ x₃ → x₂ (g x₃)) (λ z → _,_ (f z)) v1) ⟩
     prod2
      (suma2 (fmaps (λ x₂ x₃ → x₂ (g x₃)) (fmaps (λ z → _,_ (f z)) x))
       (fmapw (λ x₂ x₃ → x₂ (g x₃)) (fmapw (λ z → _,_ (f z)) v1)))
      x₁
   ≡⟨ sym (prod2-nat g (suma2 (fmaps (λ z → _,_ (f z)) x) (fmapw (λ z → _,_ (f z)) v1)) x₁) ⟩
     prod2 
       (suma2 (fmaps (λ z → _,_ (f z)) x) (fmapw (λ z → _,_ (f z)) v1))
       (fmapw g x₁)
   ≡⟨ cong₂ (λ s d → prod2 (suma2 s d) (fmapw g x₁)) (fmaps-∘ _,_ f x) (fmapw-∘ _,_ f v1) ⟩
     prod2 
       (suma2 (fmaps _,_ (fmaps f x)) (fmapw _,_ (fmapw f v1)))
       (fmapw g x₁)
   ∎
  e-nat  {C} {X} {Y} {V} {W} (prod1 {A} x) v2 f g = -- {!!}
   begin
    prod1 {A = Σ A (λ v → Y)}
      (fmapp (λ g₁ z → f (proj₁ (g₁ z)) , g (proj₂ (g₁ z)))
       (fmapp (λ f₁ p → f₁ (proj₁ p) , proj₂ p) x))
   ≡⟨ cong prod1 (sym (fmapp-∘ (λ g₁ z → f (proj₁ (g₁ z)) , g (proj₂ (g₁ z))) (λ f₁ p → f₁ (proj₁ p) , proj₂ p) x)) ⟩
       prod1 (fmapp (λ z z₁ → f (z (proj₁ z₁)) , g (proj₂ z₁)) x)
   ≡⟨ cong prod1 (fmapp-∘ (λ x₁ x₂ → x₁ (proj₁ x₂ , g (proj₂ x₂))) (λ z p → f (z (proj₁ p)) , proj₂ p) x) ⟩
       prod1 {A = Σ A (λ v → Y)}
         (fmapp (λ x₁ x₂ → x₁ (proj₁ x₂ , g (proj₂ x₂)))
          (fmapp (λ z p → f (z (proj₁ p)) , proj₂ p) x))
   ≡⟨ sym (prod1-nat (λ s → (proj₁ s) , (g (proj₂ s))) ((fmapp (λ z p → f (z (proj₁ p)) , proj₂ p) x))) ⟩
       prod1 (fmapp (λ z p → f (z (proj₁ p)) , proj₂ p) x)
   ≡⟨ cong prod1 (fmapp-∘ (λ f₁ p → f₁ (proj₁ p) , proj₂ p) (λ g₁ z → f (g₁ z)) x) ⟩
      prod1 {A = Σ A (λ v → W)}
      (fmapp (λ f₁ p → f₁ (proj₁ p) , proj₂ p)
       (fmapp (λ g₁ z → f (g₁ z)) x))
   ∎
  e-nat (prod2 x v1) v2 f g =  
   begin
    prod2
      (fmapp (λ g₁ z → f (proj₁ (g₁ z)) , g (proj₂ (g₁ z)))
       (fmapp (λ f₁ p → f₁ (proj₁ p) , proj₂ p) x))
      (v1 ⋆E v2)
   ≡⟨ cong (λ s → prod2 s (v1 ⋆E v2)) (sym (fmapp-∘ (λ g₁ z → f (proj₁ (g₁ z)) , g (proj₂ (g₁ z))) (λ f₁ p → f₁ (proj₁ p) , proj₂ p) x)) ⟩
     prod2
       (fmapp
        (λ z z₁ →
           f (proj₁ (z (proj₁ z₁) , proj₂ z₁)) ,
           g (proj₂ (z (proj₁ z₁) , proj₂ z₁)))
        x)
       (v1 ⋆E v2)
   ≡⟨ cong (λ s → prod2 s (v1 ⋆E v2)) (fmapp-∘ (λ x₁ x₂ → x₁ (proj₁ x₂ , g (proj₂ x₂))) (λ z p → f (z (proj₁ p)) , proj₂ p) x) ⟩
      prod2
        (fmapp (λ x₁ x₂ → x₁ (proj₁ x₂ , g (proj₂ x₂)))
         (fmapp (λ z p → f (z (proj₁ p)) , proj₂ p) x))
        (v1 ⋆E v2)
   ≡⟨ sym (prod2-nat (λ p → proj₁ p , g (proj₂ p)) (fmapp (λ z p → f (z (proj₁ p)) , proj₂ p) x) (v1 ⋆E v2)) ⟩
      prod2 (fmapp (λ z p → f (z (proj₁ p)) , proj₂ p) x)
        (fmapw (λ p → proj₁ p , g (proj₂ p)) (v1 ⋆E v2))
   ≡⟨ cong (λ s → prod2 s (fmapw (λ p → proj₁ p , g (proj₂ p)) (v1 ⋆E v2))) (fmapp-∘ ((λ f₁ p → f₁ (proj₁ p) , proj₂ p)) (λ z z₁ → f (z z₁)) x) ⟩
      prod2
        (fmapp (λ f₁ p → f₁ (proj₁ p) , proj₂ p)
         (fmapp (λ g₁ z → f (g₁ z)) x))
        (fmapw (λ p → proj₁ p , g (proj₂ p)) (v1 ⋆E v2))
   ≡⟨ cong (λ s → prod2 (fmapp (λ f₁ p → f₁ (proj₁ p) , proj₂ p)
       (fmapp (λ g₁ z → f (g₁ z)) x)) s) (e-nat v1 v2 (λ z → z) g) ⟩
      prod2
      (fmapp (λ f₁ p → f₁ (proj₁ p) , proj₂ p)
       (fmapp (λ g₁ z → f (g₁ z)) x))
      (fmapw (λ s → s) v1 ⋆E fmapf g v2)
   ≡⟨ cong (λ s → prod2 (fmapp (λ f₁ p → f₁ (proj₁ p) , proj₂ p)
       (fmapp (λ g₁ z → f (g₁ z)) x)) (s ⋆E fmapf g v2)) (fmapw-id v1) ⟩
      prod2
      (fmapp (λ f₁ p → f₁ (proj₁ p) , proj₂ p)
       (fmapp (λ g₁ z → f (g₁ z)) x))
      (v1 ⋆E fmapf g v2)
   ∎

  -- Luego, sobre el producto.
  ⊗F-nat : ∀ {C X Y V W} (v1 : TF C X) (v2 : TF C Y) (f : X → V) (g : Y → W) → fmapf (λ p → (f (proj₁ p)) , (g (proj₂ p))) (v1 ⊗F v2) ≡ fmapf f v1 ⊗F fmapf g v2
  ⊗F-nat z' v2 f g = refl
  ⊗F-nat (o' x) v2 f g =
    begin
      fmapf (λ p → f (proj₁ p) , g (proj₂ p)) (fmapf (_,_ x) v2)
    ≡⟨ sym (fmapf-∘ ((λ p → f (proj₁ p) , g (proj₂ p))) ((_,_) x) v2) ⟩
      fmapf (λ x₁ → f x , g x₁) v2
    ≡⟨ fmapf-∘ (_,_ (f x)) g v2 ⟩
      fmapf (_,_ (f x)) (fmapf g v2)
    ∎
  ⊗F-nat (w' x) v2 f g = cong w' (e-nat x v2 f g)
