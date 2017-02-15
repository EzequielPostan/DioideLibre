module Dioide where

-- A continuación presentamos la prueba de la construcción del dioide libre en 
-- Set.


-- Sea X un conjunto, sobre el que construiremos el libre.
postulate X : Set

-- Construimos N, el tipo de formas normales (libre).
mutual
  data N : Set where
    0N : N
    1N : N
    iN : I → N

  data I : Set where
    eI : X → I
    _⊕I_  : Is → Ds → I
    _⊗I_  : Ip → Dp → I

  data Is : Set where
    eS : X → Is
    _⊗S_ : Ip → Dp → Is

  data Ds : Set where
    1S : Ds
    iS : I → Ds

  data Ip : Set where
    eP : X → Ip
    _⊕P_ : Is → Ds → Ip

  data Dp : Set where
    0P : Dp
    iP : I → Dp

-- Y las operaciones sobre N.
-- Como Agda exige funciones totales, debemos definir operaciones auxiliares. 
_⊕v_ : I → N → I
eI x ⊕v 0N = eI x
eI x ⊕v 1N = eS x ⊕I 1S
eI x ⊕v iN y = eS x ⊕I iS y
(x ⊕I 1S) ⊕v y = x ⊕I 1S
(x ⊕I iS v) ⊕v y = x ⊕I iS (v ⊕v y)
(x ⊗I v) ⊕v 0N = x ⊗I v
(x ⊗I v) ⊕v 1N = (x ⊗S v) ⊕I 1S
(x ⊗I v) ⊕v iN y = (x ⊗S v) ⊕I iS y

_⊗v_ : I → N → I
eI x ⊗v 1N = eI x
eI x ⊗v 0N = eP x ⊗I 0P
eI x ⊗v iN y = eP x ⊗I iP y
(x ⊕I v) ⊗v 0N = (x ⊕P v) ⊗I 0P
(x ⊕I v) ⊗v 1N = x ⊕I v
(x ⊕I v) ⊗v iN y = (x ⊕P v) ⊗I iP y
(x ⊗I 0P) ⊗v y = x ⊗I 0P
(x ⊗I iP v) ⊗v y = x ⊗I iP (v ⊗v y)

-- Usando las auxiliares, definimos las operaciones sobre N.
_⊕N_ : N → N → N
0N ⊕N y = y
1N ⊕N y = 1N
iN v ⊕N y = iN (v ⊕v y)

_⊗N_ : N → N → N
0N ⊗N y = 0N
1N ⊗N y = y
iN v ⊗N y = iN (v ⊗v y)


-- Ahora pasamos a demostrar las leyes que deben satisfacerse
-- para que N sea un dioide.

open import Relation.Binary.PropositionalEquality  

-- El 0 es neutro a izquierda de la suma.
law-⊕N-0l : (t : N) → 0N ⊕N t ≡ t
law-⊕N-0l t = refl

-- El 0 es neutro a derecha de la suma.
-- Primero lo demostramos sobre la operación auxiliar.
law-⊕v-0r : (t : I) → t ⊕v 0N ≡ t
law-⊕v-0r (eI x) = refl
law-⊕v-0r (x ⊕I 1S) = refl
law-⊕v-0r (x ⊕I iS y) = cong (λ i → x ⊕I iS i) (law-⊕v-0r y)
law-⊕v-0r (x ⊗I y) = refl

-- Luego, sobre la operación sobre N.
law-⊕N-0r : (t : N) → t ⊕N 0N ≡ t
law-⊕N-0r 0N = refl
law-⊕N-0r 1N = refl
law-⊕N-0r (iN v) = cong iN (law-⊕v-0r v)


-- Asociatividad de la suma.
-- Primero sobre la operación auxiliar.
law-⊕v-a : (t : I) (u v : N) → t ⊕v (u ⊕N v) ≡ (t ⊕v u) ⊕v v
law-⊕v-a (eI x) 0N v = refl
law-⊕v-a (eI x) 1N v = refl
law-⊕v-a (eI x) (iN y) v = refl
law-⊕v-a (x ⊕I 1S) u v = refl
law-⊕v-a (x ⊕I iS y) u v = cong (λ i → x ⊕I iS i) (law-⊕v-a y u v)
law-⊕v-a (x ⊗I y) 0N v = refl
law-⊕v-a (x ⊗I y) 1N v = refl
law-⊕v-a (x ⊗I y) (iN w) v = refl

-- Luego sobre la definida sobre N.
law-⊕N-a : (t u v : N) → t ⊕N (u ⊕N v) ≡ (t ⊕N u) ⊕N v
law-⊕N-a 0N u v = refl
law-⊕N-a 1N u v = refl
law-⊕N-a (iN x) u v = cong iN (law-⊕v-a x u v)

-- El 1 es absorbente a izquierda de la suma
law-⊕N-1 : (t : N) → 1N ⊕N t ≡ 1N
law-⊕N-1 t = refl

-- Pasamos a las propiedades del producto.

-- El 1 es neutro a izquierda de la suma.
law-⊗N-1l : (t : N) → 1N ⊗N t ≡ t
law-⊗N-1l t = refl

-- El 1 es neutro a derecha de la suma.
-- Comenzamos con la operación auxiliar.
law-⊗v-1r : (t : I) → t ⊗v 1N ≡ t
law-⊗v-1r (eI x) = refl
law-⊗v-1r (x ⊗I 0P) = refl
law-⊗v-1r (x ⊗I iP y) = cong (λ i → x ⊗I iP i) (law-⊗v-1r y)
law-⊗v-1r (x ⊕I y) = refl

-- Luego, extendemos el resultado a la operación sobre N.
law-⊗N-1r : (t : N) → t ⊗N 1N ≡ t
law-⊗N-1r 1N = refl
law-⊗N-1r 0N = refl
law-⊗N-1r (iN v) = cong iN (law-⊗v-1r v)

-- Asociatividad del producto.
-- Primero sobre la operación auxiliar.
law-⊗v-a : (t : I) (u v : N) → t ⊗v (u ⊗N v) ≡ (t ⊗v u) ⊗v v
law-⊗v-a (eI x) 1N v = refl
law-⊗v-a (eI x) 0N v = refl
law-⊗v-a (eI x) (iN y) v = refl
law-⊗v-a (x ⊗I 0P) u v = refl
law-⊗v-a (x ⊗I iP y) u v = cong (λ i → x ⊗I iP i) (law-⊗v-a y u v)
law-⊗v-a (x ⊕I y) 1N v = refl
law-⊗v-a (x ⊕I y) 0N v = refl
law-⊗v-a (x ⊕I y) (iN w) v = refl

-- Luego sobre la operación sobre N.
law-⊗N-a : (t u v : N) → t ⊗N (u ⊗N v) ≡ (t ⊗N u) ⊗N v
law-⊗N-a 0N u v = refl
law-⊗N-a 1N u v = refl
law-⊗N-a (iN x) u v = cong iN (law-⊗v-a x u v)

-- El 0 es absorbente a izquierda del producto.
law-⊗N-0 : (t : N) → 0N ⊗N t ≡ 0N
law-⊗N-0 t = refl

-- Definimos ahora la estructura de dioide.
record Dioid (D : Set) : Set where
  field
    -- constantes
    1D : D
    0D : D
    -- operadores
    _⊕D_ : D → D → D
    _⊗D_ : D → D → D
    -- axiomas ⊕
    ⊕-0r : (d : D) → d ⊕D 0D ≡ d
    ⊕-0l : (d : D) → 0D ⊕D d ≡ d
    ⊕-a : (d e f : D) → d ⊕D (e ⊕D f) ≡ (d ⊕D e) ⊕D f
    ⊕-1 : (d : D) → 1D ⊕D d ≡ 1D
    -- axiomas ⊗
    ⊗-1r : (d : D) → d ⊗D 1D ≡ d
    ⊗-1l : (d : D) → 1D ⊗D d ≡ d
    ⊗-a : (d e f : D) → d ⊗D (e ⊗D f) ≡ (d ⊗D e) ⊗D f
    ⊗-0 : (d : D) → 0D ⊗D d ≡ 0D

-- Vemos que efectivamente definimos un dioide.
N-Dioid : Dioid N
N-Dioid = record
            { 1D = 1N
            ; 0D = 0N
            ; _⊕D_ = _⊕N_
            ; _⊗D_ = _⊗N_
            ; ⊕-0r = law-⊕N-0r
            ; ⊕-0l = law-⊕N-0l
            ; ⊕-a = law-⊕N-a
            ; ⊕-1 = law-⊕N-1
            ; ⊗-1r = law-⊗N-1r
            ; ⊗-1l = law-⊗N-1l
            ; ⊗-a = law-⊗N-a
            ; ⊗-0 = law-⊗N-0
            }

-- Hasta aquí probamos que N es un dioide.
-- Pasamos ahora a definiciones necesarias para mostrar la propiedad de ser libre.

-- Primero, la estructura de homomorfismo.
record Hom {D E : Set} (S : Dioid D) (T : Dioid E) : Set where
  field
    -- función
    map : D → E
    -- leyes
    map-0 : map (Dioid.0D S) ≡ Dioid.0D T
    map-1 : map (Dioid.1D S) ≡ Dioid.1D T
    map-⊕ : (d d' : D) → map ((Dioid._⊕D_ S) d d') ≡ (Dioid._⊕D_ T (map d) (map d'))
    map-⊗ : (d d' : D) → map ((Dioid._⊗D_ S) d d') ≡ (Dioid._⊗D_ T (map d) (map d'))

-- La inyección al libre.
inj : X → N
inj x = iN (eI x)

-- Dado otro dioide D
postulate D : Set
postulate D-Dioid : Dioid D
-- con una flecha desde X
postulate f : X → D

open Dioid D-Dioid

-- existe un morfismo que liftea f
lift : N → D
lift 0N = 0D
lift 1N = 1D
lift (iN (eI x)) = f x
lift (iN (eS x ⊕I 1S)) = f x ⊕D 1D
lift (iN (eS x ⊕I iS y)) = f x ⊕D lift (iN y)
lift (iN ((x ⊗S y) ⊕I 1S)) = lift (iN (x ⊗I y)) ⊕D 1D
lift (iN ((x ⊗S y) ⊕I iS v)) = lift (iN (x ⊗I y)) ⊕D lift (iN v)
lift (iN (eP x ⊗I 0P)) = f x ⊗D 0D
lift (iN (eP x ⊗I iP y)) = f x ⊗D lift (iN y)
lift (iN ((x ⊕P y) ⊗I 0P)) = lift (iN (x ⊕I y)) ⊗D 0D
lift (iN ((x ⊕P y) ⊗I iP v)) = lift (iN (x ⊕I y)) ⊗D lift (iN v)

open ≡-Reasoning

-- lift es homomorfismo
lift-0 : lift 0N ≡ 0D
lift-0 = refl

lift-1 : lift 1N ≡ 1D
lift-1 = refl

lift-⊕v : (t : I) (u : N) → lift (iN (t ⊕v u)) ≡ lift (iN t) ⊕D lift u
lift-⊕v (eI x) 0N = sym (⊕-0r (f x))
lift-⊕v (eI x) 1N = refl
lift-⊕v (eI x) (iN y) = refl
lift-⊕v (eS x ⊕I 1S) u = 
                      begin
                        f x ⊕D 1D
                      ≡⟨ cong₂ _⊕D_ refl (sym (⊕-1 (lift u))) ⟩
                        f x ⊕D (1D ⊕D lift u)
                      ≡⟨ ⊕-a (f x) 1D (lift u) ⟩
                        (f x ⊕D 1D) ⊕D lift u
                      ∎
lift-⊕v ((x ⊗S y) ⊕I 1S) u = 
                      begin
                        lift (iN (x ⊗I y)) ⊕D 1D
                      ≡⟨ cong₂ _⊕D_ refl (sym (⊕-1 (lift u))) ⟩
                        lift (iN (x ⊗I y)) ⊕D (1D ⊕D lift u)
                      ≡⟨ ⊕-a (lift (iN (x ⊗I y))) 1D (lift u) ⟩
                        (lift (iN (x ⊗I y)) ⊕D 1D) ⊕D lift u
                      ∎
lift-⊕v (eS x ⊕I iS y) u = 
                      begin
                        f x ⊕D lift (iN (y ⊕v u))
                      ≡⟨ cong₂ _⊕D_ refl (lift-⊕v y u) ⟩
                        f x ⊕D (lift (iN y) ⊕D lift u)
                      ≡⟨ ⊕-a (f x) (lift (iN y)) (lift u) ⟩
                        (f x ⊕D lift (iN y)) ⊕D lift u
                      ∎
lift-⊕v ((x ⊗S v) ⊕I iS y) u =
                      begin
                        lift (iN (x ⊗I v)) ⊕D lift (iN (y ⊕v u))
                      ≡⟨ cong₂ _⊕D_ refl (lift-⊕v y u) ⟩
                        lift (iN (x ⊗I v)) ⊕D (lift (iN y) ⊕D lift u)
                      ≡⟨ ⊕-a (lift (iN (x ⊗I v))) (lift (iN y)) (lift u) ⟩
                        (lift (iN (x ⊗I v)) ⊕D lift (iN y)) ⊕D lift u
                      ∎
lift-⊕v (x ⊗I y) 0N = sym (⊕-0r (lift (iN (x ⊗I y))))
lift-⊕v (x ⊗I y) 1N = refl
lift-⊕v (x ⊗I y) (iN v) = refl

lift-⊕ : (t u : N) → lift (t ⊕N u) ≡ lift t ⊕D lift u
lift-⊕ 0N u = begin
                lift u
              ≡⟨ sym (⊕-0l (lift u)) ⟩
                0D ⊕D lift u
              ∎
lift-⊕ 1N u = begin
                1D
              ≡⟨ sym (⊕-1 (lift u)) ⟩
                1D ⊕D lift u
              ∎
lift-⊕ (iN t) u = begin
                     lift (iN (t ⊕v u))
                   ≡⟨ lift-⊕v t u ⟩
                     lift (iN t) ⊕D lift u
                   ∎

lift-⊗v : (t : I) (u : N) → lift (iN (t ⊗v u)) ≡ lift (iN t) ⊗D lift u
lift-⊗v (eI x) 1N = sym (⊗-1r (f x))
lift-⊗v (eI x) 0N = refl
lift-⊗v (eI x) (iN y) = refl
lift-⊗v (eP x ⊗I 0P) u = 
                      begin
                        f x ⊗D 0D
                      ≡⟨ cong₂ _⊗D_ refl (sym (⊗-0 (lift u))) ⟩
                        f x ⊗D (0D ⊗D lift u)
                      ≡⟨ ⊗-a (f x) 0D (lift u) ⟩
                        (f x ⊗D 0D) ⊗D lift u
                      ∎
lift-⊗v ((x ⊕P y) ⊗I 0P) u = 
                      begin
                        lift (iN (x ⊕I y)) ⊗D 0D
                      ≡⟨ cong₂ _⊗D_ refl (sym (⊗-0 (lift u))) ⟩
                        lift (iN (x ⊕I y)) ⊗D (0D ⊗D lift u)
                      ≡⟨ ⊗-a (lift (iN (x ⊕I y))) 0D (lift u) ⟩
                        (lift (iN (x ⊕I y)) ⊗D 0D) ⊗D lift u
                      ∎
lift-⊗v (eP x ⊗I iP y) u = 
                      begin
                        f x ⊗D lift (iN (y ⊗v u))
                      ≡⟨ cong₂ _⊗D_ refl (lift-⊗v y u) ⟩
                        f x ⊗D (lift (iN y) ⊗D lift u)
                      ≡⟨ ⊗-a (f x) (lift (iN y)) (lift u) ⟩
                        (f x ⊗D lift (iN y)) ⊗D lift u
                      ∎
lift-⊗v ((x ⊕P v) ⊗I iP y) u =
                      begin
                        lift (iN (x ⊕I v)) ⊗D lift (iN (y ⊗v u))
                      ≡⟨ cong₂ _⊗D_ refl (lift-⊗v y u) ⟩
                        lift (iN (x ⊕I v)) ⊗D (lift (iN y) ⊗D lift u)
                      ≡⟨ ⊗-a (lift (iN (x ⊕I v))) (lift (iN y)) (lift u) ⟩
                        (lift (iN (x ⊕I v)) ⊗D lift (iN y)) ⊗D lift u
                      ∎
lift-⊗v (x ⊕I y) 1N = sym (⊗-1r (lift (iN (x ⊕I y))))
lift-⊗v (x ⊕I y) 0N = refl
lift-⊗v (x ⊕I y) (iN v) = refl

lift-⊗ : (t u : N) → lift (t ⊗N u) ≡ lift t ⊗D lift u
lift-⊗ 1N u = begin
                lift u
              ≡⟨ sym (⊗-1l (lift u)) ⟩
                1D ⊗D lift u
              ∎
lift-⊗ 0N u = begin
                0D
              ≡⟨ sym (⊗-0 (lift u)) ⟩
                0D ⊗D lift u
              ∎
lift-⊗ (iN t) u = begin
                     lift (iN (t ⊗v u))
                   ≡⟨ lift-⊗v t u ⟩
                     lift (iN t) ⊗D lift u
                   ∎


lift-Hom : Hom N-Dioid D-Dioid
lift-Hom = record { map = lift ;
                    map-0 = lift-0 ; 
                    map-1 = lift-1 ;
                    map-⊕ = lift-⊕ ; 
                    map-⊗ = lift-⊗
                  }

-- lift satisface la condición de inyección
prop : (x : X) → lift (inj x) ≡ f x
prop x = refl

-- Suponemos existe otro homomorfismo que satisface la propiedad universal.
postulate h : Hom N-Dioid D-Dioid
open Hom h
postulate h-prop : (x : X) → map (inj x) ≡ f x

-- Mostramos que son iguales
thm : (t : N) → map t ≡ lift t
thm 0N = map-0
thm 1N = map-1
thm (iN (eI x)) = h-prop x
thm (iN (eS x ⊕I 1S)) = begin
                      map (iN (eS x ⊕I 1S))
                    ≡⟨ cong map refl ⟩
                      map ((inj x) ⊕N 1N)
                    ≡⟨ map-⊕ (inj x) 1N ⟩
                      map (inj x) ⊕D map 1N
                    ≡⟨ cong₂ _⊕D_ (h-prop x) map-1 ⟩
                      f x ⊕D 1D
                    ∎
thm (iN (eS x ⊕I iS y)) = begin
                      map (iN (eS x ⊕I iS y))
                    ≡⟨ cong map refl ⟩
                      map ((inj x) ⊕N (iN y))
                    ≡⟨ map-⊕ (inj x) (iN y) ⟩
                      map (inj x) ⊕D map (iN y)
                    ≡⟨ cong₂ _⊕D_ (h-prop x) (thm (iN y)) ⟩
                      f x ⊕D lift (iN y)
                    ∎
thm (iN ((x ⊗S v) ⊕I 1S)) = begin
                      map (iN ((x ⊗S v) ⊕I 1S))
                    ≡⟨ cong map refl ⟩
                      map (iN (x ⊗I v) ⊕N 1N)
                    ≡⟨ map-⊕ (iN (x ⊗I v)) 1N ⟩
                      map (iN (x ⊗I v)) ⊕D map 1N
                    ≡⟨ cong₂ _⊕D_ (thm (iN (x ⊗I v))) map-1 ⟩
                      lift (iN (x ⊗I v)) ⊕D 1D
                    ∎
thm (iN ((x ⊗S v) ⊕I iS y)) = begin
                         map (iN ((x ⊗S v) ⊕I iS y))
                    ≡⟨ cong map refl ⟩
                      map (iN (x ⊗I v) ⊕N (iN y))
                    ≡⟨ map-⊕ (iN (x ⊗I v)) (iN y) ⟩
                      map (iN (x ⊗I v)) ⊕D map (iN y)
                    ≡⟨ cong₂ _⊕D_ (thm (iN (x ⊗I v))) (thm (iN y)) ⟩
                      lift (iN (x ⊗I v)) ⊕D lift (iN y)
                    ∎
thm (iN (eP x ⊗I 0P)) = begin
                      map (iN (eP x ⊗I 0P))
                    ≡⟨ cong map refl ⟩
                      map ((inj x) ⊗N 0N)
                    ≡⟨ map-⊗ (inj x) 0N ⟩
                      map (inj x) ⊗D map 0N
                    ≡⟨ cong₂ _⊗D_ (h-prop x) map-0 ⟩
                      f x ⊗D 0D
                    ∎
thm (iN (eP x ⊗I iP y)) = begin
                      map (iN (eP x ⊗I iP y))
                    ≡⟨ cong map refl ⟩
                      map ((inj x) ⊗N (iN y))
                    ≡⟨ map-⊗ (inj x) (iN y) ⟩
                      map (inj x) ⊗D map (iN y)
                    ≡⟨ cong₂ _⊗D_ (h-prop x) (thm (iN y)) ⟩
                      f x ⊗D lift (iN y)
                    ∎
thm (iN ((x ⊕P v) ⊗I 0P)) = begin
                      map (iN ((x ⊕P v) ⊗I 0P))
                    ≡⟨ cong map refl ⟩
                      map (iN (x ⊕I v) ⊗N 0N)
                    ≡⟨ map-⊗ (iN (x ⊕I v)) 0N ⟩
                      map (iN (x ⊕I v)) ⊗D map 0N
                    ≡⟨ cong₂ _⊗D_ (thm (iN (x ⊕I v))) map-0 ⟩
                      lift (iN (x ⊕I v)) ⊗D 0D
                    ∎
thm (iN ((x ⊕P v) ⊗I iP y)) = begin
                      map (iN ((x ⊕P v) ⊗I iP y))
                    ≡⟨ cong map refl ⟩
                      map (iN (x ⊕I v) ⊗N (iN y))
                    ≡⟨ map-⊗ (iN (x ⊕I v)) (iN y) ⟩
                      map (iN (x ⊕I v)) ⊗D map (iN y)
                    ≡⟨ cong₂ _⊗D_ (thm (iN (x ⊕I v))) (thm (iN y)) ⟩
                      lift (iN (x ⊕I v)) ⊗D lift (iN y)
                    ∎

-- De todo lo anterior, tenemos que N es efectivamente el dioide libre
-- en Set construido sobre X.
