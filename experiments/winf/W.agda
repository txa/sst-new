{-# OPTIONS --cubical --two-level #-}
{-
A∞-structures (non-unital, unbiased) via the Boardman–Vogt W-construction,
in cubical Agda with the two-level extension (2LTT).

The exo-level (SSet) holds the combinatorics: planar trees, their leaves L,
internal edges E, contraction and cutting of an edge. A W(Ass)-algebra on a
(fibrant) type X gives, for every planar tree T, an |E T|-dimensional cube

    μ T : (E T → I) → X ^ L T → X

with strict faces
    t e = 0 :  μ T t = μ (T/e) t'                (contract e)
    t e = 1 :  μ T t = μ bot t' ∘ (μ top t'' at e)  (cut e, graft)

The faces are stated one at a time as exo-equalities under IsOne, which is
equivalent to a single Sub-type but does not ask Agda to check agreement of
the faces on overlaps when the type is formed (that agreement only holds by
induction over the trees).

BA n bounds the number of leaves by n. Fibrancy of BA n (it is a finite
iterated extension type) and the comparison with Aₙ-structures
(Boardman–Vogt) are meta-level facts, not proved here.
-}
module W where

open import Agda.Primitive
open import Agda.Primitive.Cubical renaming (primINeg to ~_)

-- exo-level basics ------------------------------------------------------

data _≡ᵉ_ {ℓ}{A : Set ℓ}(a : A) : A → SSet ℓ where
  reflᵉ : a ≡ᵉ a

data ℕᵉ : SSet where
  zero : ℕᵉ
  suc  : ℕᵉ → ℕᵉ

_+_ : ℕᵉ → ℕᵉ → ℕᵉ
zero + n = n
suc m + n = suc (m + n)

data ⊥ᵉ : SSet where
record ⊤ᵉ : SSet where
  constructor ttᵉ

data _⊎_ (A B : SSet) : SSet where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

infixr 5 _∷_
data Listᵉ (A : SSet) : SSet where
  []  : Listᵉ A
  _∷_ : A → Listᵉ A → Listᵉ A

_++_ : {A : SSet} → Listᵉ A → Listᵉ A → Listᵉ A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- fibrant powers --------------------------------------------------------

record ⊤ : Set where
  constructor tt

record _×_ (A B : Set) : Set where
  constructor _,_
  field fst : A ; snd : B
open _×_

_^_ : Set → ℕᵉ → Set
X ^ zero = ⊤
X ^ suc n = X × (X ^ n)

module Vec {X : Set} where
  split : (m : ℕᵉ){n : ℕᵉ} → X ^ (m + n) → (X ^ m) × (X ^ n)
  split zero v = tt , v
  split (suc m) (x , v) = let (u , w) = split m v in (x , u) , w

  _⧺_ : {m n : ℕᵉ} → X ^ m → X ^ n → X ^ (m + n)
  _⧺_ {zero} tt v = v
  _⧺_ {suc m} (x , u) v = x , (u ⧺ v)

  pad : (n : ℕᵉ) → X ^ n → X ^ (n + zero)
  pad zero tt = tt
  pad (suc n) (x , v) = x , pad n v
open Vec

-- planar trees ------------------------------------------------------------

-- at least two elements (computes to ⊤ᵉ / ⊥ᵉ, so proofs are unique by η)
Two : {A : SSet} → Listᵉ A → SSet
Two [] = ⊥ᵉ
Two (_ ∷ []) = ⊥ᵉ
Two (_ ∷ _ ∷ _) = ⊤ᵉ

-- every vertex has at least two inputs: no units, no unary operations
data Tree : SSet where
  leaf : Tree
  node : (ts : Listᵉ Tree) → Two ts → Tree

-- leaves
L  : Tree → ℕᵉ
LL : Listᵉ Tree → ℕᵉ
L leaf = suc zero
L (node ts _) = LL ts
LL [] = zero
LL (t ∷ ts) = L t + LL ts

-- internal edges: EC t are the edges a child t contributes to its parent
-- (the edge to t itself, if t is a node, and the edges inside t)
E  : Tree → SSet
EL : Listᵉ Tree → SSet
EC : Tree → SSet
E leaf = ⊥ᵉ
E (node ts _) = EL ts
EL [] = ⊥ᵉ
EL (t ∷ ts) = EC t ⊎ EL ts
EC leaf = ⊥ᵉ
EC (node us _) = ⊤ᵉ ⊎ EL us

-- contraction of an internal edge ---------------------------------------

contract  : (T : Tree) → E T → Tree
contractL : (ts : Listᵉ Tree) → EL ts → Listᵉ Tree
contractC : (t : Tree) → EC t → Listᵉ Tree   -- what replaces the child t
two-contract : (ts : Listᵉ Tree) → Two ts → (e : EL ts) → Two (contractL ts e)

contract (node ts p) e = node (contractL ts e) (two-contract ts p e)
contractL (t ∷ ts) (inl c) = contractC t c ++ ts
contractL (t ∷ ts) (inr e) = t ∷ contractL ts e
contractC (node us p) (inl ttᵉ) = us                   -- splice the children
contractC (node us p) (inr e) = node (contractL us e) (two-contract us p e) ∷ []

two-contract (node (_ ∷ _ ∷ _) _ ∷ _ ∷ _) _ (inl (inl ttᵉ)) = ttᵉ
two-contract (node _ _ ∷ _ ∷ _) _ (inl (inr e)) = ttᵉ
two-contract (_ ∷ node (_ ∷ _ ∷ _) _ ∷ _) _ (inr (inl (inl ttᵉ))) = ttᵉ
two-contract (_ ∷ node _ _ ∷ _) _ (inr (inl (inr e))) = ttᵉ
two-contract (_ ∷ _ ∷ _) _ (inr (inr e)) = ttᵉ

-- edges of the contracted tree are edges of the original one
split-E : (xs ys : Listᵉ Tree) → EL (xs ++ ys) → EL xs ⊎ EL ys
split-E [] ys e = inr e
split-E (x ∷ xs) ys (inl c) = inl (inl c)
split-E (x ∷ xs) ys (inr e) with split-E xs ys e
... | inl e' = inl (inr e')
... | inr e' = inr e'

incl₀  : (T : Tree)(e : E T) → E (contract T e) → E T
incl₀L : (ts : Listᵉ Tree)(e : EL ts) → EL (contractL ts e) → EL ts
incl₀C : (t : Tree)(c : EC t) → EL (contractC t c) → EC t
incl₀ (node ts _) e = incl₀L ts e
incl₀L (t ∷ ts) (inl c) x with split-E (contractC t c) ts x
... | inl y = inl (incl₀C t c y)
... | inr y = inr y
incl₀L (t ∷ ts) (inr e) (inl c) = inl c
incl₀L (t ∷ ts) (inr e) (inr x) = inr (incl₀L ts e x)
incl₀C (node us _) (inl ttᵉ) x = inr x
incl₀C (node us _) (inr e) (inl (inl ttᵉ)) = inl ttᵉ
incl₀C (node us _) (inr e) (inl (inr x)) = inr (incl₀L us e x)

-- inputs of the contracted tree (a reassociation)
module _ {X : Set} where
  join : (xs ys : Listᵉ Tree) → X ^ LL xs → X ^ LL ys → X ^ LL (xs ++ ys)
  join [] ys tt v = v
  join (x ∷ xs) ys u v = let (a , b) = split (L x) u in a ⧺ join xs ys b v

  flat  : (T : Tree)(e : E T) → X ^ L T → X ^ L (contract T e)
  flatL : (ts : Listᵉ Tree)(e : EL ts) → X ^ LL ts → X ^ LL (contractL ts e)
  flatC : (t : Tree)(c : EC t) → X ^ L t → X ^ LL (contractC t c)
  flat (node ts _) e v = flatL ts e v
  flatL (t ∷ ts) (inl c) v = let (a , b) = split (L t) v in join (contractC t c) ts (flatC t c a) b
  flatL (t ∷ ts) (inr e) v = let (a , b) = split (L t) v in a ⧺ flatL ts e b
  flatC (node us _) (inl ttᵉ) v = v
  flatC (node us _) (inr e) v = pad _ (flatL us e v)

-- cutting an internal edge ----------------------------------------------

-- the subtree above the edge, and the tree below it (with a leaf instead)
top  : (T : Tree) → E T → Tree
topL : (ts : Listᵉ Tree) → EL ts → Tree
topC : (t : Tree) → EC t → Tree
top (node ts _) e = topL ts e
topL (t ∷ ts) (inl c) = topC t c
topL (t ∷ ts) (inr e) = topL ts e
topC (node us p) (inl ttᵉ) = node us p
topC (node us _) (inr e) = topL us e

bot  : (T : Tree) → E T → Tree
botL : (ts : Listᵉ Tree) → EL ts → Listᵉ Tree
botC : (t : Tree) → EC t → Tree
two-bot : (ts : Listᵉ Tree) → Two ts → (e : EL ts) → Two (botL ts e)
bot (node ts p) e = node (botL ts e) (two-bot ts p e)
botL (t ∷ ts) (inl c) = botC t c ∷ ts
botL (t ∷ ts) (inr e) = t ∷ botL ts e
botC (node us _) (inl ttᵉ) = leaf
botC (node us p) (inr e) = node (botL us e) (two-bot us p e)
two-bot (_ ∷ _ ∷ _) _ (inl c) = ttᵉ
two-bot (_ ∷ _ ∷ _) _ (inr (inl c)) = ttᵉ
two-bot (_ ∷ _ ∷ _) _ (inr (inr e)) = ttᵉ

inclT  : (T : Tree)(e : E T) → E (top T e) → E T
inclTL : (ts : Listᵉ Tree)(e : EL ts) → E (topL ts e) → EL ts
inclTC : (t : Tree)(c : EC t) → E (topC t c) → EC t
inclT (node ts _) e = inclTL ts e
inclTL (t ∷ ts) (inl c) x = inl (inclTC t c x)
inclTL (t ∷ ts) (inr e) x = inr (inclTL ts e x)
inclTC (node us _) (inl ttᵉ) x = inr x
inclTC (node us _) (inr e) x = inr (inclTL us e x)

inclB  : (T : Tree)(e : E T) → E (bot T e) → E T
inclBL : (ts : Listᵉ Tree)(e : EL ts) → EL (botL ts e) → EL ts
inclBC : (t : Tree)(c : EC t) → EC (botC t c) → EC t
inclB (node ts _) e = inclBL ts e
inclBL (t ∷ ts) (inl c) (inl x) = inl (inclBC t c x)
inclBL (t ∷ ts) (inl c) (inr x) = inr x
inclBL (t ∷ ts) (inr e) (inl x) = inl x
inclBL (t ∷ ts) (inr e) (inr x) = inr (inclBL ts e x)
inclBC (node us _) (inl ttᵉ) ()
inclBC (node us _) (inr e) (inl ttᵉ) = inl ttᵉ
inclBC (node us _) (inr e) (inr x) = inr (inclBL us e x)

-- grafting: feed the inputs above the edge to the top operation
module _ {X : Set} where
  graft  : (T : Tree)(e : E T) → (X ^ L (top T e) → X) → X ^ L T → X ^ L (bot T e)
  graftL : (ts : Listᵉ Tree)(e : EL ts) → (X ^ L (topL ts e) → X) → X ^ LL ts → X ^ LL (botL ts e)
  graftC : (t : Tree)(c : EC t) → (X ^ L (topC t c) → X) → X ^ L t → X ^ L (botC t c)
  graft (node ts _) e f v = graftL ts e f v
  graftL (t ∷ ts) (inl c) f v = let (a , b) = split (L t) v in graftC t c f a ⧺ b
  graftL (t ∷ ts) (inr e) f v = let (a , b) = split (L t) v in a ⧺ graftL ts e f b
  graftC (node us _) (inl ttᵉ) f v = f v , tt
  graftC (node us _) (inr e) f v = graftL us e f v

-- sizes -----------------------------------------------------------------

data _≡ˢ_ {A : SSet}(a : A) : A → SSet where
  reflˢ : a ≡ˢ a

congˢ : {A B : SSet}(f : A → B){a b : A} → a ≡ˢ b → f a ≡ˢ f b
congˢ f reflˢ = reflˢ

_∙ˢ_ : {A : SSet}{a b c : A} → a ≡ˢ b → b ≡ˢ c → a ≡ˢ c
reflˢ ∙ˢ q = q

_≤_ : ℕᵉ → ℕᵉ → SSet
zero ≤ n = ⊤ᵉ
suc m ≤ zero = ⊥ᵉ
suc m ≤ suc n = m ≤ n

≤-refl : (n : ℕᵉ) → n ≤ n
≤-refl zero = ttᵉ
≤-refl (suc n) = ≤-refl n

≤-trans : (a b c : ℕᵉ) → a ≤ b → b ≤ c → a ≤ c
≤-trans zero b c p q = ttᵉ
≤-trans (suc a) (suc b) (suc c) p q = ≤-trans a b c p q

≤-≡ : {a b : ℕᵉ}(c : ℕᵉ) → a ≡ˢ b → b ≤ c → a ≤ c
≤-≡ c reflˢ q = q

≤-+r : (m n : ℕᵉ) → m ≤ (m + n)
≤-+r zero n = ttᵉ
≤-+r (suc m) n = ≤-+r m n

≤-+l : (m n : ℕᵉ) → n ≤ (m + n)
≤-+l zero n = ≤-refl n
≤-+l (suc m) n = ≤-trans n (m + n) (suc (m + n)) (≤-+l m n) (≤-suc (m + n))
  where ≤-suc : (k : ℕᵉ) → k ≤ suc k
        ≤-suc zero = ttᵉ
        ≤-suc (suc k) = ≤-suc k

+-monoˡ : (a b c : ℕᵉ) → a ≤ b → (a + c) ≤ (b + c)
+-monoˡ zero b c p = ≤-+l b c
+-monoˡ (suc a) (suc b) c p = +-monoˡ a b c p

+-monoʳ : (a b c : ℕᵉ) → b ≤ c → (a + b) ≤ (a + c)
+-monoʳ zero b c p = p
+-monoʳ (suc a) b c p = +-monoʳ a b c p

+-assoc : (a b c : ℕᵉ) → ((a + b) + c) ≡ˢ (a + (b + c))
+-assoc zero b c = reflˢ
+-assoc (suc a) b c = congˢ suc (+-assoc a b c)

+-zero : (a : ℕᵉ) → (a + zero) ≡ˢ a
+-zero zero = reflˢ
+-zero (suc a) = congˢ suc (+-zero a)

LL-++ : (xs ys : Listᵉ Tree) → LL (xs ++ ys) ≡ˢ (LL xs + LL ys)
LL-++ [] ys = reflˢ
LL-++ (x ∷ xs) ys = congˢ (L x +_) (LL-++ xs ys) ∙ˢ symˢ (+-assoc (L x) (LL xs) (LL ys))
  where symˢ : {A : SSet}{a b : A} → a ≡ˢ b → b ≡ˢ a
        symˢ reflˢ = reflˢ

-- contraction keeps the leaves
L-contractL : (ts : Listᵉ Tree)(e : EL ts) → LL (contractL ts e) ≡ˢ LL ts
L-contractC : (t : Tree)(c : EC t) → LL (contractC t c) ≡ˢ L t
L-contractL (t ∷ ts) (inl c) = LL-++ (contractC t c) ts ∙ˢ congˢ (_+ LL ts) (L-contractC t c)
L-contractL (t ∷ ts) (inr e) = congˢ (L t +_) (L-contractL ts e)
L-contractC (node us p) (inl ttᵉ) = reflˢ
L-contractC (node us p) (inr e) = +-zero _ ∙ˢ L-contractL us e

-- every tree has a leaf
L-pos : (t : Tree) → suc zero ≤ L t
L-pos leaf = ttᵉ
L-pos (node (u ∷ us) p) = ≤-trans (suc zero) (L u) (L u + LL us) (L-pos u) (≤-+r (L u) (LL us))

L-topL : (ts : Listᵉ Tree)(e : EL ts) → L (topL ts e) ≤ LL ts
L-topC : (t : Tree)(c : EC t) → L (topC t c) ≤ L t
L-topL (t ∷ ts) (inl c) = ≤-trans (L (topC t c)) (L t) (L t + LL ts) (L-topC t c) (≤-+r (L t) (LL ts))
L-topL (t ∷ ts) (inr e) = ≤-trans (L (topL ts e)) (LL ts) (L t + LL ts) (L-topL ts e) (≤-+l (L t) (LL ts))
L-topC (node us p) (inl ttᵉ) = ≤-refl (LL us)
L-topC (node us p) (inr e) = L-topL us e

L-botL : (ts : Listᵉ Tree)(e : EL ts) → LL (botL ts e) ≤ LL ts
L-botC : (t : Tree)(c : EC t) → L (botC t c) ≤ L t
L-botL (t ∷ ts) (inl c) = +-monoˡ (L (botC t c)) (L t) (LL ts) (L-botC t c)
L-botL (t ∷ ts) (inr e) = +-monoʳ (L t) (LL (botL ts e)) (LL ts) (L-botL ts e)
L-botC (node us p) (inl ttᵉ) = L-pos (node us p)
L-botC (node us p) (inr e) = L-botL us e

module _ {n : ℕᵉ} where
  ≤-contract : (T : Tree)(e : E T) → L T ≤ n → L (contract T e) ≤ n
  ≤-contract (node ts p) e s = ≤-≡ n (L-contractL ts e) s

  ≤-top : (T : Tree)(e : E T) → L T ≤ n → L (top T e) ≤ n
  ≤-top (node ts p) e s = ≤-trans (L (topL ts e)) (LL ts) n (L-topL ts e) s

  ≤-bot : (T : Tree)(e : E T) → L T ≤ n → L (bot T e) ≤ n
  ≤-bot (node ts p) e s = ≤-trans (LL (botL ts e)) (LL ts) n (L-botL ts e) s

-- Aₙ-structures (non-unital, unbiased) as W(Ass)-algebras ----------------

-- one cube per planar tree with at most n leaves, with strict faces
record BA (n : ℕᵉ)(X : Set) : SSet where
  field
    μ : (T : Tree) → L T ≤ n → (E T → I) → X ^ L T → X

    -- a leaf is the identity, so it carries no data
    μ-leaf : (s : L leaf ≤ n)(t : E leaf → I)(v : X ^ L leaf) → μ leaf s t v ≡ᵉ fst v

    -- t e = 0: contract the edge
    face₀ : (T : Tree)(s : L T ≤ n)(e : E T)(t : E T → I) → IsOne (~ t e) → (v : X ^ L T)
          → μ T s t v ≡ᵉ μ (contract T e) (≤-contract T e s) (λ x → t (incl₀ T e x)) (flat T e v)

    -- t e = 1: cut the edge and graft
    face₁ : (T : Tree)(s : L T ≤ n)(e : E T)(t : E T → I) → IsOne (t e) → (v : X ^ L T)
          → μ T s t v ≡ᵉ μ (bot T e) (≤-bot T e s) (λ x → t (inclB T e x))
                          (graft T e (μ (top T e) (≤-top T e s) (λ x → t (inclT T e x))) v)

-- sanity check: endofunctions under composition ----------------------------
-- Composition is strictly associative, so all cubes are constant (the product
-- of the inputs in order) and every face holds by induction. The order of
-- inputs matters, so this checks flat and graft.

module Endo (A : Set) where
  X : Set
  X = A → A

  infix 4 _≐_
  _≐_ : X → X → SSet
  f ≐ g = _≡ᵉ_ {A = X} f g

  symᵉ : {a b : X} → a ≐ b → b ≐ a
  symᵉ reflᵉ = reflᵉ

  _∙ᵉ_ : {a b c : X} → a ≐ b → b ≐ c → a ≐ c
  reflᵉ ∙ᵉ q = q

  cong∘ : {f f' g g' : X} → f ≐ f' → g ≐ g' → (λ a → f (g a)) ≐ (λ a → f' (g' a))
  cong∘ reflᵉ reflᵉ = reflᵉ

  prod : {n : ℕᵉ} → X ^ n → X
  prod {zero} tt = λ a → a
  prod {suc n} (x , v) = λ a → x (prod v a)

  prod-⧺ : {m n : ℕᵉ}(u : X ^ m)(w : X ^ n) → prod (u ⧺ w) ≐ (λ a → prod u (prod w a))
  prod-⧺ {zero} tt w = reflᵉ
  prod-⧺ {suc m} (x , u) w = cong∘ {f = x} reflᵉ (prod-⧺ u w)

  prod-split : (m : ℕᵉ){n : ℕᵉ}(v : X ^ (m + n))
             → prod v ≐ (λ a → prod (fst (split m v)) (prod (snd (split m v)) a))
  prod-split zero v = reflᵉ
  prod-split (suc m) (x , v) = cong∘ {f = x} reflᵉ (prod-split m v)

  prod-join : (xs ys : Listᵉ Tree)(u : X ^ LL xs)(w : X ^ LL ys)
            → prod (join xs ys u w) ≐ (λ a → prod u (prod w a))
  prod-join [] ys tt w = reflᵉ
  prod-join (x ∷ xs) ys u w =
    let (a , b) = split (L x) u in
    prod-⧺ a (join xs ys b w)
    ∙ᵉ (cong∘ {f = prod a} reflᵉ (prod-join xs ys b w)
    ∙ᵉ symᵉ (cong∘ {g = prod w} (prod-split (L x) u) reflᵉ))

  prod-pad : (n : ℕᵉ)(v : X ^ n) → prod (pad n v) ≐ prod v
  prod-pad zero tt = reflᵉ
  prod-pad (suc n) (x , v) = cong∘ {f = x} reflᵉ (prod-pad n v)

  prod-flatL : (ts : Listᵉ Tree)(e : EL ts)(v : X ^ LL ts) → prod (flatL ts e v) ≐ prod v
  prod-flatC : (t : Tree)(c : EC t)(v : X ^ L t) → prod (flatC t c v) ≐ prod v
  prod-flatL (t ∷ ts) (inl c) v =
    let (a , b) = split (L t) v in
    prod-join (contractC t c) ts (flatC t c a) b
    ∙ᵉ (cong∘ (prod-flatC t c a) reflᵉ ∙ᵉ symᵉ (prod-split (L t) v))
  prod-flatL (t ∷ ts) (inr e) v =
    let (a , b) = split (L t) v in
    prod-⧺ a (flatL ts e b)
    ∙ᵉ (cong∘ {f = prod a} reflᵉ (prod-flatL ts e b) ∙ᵉ symᵉ (prod-split (L t) v))
  prod-flatC (node us p) (inl ttᵉ) v = reflᵉ
  prod-flatC (node us p) (inr e) v = prod-pad _ (flatL us e v) ∙ᵉ prod-flatL us e v

  prod-graftL : (ts : Listᵉ Tree)(e : EL ts)(v : X ^ LL ts) → prod (graftL ts e prod v) ≐ prod v
  prod-graftC : (t : Tree)(c : EC t)(v : X ^ L t) → prod (graftC t c prod v) ≐ prod v
  prod-graftL (t ∷ ts) (inl c) v =
    let (a , b) = split (L t) v in
    prod-⧺ (graftC t c prod a) b
    ∙ᵉ (cong∘ (prod-graftC t c a) reflᵉ ∙ᵉ symᵉ (prod-split (L t) v))
  prod-graftL (t ∷ ts) (inr e) v =
    let (a , b) = split (L t) v in
    prod-⧺ a (graftL ts e prod b)
    ∙ᵉ (cong∘ {f = prod a} reflᵉ (prod-graftL ts e b) ∙ᵉ symᵉ (prod-split (L t) v))
  prod-graftC (node us p) (inl ttᵉ) v = reflᵉ
  prod-graftC (node us p) (inr e) v = prod-graftL us e v

  endo : (n : ℕᵉ) → BA n X
  endo n = record
    { μ = λ T s t v → prod v
    ; μ-leaf = λ s t v → reflᵉ
    ; face₀ = λ { (node ts p) s e t o v → symᵉ (prod-flatL ts e v) }
    ; face₁ = λ { (node ts p) s e t o v → symᵉ (prod-graftL ts e v) }
    }
