{-# OPTIONS --cubical -W noUnsupportedIndexedMatch #-}
module SemSST where
open import Sem1
open import SSTk using (SST)

SST₁ SST₂ : Set₁
SST₁ = ⟦ SST 1 ⟧C
SST₂ = ⟦ SST 2 ⟧C
