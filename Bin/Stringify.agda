module Bin.Stringify where

open import Data.Vec using (Vec; _∷_; [])
open import Data.String using (String; fromList; _++_)
open import Bin using (Binary; O; I)

toStringᴮ-big : ∀ {n} → Binary n → String
toStringᴮ-big []       = ""
toStringᴮ-big (O ∷ xs) = "0" ++ toStringᴮ-big xs
toStringᴮ-big (I ∷ xs) = "1" ++ toStringᴮ-big xs

toStringᴮ-little : ∀ {n} → Binary n → String
toStringᴮ-little []       = ""
toStringᴮ-little (O ∷ xs) = toStringᴮ-little xs ++ "0"
toStringᴮ-little (I ∷ xs) = toStringᴮ-little xs ++ "1"
