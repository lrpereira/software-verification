module Exemplo2 where

import qualified Prelude

head :: ([] a1) -> a1
head l =
  case l of {
   [] -> Prelude.error "absurd case";
   (:) x _ -> x}

