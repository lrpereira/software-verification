module Exemplo1 where

import qualified Prelude

data List a =
   Nil
 | Cons a (List a)

head :: (List a1) -> a1
head l =
  case l of {
   Nil -> Prelude.error "absurd case";
   Cons x _ -> x}

