{-# LANGUAGE TemplateHaskellQuotes #-}
module TH_top_splice where

-- Should be a compile time error as TemplateHaskell is not enabled.

qux = $$([|| 1 ||])

foo = $([| 1 |])

