module Cpr (
    Cpr, topCpr, botCpr, sumCpr, prodCpr, returnsCPR_maybe, seqCpr,
    CprType (..), topCprType, botCprType, prodCprType, sumCprType,
    lubCprType, applyCprTy, abstractCprTy, ensureCprTyArity, trimCprTy
  ) where

import GhcPrelude

import BasicTypes
import Outputable
import Binary
import Util

data KnownShape r
  = Product [r]
  | Sum !ConTag [r]
  deriving Eq

seqKnownShape :: (r -> ()) -> KnownShape r -> ()
seqKnownShape seq_r (Product args) = foldr (seq . seq_r) () args
seqKnownShape seq_r (Sum _ args)   = foldr (seq . seq_r) () args

-- | The constructed product result lattice.
--
-- @
--      TopCpr
--        |
--   RetCpr shape
--        |
--      BotCpr
-- @
--
-- where @shape@ lifts the same lattice over 'KnownShape'.
data Cpr
  = TopCpr
  | RetCpr (KnownShape Cpr)
  | BotCpr
  deriving Eq

data TerminationFlag
  = Terminates
  | MightDiverge
  deriving Eq

data Termination
  = TopTermination
  | Termination TerminationFlag (Maybe (KnownShape Termination))
  | BotTermination

-- Reasons for design:
--  * We want to share between Cpr and Termination, so KnownShape
--  * Cpr is different from Termination in that we give up once one result
--    isn't constructed
--  * That is: For Termination we might or might not have nested info,
--    independent of termination of the current level. This is why Maybe
--  * Factoring Termination this way (i.e., TerminationFlag x shape) means less
--    duplication
-- Alternative: Interleave everything. Looks like this:
-- data Blub
--   = NoCpr Termination
--   | Cpr TerminationFlag (KnownShape Blub)
--   | BotBlub
--  + More compact
--  + No Maybe (well, not here, still in Termination)
--  + Easier to handle in WW: Termination and Cpr encode compatible shape info
--    by construction
--  - Harder to understand: NoCpr means we can still have Termination info
--  - Spreads Termination stuff between two lattices
-- ... Probably not such a good idea, after all.

lubCpr :: Cpr -> Cpr -> Cpr
lubCpr (RetCpr (Sum t1 args1)) (RetCpr (Sum t2 args2))
  | t1 == t2
  = RetCpr (Sum t1 (zipWithEqual "lubCpr" lubCpr args1 args2))
lubCpr (RetCpr (Product args1)) (RetCpr (Product args2))
  = RetCpr (Product (zipWithEqual "lubCpr" lubCpr args1 args2))
lubCpr BotCpr      cpr     = cpr
lubCpr cpr         BotCpr  = cpr
lubCpr _           _       = TopCpr

topCpr :: Cpr
topCpr = TopCpr

botCpr :: Cpr
botCpr = BotCpr

sumCpr :: ConTag -> Cpr
sumCpr t = RetCpr (Sum t [])

prodCpr :: Cpr
prodCpr = RetCpr (Product [])

trimCpr :: Bool -> Bool -> Cpr -> Cpr
trimCpr trim_all trim_sums (RetCpr Sum{})
  | trim_all || trim_sums      = TopCpr
trimCpr trim_all _         (RetCpr Product{})
  | trim_all                   = TopCpr
trimCpr _        _         cpr = cpr

returnsCPR_maybe :: Cpr -> Maybe ConTag
returnsCPR_maybe (RetCpr (Sum t _)) = Just t
returnsCPR_maybe (RetCpr Product{}) = Just fIRST_TAG
returnsCPR_maybe TopCpr             = Nothing
returnsCPR_maybe BotCpr             = Nothing

seqCpr :: Cpr -> ()
seqCpr (RetCpr shape) = seqKnownShape seqCpr shape
seqCpr _              = ()

--
-- * CprType
--

-- | The abstract domain \(A_t\) from the original 'CPR for Haskell' paper.
data CprType
  = CprType
  { ct_arty :: !Arity    -- ^ Number of arguments the denoted expression eats
                         --   before returning the 'ct_cpr'
  , ct_cpr  :: !Cpr      -- ^ 'Cpr' eventually unleashed when applied to
                         --   'ct_arty' arguments
  }

instance Eq CprType where
  a == b =  ct_cpr a == ct_cpr b
         && (ct_arty a == ct_arty b || ct_cpr a == topCpr)

topCprType :: CprType
topCprType = CprType 0 topCpr

botCprType :: CprType
botCprType = CprType 0 botCpr -- TODO: Figure out if arity 0 does what we want... Yes it does: arity zero means we may unleash it under any number of incoming arguments

prodCprType :: Arity -> CprType
prodCprType _con_arty = CprType 0 prodCpr

sumCprType :: ConTag -> CprType
sumCprType con_tag = CprType 0 (sumCpr con_tag)

lubCprType :: CprType -> CprType -> CprType
lubCprType ty1@(CprType n1 cpr1) ty2@(CprType n2 cpr2)
  -- The arity of bottom CPR types can be extended arbitrarily.
  | cpr1 == botCpr && n1 <= n2 = ty2
  | cpr2 == botCpr && n2 <= n1 = ty1
  -- There might be non-bottom CPR types with mismatching arities.
  -- Consider test DmdAnalGADTs. We want to return top in these cases.
  | n1 == n2                   = CprType n1 (lubCpr cpr1 cpr2)
  | otherwise                  = topCprType

applyCprTy :: CprType -> CprType
applyCprTy (CprType n res)
  | n > 0         = CprType (n-1) res
  | res == botCpr = botCprType
  | otherwise     = topCprType

abstractCprTy :: CprType -> CprType
abstractCprTy (CprType n res)
  | res == topCpr = topCprType
  | otherwise     = CprType (n+1) res

ensureCprTyArity :: Arity -> CprType -> CprType
ensureCprTyArity n ty@(CprType m _)
  | n == m    = ty
  | otherwise = topCprType

trimCprTy :: Bool -> Bool -> CprType -> CprType
trimCprTy trim_all trim_sums (CprType arty res) = CprType arty (trimCpr trim_all trim_sums res)

instance Outputable r => Outputable (KnownShape r) where
  ppr (Sum t fs) = int t <> parens (pprWithCommas ppr fs)
  ppr (Product fs) = parens (pprWithCommas ppr fs)

instance Outputable Cpr where
  ppr TopCpr      = empty
  ppr (RetCpr sh) = char 'm' <> ppr sh
  ppr BotCpr      = char 'b'

instance Outputable CprType where
  ppr (CprType arty res) = ppr arty <> ppr res

instance Binary r => Binary (KnownShape r) where
  -- Note that the ConTag is 1-indexed
  put_ bh (Product fs) = do { put_ bh (0 :: ConTag); put_ bh fs }
  put_ bh (Sum t fs)   = do { put_ bh t; put_ bh fs}
  get  bh = do
    t <- get bh
    fs <- get bh
    case (t :: ConTag) of
      0 -> pure (Product fs)
      _ -> pure (Sum t fs)

instance Binary Cpr where
  put_ bh (RetCpr sh) = do { putByte bh 0; put_ bh sh }
  put_ bh TopCpr      = putByte bh 1
  put_ bh BotCpr      = putByte bh 2

  get  bh = do
    h <- getByte bh
    case h of
      0 -> do { sh <- get bh; return (RetCpr sh) }
      1 -> return TopCpr
      2 -> return BotCpr
      _ -> pprPanic "Binary Cpr: Invalid tag" (int (fromIntegral h))
