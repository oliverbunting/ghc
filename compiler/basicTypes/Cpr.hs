{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Cpr (
    Cpr, topCpr, botCpr, sumCpr, prodCpr, returnsCPR_maybe, seqCpr,
    TerminationFlag (..), topTermFlag, botTermFlag,
    Termination, topTerm, botTerm, whnfTerm, prodTerm, sumTerm,
    CprType (..), topCprType, botCprType, prodCprType, sumCprType,
    markProdCprType, markSumCprType, lubCprType, applyCprTy, abstractCprTy,
    abstractCprTyNTimes, ensureCprTyArity, trimCprTy, forceCprTy, forceTerm, bothCprType
  ) where

#include "HsVersions.h"

import GhcPrelude

import BasicTypes
import Demand
import Outputable
import Binary
import Util
import Data.Tuple (swap)

--------------
-- * Levitated

data Levitated a
  = Bot
  | Levitate a
  | Top
  deriving Eq

seqLevitated :: (a -> ()) -> Levitated a -> ()
seqLevitated seq_a (Levitate a) = seq_a a
seqLevitated _     _            = ()

lubLevitated :: (a -> a -> Levitated a) -> Levitated a -> Levitated a -> Levitated a
lubLevitated _     Bot          l            = l
lubLevitated _     l            Bot          = l
lubLevitated _     Top          _            = Top
lubLevitated _     _            Top          = Top
lubLevitated lub_a (Levitate a) (Levitate b) = lub_a a b

---------------
-- * KnownShape

data KnownShape r
  = Product [r]
  | Sum !ConTag [r]
  deriving Eq

seqKnownShape :: (r -> ()) -> KnownShape r -> ()
seqKnownShape seq_r (Product args) = foldr (seq . seq_r) () args
seqKnownShape seq_r (Sum _ args)   = foldr (seq . seq_r) () args

lubKnownShape :: (r -> r -> r) -> KnownShape r -> KnownShape r -> Levitated (KnownShape r)
lubKnownShape lub_r (Product args1) (Product args2)
  | args1 `equalLength` args2
  = Levitate (Product (zipWith lub_r args1 args2))
lubKnownShape lub_r (Sum t1 args1) (Sum t2 args2)
  | t1 == t2, args1 `equalLength` args2
  = Levitate (Sum t1 (zipWith lub_r args1 args2))
lubKnownShape _ _ _
  = Top

----------------
-- * Termination

data TerminationFlag
  = Terminates
  | MightDiverge
  deriving Eq

topTermFlag :: TerminationFlag
topTermFlag = MightDiverge

botTermFlag :: TerminationFlag
botTermFlag = Terminates

lubTermFlag :: TerminationFlag -> TerminationFlag -> TerminationFlag
lubTermFlag MightDiverge _            = MightDiverge
lubTermFlag _            MightDiverge = MightDiverge
lubTermFlag Terminates   Terminates   = Terminates

lubTermFlags :: [TerminationFlag] -> TerminationFlag
lubTermFlags = foldl' lubTermFlag botTermFlag

type Termination' = (TerminationFlag, Levitated (KnownShape Termination))

-- | Normalises wrt. to some non-syntactic equalities, making sure there is only
-- one bottom and top.
liftTermination' :: TerminationFlag -> Levitated (KnownShape Termination) -> Levitated Termination'
liftTermination' Terminates   Bot = Bot
liftTermination' MightDiverge Top = Top
liftTermination' tm           l   = Levitate (tm, l)

newtype Termination
  = Termination (Levitated Termination')
  deriving (Eq, Binary)

topTerm :: Termination
topTerm = Termination Top

botTerm :: Termination
botTerm = Termination Bot

-- | Terminates rapidly to WHNF.
whnfTerm :: Termination
whnfTerm = shallowTerm Terminates

shallowTerm :: TerminationFlag -> Termination
shallowTerm tm
  | tm == topTermFlag = topTerm
  | otherwise         = Termination (Levitate (tm, Top))

deepTerm :: TerminationFlag -> Termination
deepTerm tm
  | tm == botTermFlag = botTerm
  | otherwise         = Termination (Levitate (tm, Bot))

-- Smart contructor for @Termination tm (Just (Product fs))@ that respects the
-- non-syntactic equalities of @Termination@.
prodTerm :: TerminationFlag -> [Termination] -> Termination
prodTerm tm fs
  | all (== topTerm) fs                    = shallowTerm tm
  | all (== botTerm) fs, tm == botTermFlag = botTerm
  | otherwise                              = Termination (Levitate (tm, (Levitate (Product fs))))

-- Smart contructor for @Termination tm (Just (Sum t fs))@ that respects the
-- non-syntactic equalities of @Termination@.
sumTerm :: TerminationFlag -> ConTag -> [Termination] -> Termination
sumTerm tm t fs
  | all (== topTerm) fs                    = shallowTerm tm
  | all (== botTerm) fs, tm == botTermFlag = botTerm
  | otherwise                              = Termination (Levitate (tm, (Levitate (Sum t fs))))

lubTerm :: Termination -> Termination -> Termination
lubTerm (Termination l1) (Termination l2)
  = Termination (lubLevitated lub_pairs l1 l2)
  where
    lub_pairs (tm1, l_sh1) (tm2, l_sh2) =
      liftTermination' (lubTermFlag tm1 tm2)
                       (lubLevitated (lubKnownShape lubTerm) l_sh1 l_sh2)

splitTermination :: Termination -> Termination'
-- Basically the inverse to liftTermination', I guess?!
splitTermination (Termination Top)                = (topTermFlag, Top)
splitTermination (Termination Bot)                = (botTermFlag, Bot)
splitTermination (Termination (Levitate (tm, l))) = (tm, l)

-- Reasons for design:
--  * We want to share between Cpr and Termination, so KnownShape
--  * Cpr is different from Termination in that we give up once one result
--    isn't constructed
--  * That is: For Termination we might or might not have nested info,
--    independent of termination of the current level. This is why Maybe
--    So, i.e. when we return a function (or newtype there-of) we'd have
--    something like @Termination Terminates Nothing@. We know evaluation
--    terminates, but we don't have any information on shape.
--    In fact, it's the same as
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

--------
-- * Cpr

-- | The constructed product result lattice.
--
-- @
--      Top
--       |
--   Levitate shape
--       |
--      Bot
-- @
--
-- where @shape@ lifts the same lattice over 'KnownShape'.
newtype Cpr = Cpr (Levitated (KnownShape Cpr))
  deriving (Eq, Binary)

lubCpr :: Cpr -> Cpr -> Cpr
lubCpr (Cpr l1) (Cpr l2) = Cpr (lubLevitated (lubKnownShape lubCpr) l1 l2)

topCpr :: Cpr
topCpr = Cpr Top

botCpr :: Cpr
botCpr = Cpr Bot

sumCpr :: ConTag -> [Cpr] -> Cpr
sumCpr t _args = Cpr (Levitate (Sum t []))

prodCpr :: [Cpr] -> Cpr
prodCpr args = Cpr (Levitate (Product args))

trimCpr :: Bool -> Bool -> Cpr -> Cpr
trimCpr trim_all trim_sums (Cpr (Levitate Sum{}))
  | trim_all || trim_sums      = topCpr
trimCpr trim_all _         (Cpr (Levitate Product{}))
  | trim_all                   = topCpr
trimCpr _        _         cpr = cpr

returnsCPR_maybe :: Termination -> Cpr -> Maybe (ConTag, [Termination], [Cpr])
returnsCPR_maybe term (Cpr (Levitate (Sum t cprs)))
  | Terminates <- tm = Just (t, terms, cprs)
  where
    (tm, l_sh) = splitTermination term
    terms = case l_sh of
      Bot                     -> zipWith const (repeat botTerm) cprs
      Levitate (Sum t2 terms) -> ASSERT( t == t2 )
                                 ASSERT( cprs `equalLength` terms )
                                 terms
      _                       -> zipWith const (repeat topTerm) cprs
returnsCPR_maybe term (Cpr (Levitate (Product cprs)))
  | Terminates <- tm = Just (fIRST_TAG, terms, cprs)
  where
    (tm, l_sh) = splitTermination term
    terms = case l_sh of
      Bot                      -> zipWith const (repeat botTerm) cprs
      Levitate (Product terms) -> ASSERT( cprs `equalLength` terms )
                                  terms
      _                        -> zipWith const (repeat topTerm) cprs
returnsCPR_maybe _ _                          = Nothing

seqCpr :: Cpr -> ()
seqCpr (Cpr l) = seqLevitated (seqKnownShape seqCpr) l

------------
-- * CprType

-- TODO: Maybe formulate CprType like this?
-- data CprType' = TerminatingCall CprType | Ret Cpr Termination
--   deriving Eq
-- data CprType = CT (Levitated CprType')
--   deriving Eq

-- | The abstract domain \(A_t\) from the original 'CPR for Haskell' paper.
data CprType
  = CprType
  { ct_args :: !Arity       -- ^ Number of arguments the denoted expression eats
                            --   before returning the 'ct_cpr' and 'ct_term'
  , ct_cpr  :: !Cpr         -- ^ 'Cpr' eventually unleashed when applied to
                            --   'ct_args' arguments
  , ct_term :: !Termination -- ^ 'Termination' unleashed when applied to
                            --   'ct_args' arguments
  }

instance Eq CprType where
  a == b =  ct_cpr a  == ct_cpr b
         && ct_term a == ct_term b
         && (ct_args a == ct_args b || isTopCprType a)

isTopCprType :: CprType -> Bool
isTopCprType (CprType _ cpr term) = cpr == topCpr && term == topTerm

-- | Is this ultimately 'botCprType' when applied to enough arguments?
isUltimatelyBotCprType :: CprType -> Bool
isUltimatelyBotCprType (CprType _ cpr term) = cpr == botCpr && term == botTerm

topCprType :: CprType
topCprType = CprType 0 topCpr topTerm

botCprType :: CprType
botCprType = CprType 0 botCpr botTerm

prodCprType :: [CprType] -> CprType
prodCprType args = CprType 0 (prodCpr cprs) (prodTerm Terminates terms)
  where
    (cprs, terms) = unzip (extractArgCprAndTermination args)

extractArgCprAndTermination :: [CprType] -> [(Cpr, Termination)]
extractArgCprAndTermination = map go
  where
    go (CprType 0 cpr term) = (cpr, term)
    -- we didn't give it enough arguments, so terminates rapidly
    go _                    = (topCpr, whnfTerm)

sumCprType :: ConTag -> [CprType] -> CprType
sumCprType con_tag args = CprType 0 (sumCpr con_tag cprs) (sumTerm Terminates con_tag terms)
  where
    (cprs, terms) = unzip (extractArgCprAndTermination args)


markProdCprType :: [CprType] -> CprType -> CprType
markProdCprType args ty = ASSERT( 0 == ct_args ty ) ty { ct_cpr = prodCpr cprs }
  where
    cprs = map fst (extractArgCprAndTermination args)

markSumCprType :: ConTag -> [CprType] -> CprType -> CprType
markSumCprType con_tag args ty = ASSERT( ct_args ty == 0 ) ty { ct_cpr = sumCpr con_tag cprs }
  where
    cprs = map fst (extractArgCprAndTermination args)

lubCprType :: CprType -> CprType -> CprType
lubCprType ty1@(CprType n1 cpr1 term1) ty2@(CprType n2 cpr2 term2)
  -- The arity of bottom CPR types can be extended arbitrarily.
  | isUltimatelyBotCprType ty1 && (n1 <= n2) = ty2
  | isUltimatelyBotCprType ty2 && (n2 <= n1) = ty1
  -- There might be non-bottom CPR types with mismatching arities.
  -- Consider test DmdAnalGADTs. We want to return topCpr in these cases.
  -- But at the same time, we have to preserve strictness obligations wrt.
  -- Termination. Returning topCprType is a safe default.
  | n1 == n2
  = CprType n1 (lubCpr cpr1 cpr2) (lubTerm term1 term2)
  | otherwise
  = topCprType

applyCprTy :: CprType -> CprType
applyCprTy ty@(CprType 0 _ _)
  | ty == botCprType = botCprType
  | otherwise        = topCprType
applyCprTy (CprType n cpr term)
  = CprType (n-1) cpr term

abstractCprTy :: CprType -> CprType
abstractCprTy = abstractCprTyNTimes 1

abstractCprTyNTimes :: Arity -> CprType -> CprType
abstractCprTyNTimes n ty@(CprType m cpr term)
  | isTopCprType ty = topCprType
  | otherwise       = CprType (n+m) cpr term

ensureCprTyArity :: Arity -> CprType -> CprType
ensureCprTyArity n ty@(CprType m _ _)
  | n == m    = ty
  | otherwise = topCprType

trimCprTy :: Bool -> Bool -> CprType -> CprType
trimCprTy trim_all trim_sums (CprType arty cpr term)
  = CprType arty (trimCpr trim_all trim_sums cpr) term

-- | Forces possibly deep 'Termination' info of a 'CprType' according to
-- incoming 'ArgStr'. If there's any possibility that this 'MightDiverge',
-- return that.
forceCprTy :: ArgStr -> CprType -> (TerminationFlag, CprType)
-- TODO: This doesn't consider strict fields yet, I think
forceCprTy arg_str ty = force_term_ty (toStrDmd arg_str) ty
  where
    force_term_ty :: (Str (), StrDmd) -> CprType -> (TerminationFlag, CprType)
    force_term_ty (Lazy, _) ty = (botTermFlag, ty)
    force_term_ty (_, str) (CprType 0 cpr term) = (flag, CprType 0 cpr term')
      where
        (flag, term') = forceTerm (Str str) term
    force_term_ty (_, str) ty = (flag, abstractCprTy ty')
      where
        (flag, ty') = force_term_ty (swap (peelStrCall str)) (applyCprTy ty)

forceTerm :: ArgStr -> Termination -> (TerminationFlag, Termination)
forceTerm arg_str (Termination l) = (flag, Termination l')
  where
    (flag, l') = force_term' arg_str l

    force_term' :: ArgStr -> Levitated Termination' -> (TerminationFlag, Levitated Termination')
    force_term' _                  Bot                   = (botTermFlag, Bot) -- everything Terminates anyway
    force_term' Lazy               t                     = (botTermFlag, t) -- lazy = not forced = Terminates
    force_term' (Str (SCall _))    t                     = (topTermFlag, t) -- we have no info about more incoming arguments
    force_term' (Str HyperStr)     _                     = (topTermFlag, Bot) -- dito; botTerm is already handled above
    force_term' (Str HeadStr)      (Levitate (tm, l_sh)) = (tm, liftTermination' botTermFlag l_sh)
    force_term' (Str HeadStr)      Top                   = force_term' (Str HeadStr) (Levitate (topTermFlag, Top))
    force_term' (Str (SProd args)) (Levitate (tm, l_sh)) = (tm `lubTermFlag` flag, liftTermination' botTermFlag l_sh')
      where
        (flag, l_sh') = force_shape args l_sh
    force_term' (Str (SProd args)) Top                   = force_term' (Str (SProd args)) (Levitate (topTermFlag, Top))

    force_shape :: [ArgStr] -> Levitated (KnownShape Termination) -> (TerminationFlag, Levitated (KnownShape Termination))
    force_shape arg_strs Top = force_shape arg_strs (Levitate (Product (repeat topTerm)))
    force_shape arg_strs (Levitate (Product arg_terms)) = (lubTermFlags flags, sh')
      where
        (flags, shs') = unzip (zipWith forceTerm arg_strs arg_terms)
        sh' -- Yuck, we should have smart constructor for that
          | all (== topTerm) shs' = Top
          | all (== botTerm) shs' = Bot
          | otherwise             = Levitate (Product shs')
    force_shape _        sh       = (botTermFlag, sh) -- We don't currently record strictness in Sums, so no need to force.

-- | 'lubTerm's the given outer @TerminationFlag@ on the @CprType@s 'ct_term'.
bothCprType :: CprType -> TerminationFlag -> CprType
-- deepTerm because we only want to affect the WHNF layer.
-- If tm = Terminates, it's just 'id'.
-- If tm = MightDiverge, it will only set the WHNF layer to MightDiverge,
-- leaving nested termination info (e.g. on product components) intact.
bothCprType ct tm = ct { ct_term = ct_term ct `lubTerm` deepTerm tm }

---------------
-- * Outputable

instance Outputable a => Outputable (Levitated a) where
  ppr Bot = char '⊥'
  ppr Top = char 'T'
  ppr (Levitate a) = ppr a

instance Outputable r => Outputable (KnownShape r) where
  ppr (Sum t fs) = int t <> pprFields fs
  ppr (Product fs) = pprFields fs

pprFields :: Outputable r => [r] -> SDoc
pprFields fs
  | let sdoc = pprWithCommas ppr fs
  = cparen (notNull fs) sdoc

instance Outputable TerminationFlag where
  ppr MightDiverge = char '*'
  ppr Terminates   = char '#'

instance Outputable Termination where
  ppr (Termination l) = case l of
    Top                           -> char '*'
    Bot                           -> text "#.."
    Levitate (tm, Top)            -> ppr tm
    Levitate (tm, Bot)            -> ppr tm <> text "(#..)"
    Levitate (tm, Levitate shape) -> ppr tm <> ppr shape

instance Outputable Cpr where
  ppr (Cpr l) = case l of
    Top            -> char '-'
    Bot            -> char 'b'
    Levitate shape -> ppr shape

instance Outputable CprType where
  ppr (CprType arty cpr term) = ppr arty <+> ppr cpr <+> ppr term

-----------
-- * Binary

instance Binary a => Binary (Levitated a) where
  put_ bh Bot          = putByte bh 0
  put_ bh (Levitate a) = do { putByte bh 1; put_ bh a }
  put_ bh Top          = putByte bh 2
  get  bh = do
    h <- getByte bh
    case h of
      0 -> return Bot
      1 -> Levitate <$> get bh
      2 -> return Top
      _ -> pprPanic "Binary Levitated: Invalid tag" (int (fromIntegral h))

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

instance Binary TerminationFlag where
  put_ bh MightDiverge = put_ bh False
  put_ bh Terminates   = put_ bh True
  get  bh = do
    b <- get bh
    if b
      then pure Terminates
      else pure MightDiverge
