-- (c) The GRASP/AQUA Project, Glasgow University, 1992-1998
{-# LANGUAGE CPP #-}

-----------------------------------------------------------------------------
-- Generate CAF cost centres

module SCCfinal ( stgMassageForProfiling ) where

#include "HsVersions.h"

import GhcPrelude

import StgSyn

import CostCentre       -- lots of things
import Id
import Name
import Module
import UniqSupply       ( UniqSupply )
import Outputable
import DynFlags
import FastString
import SrcLoc
import Util

import Control.Monad (liftM, ap)

stgMassageForProfiling
        :: DynFlags
        -> Module                       -- module name
        -> UniqSupply                   -- unique supply
        -> [StgTopBinding]              -- input
        -> (CollectedCCs, [StgTopBinding])

stgMassageForProfiling dflags mod_name _us stg_binds
  = let
        ((local_ccs, cc_stacks),
         stg_binds2)
          = initMM (do_top_bindings stg_binds)

        (fixed_ccs, fixed_cc_stacks)
          = if gopt Opt_AutoSccsOnIndividualCafs dflags
            then ([],[])  -- don't need "all CAFs" CC
            else ([all_cafs_cc], [all_cafs_ccs])
    in
    ((fixed_ccs ++ local_ccs,
      fixed_cc_stacks ++ cc_stacks), stg_binds2)
  where

    span = mkGeneralSrcSpan (mkFastString "<entire-module>") -- XXX do better
    all_cafs_cc  = mkAllCafsCC mod_name span
    all_cafs_ccs = mkSingletonCCS all_cafs_cc

    ----------
    do_top_bindings :: [StgTopBinding] -> MassageM [StgTopBinding]

    do_top_bindings [] = return []

    do_top_bindings (StgTopLifted (StgNonRec b rhs) : bs) = do
        rhs' <- do_top_rhs b rhs
        bs' <- do_top_bindings bs
        return (StgTopLifted (StgNonRec b rhs') : bs')

    do_top_bindings (StgTopLifted (StgRec pairs) : bs) = do
        pairs2 <- mapM do_pair pairs
        bs' <- do_top_bindings bs
        return (StgTopLifted (StgRec pairs2) : bs')
      where
        do_pair (b, rhs) = do
             rhs2 <- do_top_rhs b rhs
             return (b, rhs2)

    do_top_bindings (b@StgTopStringLit{} : bs) = do
        bs' <- do_top_bindings bs
        return (b : bs')

    ----------
    do_top_rhs :: Id -> StgRhs -> MassageM StgRhs

    do_top_rhs binder (StgRhsClosure _ bi fv u [] body)
      = do
        -- Top level CAF without a cost centre attached
        -- Attach CAF cc (collect if individual CAF ccs)
        caf_ccs <- if gopt Opt_AutoSccsOnIndividualCafs dflags
                   then let cc = mkAutoCC binder modl CafCC
                            ccs = mkSingletonCCS cc
                                   -- careful: the binder might be :Main.main,
                                   -- which doesn't belong to module mod_name.
                                   -- bug #249, tests prof001, prof002
                            modl | Just m <- nameModule_maybe (idName binder) = m
                                 | otherwise = mod_name
                        in do
                        collectNewCC  cc
                        collectCCS ccs
                        return ccs
                   else
                        return all_cafs_ccs
        return (StgRhsClosure caf_ccs bi fv u [] body)

    do_top_rhs _ rhs@StgRhsClosure{}
      = return rhs

    do_top_rhs _ rhs@StgRhsCon{}
      = return rhs

-- -----------------------------------------------------------------------------
-- Boring monad stuff for this

newtype MassageM result
  = MassageM {
      unMassageM :: CollectedCCs
                 -> (CollectedCCs, result)
    }

instance Functor MassageM where
      fmap = liftM

instance Applicative MassageM where
      pure x = MassageM (\ccs -> (ccs, x))
      (<*>) = ap
      (*>) = thenMM_

instance Monad MassageM where
    (>>=) = thenMM
    (>>)  = (*>)

-- the initMM function also returns the final CollectedCCs

initMM :: MassageM a
       -> (CollectedCCs, a)

initMM (MassageM m) = m ([],[])

thenMM  :: MassageM a -> (a -> MassageM b) -> MassageM b
thenMM_ :: MassageM a -> (MassageM b) -> MassageM b

thenMM expr cont = MassageM $ \ccs ->
    case unMassageM expr ccs of { (ccs2, result) ->
    unMassageM (cont result) ccs2 }

thenMM_ expr cont = MassageM $ \ccs ->
    case unMassageM expr ccs of { (ccs2, _) ->
    unMassageM cont ccs2 }

-- Version of collectCC used when we definitely want to declare this
-- CC as local, even if its module name is not the same as the current
-- module name (eg. the special :Main module) see bug #249, #1472,
-- test prof001,prof002.
collectNewCC :: CostCentre -> MassageM ()
collectNewCC cc
 = MassageM $ \(local_ccs, ccss)
              -> ((cc : local_ccs, ccss), ())

collectCCS :: CostCentreStack -> MassageM ()

collectCCS ccs
 = MassageM $ \(local_ccs, ccss)
              -> ASSERT(not (noCCSAttached ccs))
                       ((local_ccs, ccs : ccss), ())
