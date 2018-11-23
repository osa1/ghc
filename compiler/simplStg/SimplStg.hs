{-
(c) The GRASP/AQUA Project, Glasgow University, 1993-1998

\section[SimplStg]{Driver for simplifying @STG@ programs}
-}

{-# LANGUAGE CPP, LambdaCase #-}

module SimplStg ( stg2stg, depSortStg, cafAnalStg ) where

#include "HsVersions.h"

import GhcPrelude

import StgSyn

import StgLint          ( lintStgTopBindings )
import StgStats         ( showStgStats )
import UnariseStg       ( unarise )
import StgCse           ( stgCse )
import Module           ( Module )
import Digraph          ( SCC(..) )
import NameEnv          ( depAnal )
import Name             ( Name )
import Id               ( Id, idName, idCafInfo )
import UniqSet
import NameEnv
import IdInfo           ( CafInfo (..) )

import DynFlags
import ErrUtils
import UniqSupply       ( mkSplitUniqSupply )
import Outputable
import Control.Monad
import Data.List        ( foldl' )

stg2stg :: DynFlags                  -- includes spec of what stg-to-stg passes to do
        -> Module                    -- module being compiled
        -> [StgTopBinding]           -- input program
        -> IO [StgTopBinding]        -- output program

stg2stg dflags this_mod binds
  = do  { showPass dflags "Stg2Stg"
        ; us <- mkSplitUniqSupply 'g'

                -- Do the main business!
        ; dumpIfSet_dyn dflags Opt_D_dump_stg "Pre unarise:"
                        (pprStgTopBindings binds)

        ; stg_linter False "Pre-unarise" binds
        ; let un_binds = unarise us binds
        ; stg_linter True "Unarise" un_binds
         -- Important that unarisation comes first
         -- See Note [StgCse after unarisation] in StgCse

        ; dumpIfSet_dyn dflags Opt_D_dump_stg "STG syntax:"
                        (pprStgTopBindings un_binds)

        ; foldM do_stg_pass un_binds (getStgToDo dflags)
        }

  where
    stg_linter unarised
      | gopt Opt_DoStgLinting dflags
      = lintStgTopBindings dflags this_mod unarised
      | otherwise
      = \ _whodunnit _binds -> return ()

    -------------------------------------------
    do_stg_pass binds to_do
      = case to_do of
          D_stg_stats ->
             trace (showStgStats binds) (return binds)

          StgCSE ->
             {-# SCC "StgCse" #-}
             let
                 binds' = stgCse binds
             in
             end_pass "StgCse" binds'

    end_pass what binds2
      = do -- report verbosely, if required
           dumpIfSet_dyn dflags Opt_D_verbose_stg2stg what
              (pprStgTopBindings binds2)
           stg_linter True what binds2
           return binds2

depSortStg :: [CgStgTopBinding] -> [CgStgTopBinding]
depSortStg pgm =
    concatMap get_binds (depAnal defs deps pgm)
  where
    deps (StgTopLifted (StgNonRec _ rhs)) =
      rhs_deps rhs
    deps (StgTopLifted (StgRec binds)) =
      concatMap (\(_, rhs) -> rhs_deps rhs) binds
    deps (StgTopStringLit _ _) =
      []

    defs (StgTopLifted (StgNonRec bndr _)) =
      [idName bndr]
    defs (StgTopLifted (StgRec binds)) =
      map (\(bndr, _) -> idName bndr) binds
    defs (StgTopStringLit bndr _) =
      [idName bndr]

    rhs_deps :: CgStgRhs -> [Name]
    rhs_deps (StgRhsClosure fvs _ _ _ _) =
      map idName (nonDetEltsUniqSet fvs)
    rhs_deps (StgRhsCon _ _ args) =
      [ idName i | StgVarArg i <- args ]

    get_binds (AcyclicSCC bind) = [bind]
    get_binds (CyclicSCC binds) = binds

-- Should be called with dep sorted Stg!
cafAnalStg :: [CgStgTopBinding] -> NameEnv CafInfo
cafAnalStg = foldl' cafAnalTopBinding emptyNameEnv
  where
    join MayHaveCafRefs _ = MayHaveCafRefs
    join _ MayHaveCafRefs = MayHaveCafRefs
    join NoCafRefs NoCafRefs = NoCafRefs

    cafAnalTopBinding :: NameEnv CafInfo -> CgStgTopBinding -> NameEnv CafInfo
    cafAnalTopBinding env0 bind = case bind of
      StgTopLifted (StgNonRec bndr rhs) ->
        extendNameEnv env0 (idName bndr) (cafAnalRhs env0 rhs)
      StgTopLifted (StgRec binds) ->
        let
          rhs_env =
            extendNameEnvList env0 $
              map (\(bndr, _) -> (idName bndr, NoCafRefs)) binds

          caf_info =
            foldl' join NoCafRefs $
              map (\(_, rhs) -> cafAnalRhs rhs_env rhs) binds
        in
          extendNameEnvList env0 $
            map (\(bndr, _) -> (idName bndr, caf_info)) binds
      StgTopStringLit bndr _ ->
        extendNameEnv env0 (idName bndr) NoCafRefs

    idCafInfo' :: NameEnv CafInfo -> Id -> CafInfo
    idCafInfo' env id =
      case lookupNameEnv env (idName id) of
        Nothing -> idCafInfo id -- must be imported
        Just caf_info -> caf_info

    cafAnalRhs :: NameEnv CafInfo -> CgStgRhs -> CafInfo
    cafAnalRhs env0 (StgRhsClosure fvs _ _ _ _) =
      foldl' join NoCafRefs (map (idCafInfo' env0) (nonDetEltsUniqSet fvs))
    cafAnalRhs env (StgRhsCon _ con args) =
      foldl' join NoCafRefs [ idCafInfo' env i | StgVarArg i <- args ]

-- -----------------------------------------------------------------------------
-- StgToDo:  abstraction of stg-to-stg passes to run.

-- | Optional Stg-to-Stg passes.
data StgToDo
  = StgCSE
  | D_stg_stats

-- | Which optional Stg-to-Stg passes to run. Depends on flags, ways etc.
getStgToDo :: DynFlags -> [StgToDo]
getStgToDo dflags
  = [ StgCSE                   | gopt Opt_StgCSE dflags] ++
    [ D_stg_stats              | stg_stats ]
  where
        stg_stats = gopt Opt_StgStats dflags
