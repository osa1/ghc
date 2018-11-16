/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-2009
 *
 * Stable Names
 *
 * Do not #include this file directly: #include "Rts.h" instead.
 *
 * To understand the structure of the RTS headers, see the wiki:
 *   http://ghc.haskell.org/trac/ghc/wiki/Commentary/SourceTree/Includes
 *
 * ---------------------------------------------------------------------------*/

#pragma once

/* -----------------------------------------------------------------------------
   PRIVATE from here.
   -------------------------------------------------------------------------- */

typedef struct {
    // Haskell object when entry is in use, next free entry (NULL when this is
    // the last free entry) otherwise. May be NULL temporarily during GC (when
    // pointee dies).
    StgPtr  addr;

    // Old Haskell object, used during GC
    StgPtr  old;

    // The StableName object, or NULL when the entry is free
    StgClosure *sn_obj;
} snEntry;

extern DLL_IMPORT_RTS snEntry *stable_name_table;
