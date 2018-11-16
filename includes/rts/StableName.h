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

// It's important that SN_ENTRY_FREE is NULL as return value of isAlive is
// directly used as new sn_obj in gcStableNameTable().
#define SN_ENTRY_FREE 0
#define SN_ENTRY_ALLOCATING ((StgClosure*)1)

/* -----------------------------------------------------------------------------
   PRIVATE from here.
   -------------------------------------------------------------------------- */

typedef struct {
    // Haskell object when entry is in use (when sn_obj is not SN_ENTRY_FREE),
    // next free entry otherwise (NULL when this is the last free entry). May be
    // NULL temporarily during GC (when pointee dies).
    StgPtr  addr;

    // Old Haskell object, used during GC.
    StgPtr  old;

    // SN_ENTRY_FREE when the entry is free, SN_ENTRY_ALLOCATING when the entry
    // is being allocated (we run out of heap space after allocating the entry
    // but before allocating the StableName object). Otherwise the StableName
    // object.
    StgClosure *sn_obj;
} snEntry;

extern DLL_IMPORT_RTS snEntry *stable_name_table;
