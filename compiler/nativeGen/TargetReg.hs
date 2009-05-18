
-- | Hard wired things related to registers.
--	This is module is preventing the native code generator being able to 
--	emit code for non-host architectures.
--
--	TODO: Do a better job of the overloading, and eliminate this module.
--	We'd probably do better with a Register type class, and hook this to 
--	Instruction somehow.
--
--	TODO: We should also make arch specific versions of RegAlloc.Graph.TrivColorable

module TargetReg (
	targetVirtualRegSqueeze,
	targetRealRegSqueeze,
	targetClassOfRealReg,
	targetMkVirtualReg,
	targetWordSize,
	targetRegDotColor,
	targetClassOfReg
)

where

#include "HsVersions.h"

import Reg
import RegClass
import Size

import CmmExpr	(wordWidth)
import Outputable
import Unique
import FastTypes


#if i386_TARGET_ARCH || x86_64_TARGET_ARCH
import qualified X86.Regs	as X86
import qualified X86.RegInfo	as X86

#elif powerpc_TARGET_ARCH
import qualified PPC.Regs	as PPC
import qualified PPC.RegInfo	as PPC

#elif sparc_TARGET_ARCH	
import qualified SPARC.Regs	as SPARC

#else
#error "RegAlloc.Graph.TargetReg: not defined"
#endif

-- x86 -------------------------------------------------------------------------
#if i386_TARGET_ARCH || x86_64_TARGET_ARCH
targetRegClasses :: Reg -> [RegClass]
targetRegClasses = X86.regClasses

targetRegSupportsClass :: Reg -> RegClass -> Bool
targetRegSupportsClass = X86.regSupportsClass

targetWordSize :: Size
targetWordSize = intSize wordWidth

targetMkVReg :: Unique -> Size -> Reg
targetMkVReg	= X86.mkVReg

targetRegDotColor :: Reg -> SDoc
targetRegDotColor = X86.regDotColor


-- ppc -------------------------------------------------------------------------
#elif powerpc_TARGET_ARCH
targetRegClasses :: Reg -> [RegClass]
targetRegClasses = PPC.regClasses

targetRegSupportsClass :: Reg -> RegClass -> Bool
targetRegSupportsClass = PPC.regSupportsClass

targetWordSize :: Size
targetWordSize = intSize wordWidth

targetMkVReg :: Unique -> Size -> Reg
targetMkVReg	= PPC.mkVReg

targetRegDotColor :: Reg -> SDoc
targetRegDotColor = PPC.regDotColor


-- sparc -----------------------------------------------------------------------
#elif sparc_TARGET_ARCH

targetVirtualRegSqueeze :: RegClass -> VirtualReg -> FastInt
targetVirtualRegSqueeze = SPARC.virtualRegSqueeze

targetRealRegSqueeze :: RegClass -> RealReg -> FastInt
targetRealRegSqueeze = SPARC.realRegSqueeze

targetClassOfRealReg :: RealReg -> RegClass
targetClassOfRealReg = SPARC.classOfRealReg

-- | Size of a machine word. 
--	This is big enough to hold a pointer.
targetWordSize :: Size
targetWordSize = intSize wordWidth

targetMkVirtualReg :: Unique -> Size -> VirtualReg
targetMkVirtualReg = SPARC.mkVirtualReg

targetRegDotColor :: RealReg -> SDoc
targetRegDotColor = SPARC.regDotColor

--------------------------------------------------------------------------------
#else
#error "RegAlloc.Graph.TargetReg: not defined"
#endif


targetClassOfReg :: Reg -> RegClass
targetClassOfReg reg
 = case reg of
 	RegVirtual vr	-> classOfVirtualReg vr
	RegReal rr	-> targetClassOfRealReg rr


