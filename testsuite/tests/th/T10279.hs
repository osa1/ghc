module T10279 where
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

blah = $(conE (Name (mkOccName "Foo")
                    (NameG VarName rtsPkgKey (mkModName "A"))))
