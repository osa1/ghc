{-# LANGUAGE QuasiQuotes, TemplateHaskell #-}

module Main where

import Language.Haskell.TH.Lib
import Language.Haskell.TH.Syntax

-- Should link 'containers' package
import qualified Data.Map as M

import T10279_Instances ()

main :: IO ()
main = do
    let currentPackage :: Package
        currentPackage = $(thisPackage >>= lift)

        basePackages :: [Package]
        basePackages = $(searchPackage "base" Nothing >>= lift)

        containersPackages :: [Package]
        containersPackages = $(searchPackage "containers" Nothing >>= lift)

    putStrLn $ "# of linked packages: " ++
               show (length (packageDepends currentPackage))

    putStrLn $ "# of base packages linked: " ++
               show (length basePackages)

    putStrLn $ "# of containers packages linked: " ++
               show (length containersPackages)
