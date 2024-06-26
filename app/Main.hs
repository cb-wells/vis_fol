module Main (main) where

import Lib
import System.Environment (getArgs)

main :: IO ()
main = do
    filename <- getArgs
    initialMap <- readInitialMapFromFile (filename!!0)
    interactive (filename!!0) initialMap
