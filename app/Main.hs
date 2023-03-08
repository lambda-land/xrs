module Main where


import Lang.Evaluation

import System.Environment (getArgs)


main :: IO ()
main = do
  args <- getArgs
  print (evalExample (args !! 0))