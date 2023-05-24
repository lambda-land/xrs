{-# OPTIONS_GHC -ddump-splices #-}
{-# LANGUAGE TemplateHaskell #-}

module Meta.Experiment where

import Meta.ExperimentTH
import Language.Haskell.TH



data MyData2 = D2 Int String (Int, String) Int deriving (Show)
deriveA ''MyData2

data MyData3 = D3 { field1 :: Int, field2 :: String, field3 :: (Int, String), field4 :: Int } deriving (Show)
deriveA ''MyData3

-- getConstructorBody' ''MyData3

-- deriveScore ''MyData3



data Car = ConsCar { year :: Int, miles :: Int } deriving Show

metaCar :: Q [Dec]
metaCar = [d| data Car = ConsCar { year :: Int, miles :: Int } deriving Show |]

metaCarScore :: Q [Dec]
metaCarScore = [d| 
  data Car = ConsCar { year :: Int, miles :: Int } deriving Show
  instance Score Car where
    score (ConsCar y m) = score y * score m
  |]

deriveScore ''Car

-- metaTest :: Q [Dec]
metaTest :: Q [Dec]
metaTest = [d| 
  data C1 = C1 Int Int
  f (C1 y m) = score y * score m
  |]


-- main :: IO ()
-- main = print (a :: MyData2)