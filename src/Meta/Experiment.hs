{-# OPTIONS_GHC -ddump-splices #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

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

data J1 = ConsJ1 Int Int

deriveContext ''Car ''J1

z :: Q Exp
z = zipn 3

z' = $(zipn 3)
-- main :: IO ()
-- main = print (a :: MyData2)


newtype EqJ = EqJ { isEq :: Bool } deriving Show

-- instance Classify EqJ J1 () where
--   classify () (ConsJ1 x y) _ = EqJ (x == y)


--- deriveClassify ''EqJ ''J1

