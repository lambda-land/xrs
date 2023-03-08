module Display.Latex where

class Latex a where
  latex :: a -> String

