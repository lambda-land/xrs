

module Tests.ExampleTests where


import Logic.Proof
import Lang.Lang
import Lang.Operation
import Lang.Classification
import Lang.ClassificationInstances ()



-- The type of a strategy function
type StrategyFunction = Proof EvalJ -> [EvalJ]


-- The result of picking a list of judgments from a proof tree
type StrategyResult = [EvalJ]



data Trial = Trial { target :: EvalJ,             -- The target judgment
                     expected :: StrategyResult,  -- The expected result
                     results :: [StrategyResult]  -- The results of each strategy
                   }


-- trial1 :: Trial
-- trial1 = Trial { target = (fac 5 => 120)
--                , expected = [fac 4 => 24, 5 * 24 => 120]
--                , results = [
--                     [fac 4 => 24, 5 * (fac 4) => 120],                  -- Results for the first strategy   1/3
--                     [fac 4 => 24, 5 * (fac 4) => 120, 5 * 24 => 120],   -- Second strategy                  2/5
--                     [fac 4 => 24, 120 => 120]                           -- Third strategy                   1/3
--                   ]
--                 }
--                ]}



runTrial :: [StrategyFunction] -> (EvalJ, StrategyResult) -> Trial
runTrial strategies (j, model) 
  = Trial {
      target = j,
      expected = model,
      results = map (\f -> f (prove' j)) strategies
    }


definedStrategies :: [StrategyFunction]
definedStrategies = 
  [ 

  ]