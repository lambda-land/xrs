module Display.Latex where


import System.Process (callCommand)
import System.IO (readFile, writeFile)


class Latex a where
  latex :: a -> String


render :: Latex a => a -> IO ()
render x = do
  contents <- readFile "tex/template.tex"
  let source = "$$" ++ latex x ++ "$$"
  writeFile "tex/out.tex" $ contents ++ "\n" ++ source ++ "\n\\end{document}"
  callCommand "pdflatex -output-directory=tex tex/out.tex"