import System.Exit

import qualified BitVectorValueTest
import qualified SolveTest

main :: IO ()
main = do
    good <- and <$> sequence [BitVectorValueTest.runTests, SolveTest.runTests]
    if good
        then exitSuccess
        else exitFailure
