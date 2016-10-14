import Tests
import Regular (from)

-- Main program
main :: IO ()
main =  do
    print tree
    putStrLn $ show (from tree) ++ "\n"
    runTests
