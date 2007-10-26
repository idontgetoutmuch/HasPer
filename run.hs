import System.Process
import System.Exit

main = 
   do pH <- runCommand "gcc -I. -o test *.c"
      ec <- waitForProcess pH
      case ec of
         ExitSuccess ->
            putStrLn "Success"
         ExitFailure n ->
            putStrLn ("Failure " ++ show n)