import System.Process
import System.Exit

runTest f =
   runCommands [
      ("asn1c -gen-PER " ++ f, "Failure in asn1c"),
      ("mv converter-sample.c converter-sample.c.old", "Failure in mv of converter-sample.c"),
      ("gcc -I. -o test *.c",  "Failure in gcc")
   ]

runCommands [] =
   return "Success"
runCommands ((c,e):xs) =
   do h <- runCommand c
      d <- waitForProcess h 
      case d of
         ExitSuccess ->
            runCommands xs 
         ExitFailure n ->
            return (e ++ ": " ++ show n)

main = runTest "../Segment.asn1"