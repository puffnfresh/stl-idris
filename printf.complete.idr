module printf

data Format = FLiteral Char Format
            | FString Format
            | FInt Format
            | FEnd

format : String -> Format
format s = f (unpack s)
  where f : List Char -> Format
        f ('%' :: 'd' :: next) = FInt (f next)
        f ('%' :: 's' :: next) = FString (f next)
        f (c :: next) = FLiteral c (f next)
        f [] = FEnd

printfType : Format -> Type
printfType (FLiteral _ next) = printfType next
printfType (FString next) = String -> printfType next
printfType (FInt next) = Int -> printfType next
printfType FEnd = String

printfFormat : (s : Format) -> String -> printfType s
printfFormat (FLiteral c next) s = printfFormat next (s ++ strCons c "")
printfFormat (FString next) s = \t => printfFormat next (s ++ t)
printfFormat (FInt next) s = \t => printfFormat next (s ++ show t)
printfFormat FEnd s = s

sprintf : (s : String) -> printfType (format s)
sprintf s = printfFormat (format s) ""

main : IO ()
main = putStrLn (sprintf "Hello world")
