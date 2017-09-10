open System

type Expression =
    | Symbol of string
    | Number of int
    | Composite of (Expression * Expression)

type Token =
    | Symbolic of string
    | Numeric of string
    | Delimiter of char
    | End

let tokenize source =
    let rec skip = function ' ' :: cs -> skip cs | cs -> cs
    let toString = Seq.rev >> Seq.toArray >> String
    let rec number n = function c :: cs when Char.IsDigit c -> number (c :: n) cs | cs -> Numeric (toString n), cs
    let rec symbol s = function c :: cs when Char.IsLetter c || Char.IsDigit c -> symbol (c :: s) cs | cs -> Symbolic (toString s), cs
    let rec tokenize' tokens = function
        | c :: cs when c = '-' || Char.IsDigit c -> let (n, cs') = number [c] cs in tokenize' (n :: tokens) cs'
        | c :: cs when Char.IsLetter c -> let (s, cs') = symbol [c] cs in tokenize' (s :: tokens) cs'
        | c :: cs -> tokenize' (Delimiter c :: tokens) cs
        | [] -> (End :: tokens) |> Seq.rev
    source |> List.ofSeq |> skip |> tokenize' []

let parse tokens =
    let rec parse' = function
        | Numeric n :: t -> n |> int |> Number, t
        | Symbolic s :: t -> Symbol s, t
        | Delimiter '(' :: t -> let lst, t' = parseList t in lst, t'
        | Delimiter _ :: _ -> failwith "Unexpected character"
        | End :: t -> failwith "Expected token"
        | [] -> failwith "Expected single expression"
    and parseList tokens =
        let head, tokens' = parse' tokens
        match tokens' with
        | Delimiter '.' :: t ->
            match parse' t with
            | tail, (Delimiter ')' :: tokens'') ->  Composite (head, tail), tokens''
            | _ -> failwith "Unexpected expression following dotted pair"
        | Delimiter ')' :: t -> Composite (head, Symbol "NIL"), t
        | h :: t -> let lst, t' = parseList t in Composite (head, lst), t'
        | [] -> failwith "Unexpected end of list expression"
    match tokens |> List.ofSeq |> parse' with
    | parsed, [End] -> parsed
    | _ -> failwith "Unexpected trailing tokens"

let print expression =
    let rec print' out comp = function
        | Symbol s -> s :: out
        | Number n -> sprintf "%i" n :: out
        | Composite (h, Composite c) ->
            let p = print' [] false h
            let p' = print' [] true (Composite c)
            p' @ " " :: p @ [(if comp then "" else "(")] @ out
        | Composite (h, Symbol "NIL") -> let p = print' [] false h in (")" :: p @ [(if comp then "" else "(")] @ out)
        | Composite (h, d) -> let p, p' = print' [] false h, print' [] false d in ")" :: p' @ ["."] @ p @ [(if comp then "" else "(")] @ out
    print' [] false expression |> Seq.rev |> String.Concat

let exec exp args =
    let rec exec' s e c d =
        printfn "DEBUG: S=%s E=%s C=%s D=%s" (print s) (print e) (print c) (print d)
        match (s, e, c, d) with 
        | s, e, Composite (Number 1 (* LD *), c), d -> exec' s e c d // TODO
        | s, e, Composite (Number 2 (* LDC *), Composite (x, c)), d -> exec' (Composite (x, s)) e c d
        | s, e, Composite (Number 3 (* LDF *), c), d -> exec' s e c d // TODO
        | s, e, Composite (Number 4 (* AP *), c), d -> exec' s e c d // TODO
        | s, e, Composite (Number 5 (* RTN *), c), d -> exec' s e c d // TODO
        | s, e, Composite (Number 6 (* DUM *), c), d -> exec' s e c d // TODO
        | s, e, Composite (Number 7 (* RAP *), c), d -> exec' s e c d // TODO
        | s, e, Composite (Number 8 (* SEL *), c), d -> exec' s e c d // TODO
        | s, e, Composite (Number 9 (* JOIN *), c), d -> exec' s e c d // TODO
        | Composite (Composite (x, _), s), e, Composite (Number 10 (* CAR *), c), d -> exec' (Composite (x, s)) e c d
        | Composite (Composite (_, x), s), e, Composite (Number 11 (* CDR *), c), d -> exec' (Composite (x, s)) e c d
        | Composite (x, s), e, Composite (Number 12 (* ATOM *), c), d -> exec' (Composite (Symbol (match x with Symbol _ | Number _ -> "T" | _ -> "F"), s)) e c d
        | Composite (h, Composite (t, s)), e, Composite (Number 13 (* CONS *), c), d -> exec' (Composite (Composite (h, t), s)) e c d
        | Composite (x, Composite (y, s)), e, Composite (Number 14 (* EQ *), c), d -> exec' (Composite (Symbol (if y = x then "T" else "F"), s)) e c d
        | Composite (Number x, Composite (Number y, s)), e, Composite (Number 15 (* ADD *), c), d -> exec' (Composite (Number (y + x), s)) e c d
        | Composite (Number x, Composite (Number y, s)), e, Composite (Number 16 (* SUB *), c), d -> exec' (Composite (Number (y - x), s)) e c d
        | Composite (Number x, Composite (Number y, s)), e, Composite (Number 17 (* MUL *), c), d -> exec' (Composite (Number (y * x), s)) e c d
        | Composite (Number x, Composite (Number y, s)), e, Composite (Number 18 (* DIV *), c), d -> exec' (Composite (Number (y / x), s)) e c d
        | Composite (Number x, Composite (Number y, s)), e, Composite (Number 19 (* REM *), c), d -> exec' (Composite (Number (y % x), s)) e c d
        | Composite (Number x, Composite (Number y, s)), e, Composite (Number 20 (* LEQ *), c), d -> exec' (Composite (Symbol (if y <= x then "T" else "F"), s)) e c d
        | s, e, Composite (Number 21 (* STOP *), c), d -> exec' s e c d // TODO
        | s, e, Symbol "NIL", d -> s
        | _ -> failwith "Invalid machine state"
    exec' (Composite (args, Symbol "NIL")) (Symbol "NIL") exp (Symbol "NIL")

let run exp args = exec (exp |> tokenize |> parse) (args |> tokenize |> parse)

let testParse source =
    let tokens = tokenize source
    let expression = parse tokens
    let printed = print expression
    if printed <> source then 
        printfn "!!!ERROR!!!\nSOURCE: %s\nTOKENS: %A\nEXPRESSION: %A\nPRINTED: %s\n" source (List.ofSeq tokens) expression printed

testParse "123"
testParse "FOO"
testParse "(42)"
testParse "(A.B)"
testParse "(A BAY 73)"
testParse "(A (B C) D)"
testParse "(A (D E F) (B.C) 123)"
testParse "(A (B.C) (D E F) 123)"

let testExec exp args expected =
    let result = run exp args |> print
    if result <> expected then printfn "!!!ERROR!!!\nPROGRAM: %s\nARGUMENTS: %s\nEXPECTED: %s\nRESULT: %s" exp args expected result

testExec "(2 123 2 7)" "42" "(7 123 42)" // LDC
testExec "(10)" "(7 42 123)" "(7)" // CAR
testExec "(11)" "(7 42 123)" "((42 123))" // CDR
testExec "(12)" "7" "(T)" // ATOM
testExec "(12)" "FOO" "(T)" // ATOM
testExec "(12)" "(FOO BAR)" "(F)" // ATOM
testExec "(2 123 2 7 13)" "42" "((7.123) 42)" // CONS
testExec "(2 123 2 7 14)" "42" "(F 42)" // EQ
testExec "(2 7 2 7 14)" "42" "(T 42)" // EQ
testExec "(2 FOO 2 BAR 14)" "42" "(F 42)" // EQ
testExec "(2 FOO 2 FOO 14)" "42" "(T 42)" // EQ
testExec "(2 123 2 7 15)" "42" "(130 42)" // ADD
testExec "(2 123 2 7 16)" "42" "(116 42)" // SUB
testExec "(2 123 2 7 17)" "42" "(861 42)" // MUL
testExec "(2 123 2 7 18)" "42" "(17 42)" // DIV
testExec "(2 123 2 7 19)" "42" "(4 42)" // REM
testExec "(2 123 2 7 20)" "42" "(F 42)" // LEQ
testExec "(2 7 2 123 20)" "42" "(T 42)" // LEQ
testExec "(2 7 2 7 20)" "42" "(T 42)" // LEQ

Console.ReadLine () |> ignore