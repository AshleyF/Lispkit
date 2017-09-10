open System

type Expression =
    | Sym of string
    | Num of int
    | Cons of (Expression * Expression)

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
        | Numeric n :: t -> n |> int |> Num, t
        | Symbolic s :: t -> Sym s, t
        | Delimiter '(' :: t -> let lst, t' = parseList t in lst, t'
        | Delimiter _ :: _ -> failwith "Unexpected character"
        | End :: t -> failwith "Expected token"
        | [] -> failwith "Expected single expression"
    and parseList tokens =
        let head, tokens' = parse' tokens
        match tokens' with
        | Delimiter '.' :: t ->
            match parse' t with
            | tail, (Delimiter ')' :: tokens'') ->  Cons (head, tail), tokens''
            | _ -> failwith "Unexpected expression following dotted pair"
        | Delimiter ')' :: t -> Cons (head, Sym "NIL"), t
        | h :: t -> let lst, t' = parseList t in Cons (head, lst), t'
        | [] -> failwith "Unexpected end of list expression"
    match tokens |> List.ofSeq |> parse' with
    | parsed, [End] -> parsed
    | _ -> failwith "Unexpected trailing tokens"

let print expression =
    let rec print' out comp = function
        | Sym s -> s :: out
        | Num n -> sprintf "%i" n :: out
        | Cons (h, Cons c) ->
            let p = print' [] false h
            let p' = print' [] true (Cons c)
            p' @ " " :: p @ [(if comp then "" else "(")] @ out
        | Cons (h, Sym "NIL") -> let p = print' [] false h in (")" :: p @ [(if comp then "" else "(")] @ out)
        | Cons (h, d) -> let p, p' = print' [] false h, print' [] false d in ")" :: p' @ ["."] @ p @ [(if comp then "" else "(")] @ out
    print' [] false expression |> Seq.rev |> String.Concat

let exec exp args =
    let rec exec' s e c d =
        printfn "DEBUG: S=%s E=%s C=%s D=%s" (print s) (print e) (print c) (print d)
        let rec locate i = function Cons (e', e) -> (if i > 1 then locate (i - 1) e else e') | _ -> failwith "Invalid environment state"
        let rplaca e v = e
        match (s, e, c, d) with 
        | s, e, Cons (Num 1 (* LD *), Cons (Cons (Num n, Num m), c)), d -> exec' (Cons (locate m (locate n e), s)) e c d
        | s, e, Cons (Num 2 (* LDC *), Cons (x, c)), d -> exec' (Cons (x, s)) e c d
        | s, e, Cons (Num 3 (* LDF *), Cons (c', c)), d -> exec' (Cons (Cons (c', e), s)) e c d
        | Cons (Cons (c', e'), Cons (v, s)), e, Cons (Num 4 (* AP *), c), d -> exec' (Sym "NIL") (Cons (v, e')) c' (Cons (s, Cons (e, Cons (c, d))))
        | r, _, Cons (Num 5 (* RTN *), Sym "NIL"), (Cons (s, Cons (e, Cons (c, d)))) -> exec' (Cons (r, s)) e c d
        | s, e, Cons (Num 6 (* DUM *), c), d -> exec' s (Cons (Sym "NIL", e)) c d
        | (Cons (Cons (c', e'), Cons (v, s))), (Cons (Sym "NIL", e)), Cons (Num 7 (* RAP *), c), d -> exec' (Sym "NIL") (rplaca e v) c' (Cons (s, Cons (e, Cons (c, d))))
        | Cons (x, s), e, Cons (Num 8 (* SEL *), Cons (t, Cons (f, c))), d -> exec' s e (if x = Sym "T" then t else f) (Cons (c, d))
        | s, e, Cons (Num 9 (* JOIN *), Sym "NIL"), (Cons (c, d)) -> exec' s e c d
        | Cons (Cons (x, _), s), e, Cons (Num 10 (* CAR *), c), d -> exec' (Cons (x, s)) e c d
        | Cons (Cons (_, x), s), e, Cons (Num 11 (* CDR *), c), d -> exec' (Cons (x, s)) e c d
        | Cons (x, s), e, Cons (Num 12 (* ATOM *), c), d -> exec' (Cons (Sym (match x with Sym _ | Num _ -> "T" | _ -> "F"), s)) e c d
        | Cons (h, Cons (t, s)), e, Cons (Num 13 (* CONS *), c), d -> exec' (Cons (Cons (h, t), s)) e c d
        | Cons (x, Cons (y, s)), e, Cons (Num 14 (* EQ *), c), d -> exec' (Cons (Sym (if y = x then "T" else "F"), s)) e c d
        | Cons (Num x, Cons (Num y, s)), e, Cons (Num 15 (* ADD *), c), d -> exec' (Cons (Num (y + x), s)) e c d
        | Cons (Num x, Cons (Num y, s)), e, Cons (Num 16 (* SUB *), c), d -> exec' (Cons (Num (y - x), s)) e c d
        | Cons (Num x, Cons (Num y, s)), e, Cons (Num 17 (* MUL *), c), d -> exec' (Cons (Num (y * x), s)) e c d
        | Cons (Num x, Cons (Num y, s)), e, Cons (Num 18 (* DIV *), c), d -> exec' (Cons (Num (y / x), s)) e c d
        | Cons (Num x, Cons (Num y, s)), e, Cons (Num 19 (* REM *), c), d -> exec' (Cons (Num (y % x), s)) e c d
        | Cons (Num x, Cons (Num y, s)), e, Cons (Num 20 (* LEQ *), c), d -> exec' (Cons (Sym (if y <= x then "T" else "F"), s)) e c d
        | Cons (r, _), _, Cons (Num 21 (* STOP *), Sym "NIL"), _ -> r
        | _ -> failwith "Invalid machine state"
    exec' (Cons (args, Sym "NIL")) (Sym "NIL") exp (Sym "NIL")

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

testExec "(2 123 2 7 21)" "42" "(7 123 42)" // LDC
testExec "(10 21)" "(7 42 123)" "7" // CAR
testExec "(11 21)" "(7 42 123)" "(42 123)" // CDR
testExec "(12 21)" "7" "T" // ATOM
testExec "(12 21)" "FOO" "T" // ATOM
testExec "(12 21)" "(FOO BAR)" "F" // ATOM
testExec "(2 123 2 7 13 21)" "42" "(7.123)" // CONS
testExec "(2 123 2 7 14 21)" "42" "F" // EQ
testExec "(2 7 2 7 14 21)" "42" "T" // EQ
testExec "(2 FOO 2 BAR 14 21)" "42" "F" // EQ
testExec "(2 FOO 2 FOO 14 21)" "42" "T" // EQ
testExec "(2 123 2 7 15 21)" "42" "130" // ADD
testExec "(2 123 2 7 16 21)" "42" "116" // SUB
testExec "(2 123 2 7 17 21)" "42" "861" // MUL
testExec "(2 123 2 7 18 21)" "42" "17" // DIV
testExec "(2 123 2 7 19 21)" "42" "4" // REM
testExec "(2 123 2 7 20 21)" "42" "F" // LEQ
testExec "(2 7 2 123 20 21)" "42" "T" // LEQ
testExec "(2 7 2 7 20 21)" "42" "T" // LEQ

Console.ReadLine () |> ignore