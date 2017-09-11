open System

// tokenizer

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

// parser

type Cell = { mutable Head: Expression; Tail: Expression } // this uglyness (record with `mutable Head`) is needed to allow in-place environment update
and Expression =
    | Sym of string
    | Num of int
    | Cons of Cell
let cons h t = Cons { Head = h; Tail = t }
let nil = Sym "NIL"

let parse tokens =
    let rec parse' = function
        | Numeric n :: t -> n |> int |> Num, t
        | Symbolic s :: t -> Sym s, t
        | Delimiter '(' :: t -> let lst, t' = parseList t in lst, t'
        | Delimiter d :: _ -> failwith "Unexpected character"
        | End :: t -> failwith "Expected token"
        | [] -> failwith "Expected single expression"
    and parseList tokens =
        let head, tokens' = parse' tokens
        match tokens' with
        | Delimiter '.' :: t ->
            match parse' t with
            | tail, (Delimiter ')' :: tokens'') -> cons head tail, tokens''
            | _ -> failwith "Unexpected expression following dotted pair"
        | Delimiter ')' :: t -> cons head nil, t
        | h :: t -> let lst, t' = parseList t in cons head lst, t'
        | [] -> failwith "Unexpected end of list expression"
    match tokens |> List.ofSeq |> parse' with
    | parsed, [End] -> parsed
    | _ -> failwith "Unexpected trailing tokens"

// pretty printer

let print expression =
    let rec print' i out comp exp =
        let j = i - 1 // TODO
        if i > 0 then
            match exp with
            | Sym s -> s :: out
            | Num n -> sprintf "%i" n :: out
            | Cons { Head = h; Tail = Cons c } ->
                let p = print' j [] false h
                let p' = print' j [] true (Cons c)
                p' @ " " :: p @ [(if comp then "" else "(")] @ out
            | Cons { Head = h; Tail = Sym "NIL" } -> let p = print' j [] false h in (")" :: p @ [(if comp then "" else "(")] @ out)
            | Cons { Head = h; Tail = d } -> let p, p' = print' j [] false h, print' j [] false d in ")" :: p' @ ["."] @ p @ [(if comp then "" else "(")] @ out
        else "..." :: out
    print' 10000 [] false expression |> Seq.rev |> String.Concat

// SECD machine

let exec exp args =
    let rec exec' s e c d =
        // printfn "DEBUG: S=%s E=%s C=%s D=%s" (print s) (print e) (print c) (print d)
        let rec nth i = function Cons { Head = e'; Tail = e } -> (if i > 0 then nth (i - 1) e else e') | _ -> failwith "Invalid environment state"
        let rplaca e v = match e with Cons e' -> e'.Head <- v; Cons e' | _ -> failwith "Invalid environment" // note: this is the *only* mutation
        match (s, e, c, d) with 
        | s, e, Cons { Head = Num 1 (* LD *); Tail = Cons { Head = Cons { Head = Num n; Tail = Num m }; Tail = c }}, d -> exec' (cons (nth m (nth n e)) s) e c d
        | s, e, Cons { Head = Num 2 (* LDC *); Tail = Cons { Head = x; Tail = c }}, d -> exec' (cons x s) e c d
        | s, e, Cons { Head = Num 3 (* LDF *); Tail = Cons { Head = c'; Tail = c }}, d -> exec' (cons (cons c' e) s) e c d
        | Cons { Head = Cons { Head = c'; Tail = e' }; Tail = Cons { Head = v; Tail = s }}, e, Cons { Head = Num 4 (* AP *); Tail = c }, d -> exec' nil (cons v e') c' (cons s (cons e (cons c d)))
        | Cons { Head = r; Tail = Sym "NIL" }, _, Cons { Head = Num 5 (* RTN *); Tail = Sym "NIL" }, (Cons { Head = s; Tail = Cons { Head = e; Tail = Cons { Head = c; Tail = d }}}) -> exec' (cons r s) e c d
        | s, e, Cons { Head = Num 6 (* DUM *); Tail = c }, d -> exec' s (cons nil e) c d
        | (Cons { Head = Cons { Head = c'; Tail = e' }; Tail = Cons { Head = v; Tail = s }}), (Cons { Head = Sym "NIL"; Tail = e }), Cons { Head = Num 7 (* RAP *); Tail = c }, d -> exec' nil (rplaca e' v) c' (cons s (cons e (cons c d)))
        | Cons { Head = x; Tail = s }, e, Cons { Head = Num 8 (* SEL *); Tail = Cons { Head = t; Tail = Cons { Head = f; Tail = c }}}, d -> exec' s e (if x = Sym "T" then t else f) (cons c d)
        | s, e, Cons { Head = Num 9 (* JOIN *); Tail = Sym "NIL" }, (Cons { Head = c; Tail = d }) -> exec' s e c d
        | Cons { Head = Cons { Head = x; Tail = _ }; Tail = s }, e, Cons { Head = Num 10 (* CAR *); Tail = c }, d -> exec' (cons x s) e c d
        | Cons { Head = Cons { Head = _; Tail = x }; Tail = s }, e, Cons { Head = Num 11 (* CDR *); Tail = c }, d -> exec' (cons x s) e c d
        | Cons { Head = x; Tail = s }, e, Cons { Head = Num 12 (* ATOM *); Tail = c }, d -> exec' (cons (Sym (match x with Sym _ | Num _ -> "T" | _ -> "F")) s) e c d
        | Cons { Head = h; Tail = Cons { Head = t; Tail = s }}, e, Cons { Head = Num 13 (* CONS *); Tail = c }, d -> exec' (cons (cons h t) s) e c d
        | Cons { Head = x; Tail = Cons { Head = y; Tail = s }}, e, Cons { Head = Num 14 (* EQ *); Tail = c }, d -> exec' (cons (Sym (if y = x then "T" else "F")) s) e c d
        | Cons { Head = Num x; Tail = Cons { Head = Num y; Tail = s }}, e, Cons { Head = Num 15 (* ADD *); Tail = c }, d -> exec' (cons (Num (y + x)) s) e c d
        | Cons { Head = Num x; Tail = Cons { Head = Num y; Tail = s }}, e, Cons { Head = Num 16 (* SUB *); Tail = c }, d -> exec' (cons (Num (y - x)) s) e c d
        | Cons { Head = Num x; Tail = Cons { Head = Num y; Tail = s }}, e, Cons { Head = Num 17 (* MUL *); Tail = c }, d -> exec' (cons (Num (y * x)) s) e c d
        | Cons { Head = Num x; Tail = Cons { Head = Num y; Tail = s }}, e, Cons { Head = Num 18 (* DIV *); Tail = c }, d -> exec' (cons (Num (y / x)) s) e c d
        | Cons { Head = Num x; Tail = Cons { Head = Num y; Tail = s }}, e, Cons { Head = Num 19 (* REM *); Tail = c }, d -> exec' (cons (Num (y % x)) s) e c d
        | Cons { Head = Num x; Tail = Cons { Head = Num y; Tail = s }}, e, Cons { Head = Num 20 (* LEQ *); Tail = c }, d -> exec' (cons (Sym (if y <= x then "T" else "F")) s) e c d
        | Cons { Head = r; Tail = _ }, _, Cons { Head = Num 21 (* STOP *); Tail = Sym "NIL" }, _ -> r
        | _ -> failwith "Invalid machine state"
    exec' (Cons { Head = args; Tail = nil }) nil exp nil

let run exp args = exec (exp |> tokenize |> parse) (args |> tokenize |> parse)

// tests

let testParse source =
    let tokens = tokenize source
    let expression = parse tokens
    let printed = print expression
    if printed <> source then 
        printfn "!!!PARSER TEST FAILURE!!!\nSOURCE: %s\nTOKENS: %A\nEXPRESSION: %A\nPRINTED: %s\n" source (List.ofSeq tokens) expression printed

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
    if result <> expected then printfn "!!!SECD MACHINE TEST FAILURE!!!\nPROGRAM: %s\nARGUMENTS: %s\nEXPECTED: %s\nRESULT: %s" exp args expected result

testExec "(2 123 21)" "42" "123" // LDC
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
testExec "(21)" "(B C)" "(B C)" // (STOP)
testExec "(2 A 21)" "42" "A" // (LDC A STOP)
testExec "(2 A 12 21)" "42" "T" // (LDC A ATOM STOP)
testExec "(2 (A) 12 21)" "42" "F" // (LDC (A) ATOM STOP)
testExec "(2 (A) 10 21)" "42" "A" // (LDC (A) CAR STOP)
testExec "(2 A 2 B 13 21)" "42" "(B.A)" // (LDC A LDC B CONS STOP)
testExec "(2 A 2 B 14 21)" "42" "F" // (LDC A LDC B EQ STOP)
testExec "(2 A 2 A 14 21)" "42" "T" // (LDC A LDC A EQ STOP)
testExec "(2 T 8 (2 A 21) (2 B 21))" "42" "A" // (LDC T SEL (LDC A STOP) (LDC B STOP))
testExec "(2 F 8 (2 A 21) (2 B 21))" "42" "B" // (LDC F SEL (LDC A STOP) (LDC B STOP))
testExec "(2 T 8 (2 A 9) (2 B 9) 21)" "42" "A" // (LDC T SEL (LDC A JOIN) (LDC B JOIN) STOP)
testExec "(2 F 8 (2 A 9) (2 B 9) 21)" "42" "B" // (LDC F SEL (LDC A JOIN) (LDC B JOIN) STOP)
testExec "(3 (2 A) 21)" "((B C))" "((2 A))" // (LDF (LDC A) STOP)
testExec "(3 (2 A 21) 4)" "((B C))" "A" // (LDF (LDC A STOP) AP)
testExec "(3 (2 A 5) 4 21)" "((B C))" "A" // (LDF (LDC A RTN) AP STOP)
testExec "(3 (1 (0.0) 21) 4 21)" "((B C))" "(B C)" // (LDF (LD (0.0) RTN) AP STOP)
testExec "(3 (1 (0.1) 21) 4 21)" "((B C) (D E))" "(D E)" // (LDF (LD (0.1) RTN) AP STOP)
testExec "(3 (6 1 (1.0) 21) 4 21)" "((B C))" "(B C)" // (LDF (DUM LD (1.0) RTN) AP STOP)
testExec "(3 (6 1 (1.1) 21) 4 21)" "((B C) (D E))" "(D E)" // (LDF (DUM LD (1.1) RTN) AP STOP)
testExec "(6 3 (1 (0.0) 21) 7)" "((B C))" "(B C)" // (DUM LDF (LD (0.0) STOP) RAP)

// from appendix of Functional Programming - Application and Implementation, Peter Henderson 
let compilerSource = "(LETREC COMPILE (COMPILE LAMBDA (E) (COMP E (QUOTE NIL) (QUOTE (4 21)))) (COMP LAMBDA (E N C) (IF (ATOM E) (CONS (QUOTE 1) (CONS (LOCATION E N) C)) (IF (EQ (CAR E) (QUOTE QUOTE)) (CONS (QUOTE 2) (CONS (CAR (CDR E)) C)) (IF (EQ (CAR E) (QUOTE ADD)) (COMP (CAR (CDR E)) N (COMP (CAR (CDR (CDR E))) N (CONS (QUOTE 15) C))) (IF (EQ (CAR E) (QUOTE SUB)) (COMP (CAR (CDR E)) N (COMP (CAR (CDR (CDR E))) N (CONS (QUOTE 16) C))) (IF (EQ (CAR E) (QUOTE MUL)) (COMP (CAR (CDR E)) N (COMP (CAR (CDR (CDR E))) N (CONS (QUOTE 17) C))) (IF (EQ (CAR E) (QUOTE DIV)) (COMP (CAR (CDR E)) N (COMP (CAR (CDR (CDR E))) N (CONS (QUOTE 18) C))) (IF (EQ (CAR E) (QUOTE REM)) (COMP (CAR (CDR E)) N (COMP (CAR (CDR (CDR E))) N (CONS (QUOTE 19) C))) (IF (EQ (CAR E) (QUOTE LEQ)) (COMP (CAR (CDR E)) N (COMP (CAR (CDR (CDR E))) N (CONS (QUOTE 20) C))) (IF (EQ (CAR E) (QUOTE EQ)) (COMP (CAR (CDR E)) N (COMP (CAR (CDR (CDR E))) N (CONS (QUOTE 14) C))) (IF (EQ (CAR E) (QUOTE CAR)) (COMP (CAR (CDR E)) N (CONS (QUOTE 10) C)) (IF (EQ (CAR E) (QUOTE CDR)) (COMP (CAR (CDR E)) N (CONS (QUOTE 11) C)) (IF (EQ (CAR E) (QUOTE ATOM)) (COMP (CAR (CDR E)) N (CONS (QUOTE 12) C)) (IF (EQ (CAR E) (QUOTE CONS)) (COMP (CAR (CDR (CDR E))) N (COMP (CAR (CDR E)) N (CONS (QUOTE 13) C))) (IF (EQ (CAR E) (QUOTE IF)) (LET (COMP (CAR (CDR E)) N (CONS (QUOTE 8) (CONS THENPT (CONS ELSEPT C)))) (THENPT COMP (CAR (CDR (CDR E))) N (QUOTE (9))) (ELSEPT COMP (CAR (CDR (CDR (CDR E)))) N (QUOTE (9)))) (IF (EQ (CAR E) (QUOTE LAMBDA)) (LET (CONS (QUOTE 3) (CONS BODY C)) (BODY COMP (CAR (CDR (CDR E))) (CONS (CAR (CDR E)) N) (QUOTE (5)))) (IF (EQ (CAR E) (QUOTE LET)) (LET (LET (COMPLIS ARGS N (CONS (QUOTE 3) (CONS BODY (CONS (QUOTE 4) C)))) (BODY COMP (CAR (CDR E)) M (QUOTE (5)))) (M CONS (VARS (CDR (CDR E))) N) (ARGS EXPRS (CDR (CDR E)))) (IF (EQ (CAR E) (QUOTE LETREC)) (LET (LET (CONS (QUOTE 6) (COMPLIS ARGS M (CONS (QUOTE 3) (CONS BODY (CONS (QUOTE 7) C))))) (BODY COMP (CAR (CDR E)) M (QUOTE (5)))) (M CONS (VARS (CDR (CDR E))) N) (ARGS EXPRS (CDR (CDR E)))) (COMPLIS (CDR E) N (COMP (CAR E) N (CONS (QUOTE 4) C))))))))))))))))))))) (COMPLIS LAMBDA (E N C) (IF (EQ E (QUOTE NIL)) (CONS (QUOTE 2) (CONS (QUOTE NIL) C)) (COMPLIS (CDR E) N (COMP (CAR E) N (CONS (QUOTE 13) C))))) (LOCATION LAMBDA (E N) (LETREC (IF (MEMBER E (CAR N)) (CONS (QUOTE 0) (POSN E (CAR N))) (INCAR (LOCATION E (CDR N)))) (MEMBER LAMBDA (E N) (IF (EQ N (QUOTE NIL)) (QUOTE F) (IF (EQ E (CAR N)) (QUOTE T) (MEMBER E (CDR N))))) (POSN LAMBDA (E N) (IF (EQ E (CAR N)) (QUOTE 0) (ADD (QUOTE 1) (POSN E (CDR N))))) (INCAR LAMBDA (L) (CONS (ADD (QUOTE 1) (CAR L)) (CDR L))))) (VARS LAMBDA (D) (IF (EQ D (QUOTE NIL)) (QUOTE NIL) (CONS (CAR (CAR D)) (VARS (CDR D))))) (EXPRS LAMBDA (D) (IF (EQ D (QUOTE NIL)) (QUOTE NIL) (CONS (CDR (CAR D)) (EXPRS (CDR D))))))"
let compilerCode = "(6 2 NIL 3 (1 (0.0) 2 NIL 14 8 (2 NIL 9) (2 NIL 1 (0.0) 11 13 1 (1.5) 4 1 (0.0) 10 11 13 9) 5) 13 3 (1 (0.0) 2 NIL 14 8 (2 NIL 9) (2 NIL 1 (0.0) 11 13 1 (1.4) 4 1 (0.0) 10 10 13 9) 5) 13 3 (6 2 NIL 3 (1 (0.0) 11 2 1 1 (0.0) 10 15 13 5) 13 3 (1 (0.0) 1 (0.1) 10 14 8 (2 0 9) (2 1 2 NIL 1 (0.1) 11 13 1 (0.0) 13 1 (1.1) 4 15 9) 5) 13 3 (1 (0.1) 2 NIL 14 8 (2 F 9) (1 (0.0) 1 (0.1) 10 14 8 (2 T 9) (2 NIL 1 (0.1) 11 13 1 (0.0) 13 1 (1.0) 4 9) 9) 5) 13 3 (2 NIL 1 (1.1) 10 13 1 (1.0) 13 1 (0.0) 4 8 (2 NIL 1 (1.1) 10 13 1 (1.0) 13 1 (0.1) 4 2 0 13 9) (2 NIL 2 NIL 1 (1.1) 11 13 1 (1.0) 13 1 (2.3) 4 13 1 (0.2) 4 9) 5) 7 5) 13 3 (1 (0.0) 2 NIL 14 8 (1 (0.2) 2 NIL 13 2 2 13 9) (2 NIL 2 NIL 1 (0.2) 2 13 13 13 1 (0.1) 13 1 (0.0) 10 13 1 (1.1) 4 13 1 (0.1) 13 1 (0.0) 11 13 1 (1.2) 4 9) 5) 13 3 (1 (0.0) 12 8 (1 (0.2) 2 NIL 1 (0.1) 13 1 (0.0) 13 1 (1.3) 4 13 2 1 13 9) (1 (0.0) 10 2 QUOTE 14 8 (1 (0.2) 1 (0.0) 11 10 13 2 2 13 9) (1 (0.0) 10 2 ADD 14 8 (2 NIL 2 NIL 1 (0.2) 2 15 13 13 1 (0.1) 13 1 (0.0) 11 11 10 13 1 (1.1) 4 13 1 (0.1) 13 1 (0.0) 11 10 13 1 (1.1) 4 9) (1 (0.0) 10 2 SUB 14 8 (2 NIL 2 NIL 1 (0.2) 2 16 13 13 1 (0.1) 13 1 (0.0) 11 11 10 13 1 (1.1) 4 13 1 (0.1) 13 1 (0.0) 11 10 13 1 (1.1) 4 9) (1 (0.0) 10 2 MUL 14 8 (2 NIL 2 NIL 1 (0.2) 2 17 13 13 1 (0.1) 13 1 (0.0) 11 11 10 13 1 (1.1) 4 13 1 (0.1) 13 1 (0.0) 11 10 13 1 (1.1) 4 9) (1 (0.0) 10 2 DIV 14 8 (2 NIL 2 NIL 1 (0.2) 2 18 13 13 1 (0.1) 13 1 (0.0) 11 11 10 13 1 (1.1) 4 13 1 (0.1) 13 1 (0.0) 11 10 13 1 (1.1) 4 9) (1 (0.0) 10 2 REM 14 8 (2 NIL 2 NIL 1 (0.2) 2 19 13 13 1 (0.1) 13 1 (0.0) 11 11 10 13 1 (1.1) 4 13 1 (0.1) 13 1 (0.0) 11 10 13 1 (1.1) 4 9) (1 (0.0) 10 2 LEQ 14 8 (2 NIL 2 NIL 1 (0.2) 2 20 13 13 1 (0.1) 13 1 (0.0) 11 11 10 13 1 (1.1) 4 13 1 (0.1) 13 1 (0.0) 11 10 13 1 (1.1) 4 9) (1 (0.0) 10 2 EQ 14 8 (2 NIL 2 NIL 1 (0.2) 2 14 13 13 1 (0.1) 13 1 (0.0) 11 11 10 13 1 (1.1) 4 13 1 (0.1) 13 1 (0.0) 11 10 13 1 (1.1) 4 9) (1 (0.0) 10 2 CAR 14 8 (2 NIL 1 (0.2) 2 10 13 13 1 (0.1) 13 1 (0.0) 11 10 13 1 (1.1) 4 9) (1 (0.0) 10 2 CDR 14 8 (2 NIL 1 (0.2) 2 11 13 13 1 (0.1) 13 1 (0.0) 11 10 13 1 (1.1) 4 9) (1 (0.0) 10 2 ATOM 14 8 (2 NIL 1 (0.2) 2 12 13 13 1 (0.1) 13 1 (0.0) 11 10 13 1 (1.1) 4 9) (1 (0.0) 10 2 CONS 14 8 (2 NIL 2 NIL 1 (0.2) 2 13 13 13 1 (0.1) 13 1 (0.0) 11 10 13 1 (1.1) 4 13 1 (0.1) 13 1 (0.0) 11 11 10 13 1 (1.1) 4 9) (1 (0.0) 10 2 IF 14 8 (2 NIL 2 NIL 2 (9) 13 1 (0.1) 13 1 (0.0) 11 11 11 10 13 1 (1.1) 4 13 2 NIL 2 (9) 13 1 (0.1) 13 1 (0.0) 11 11 10 13 1 (1.1) 4 13 3 (2 NIL 1 (1.2) 1 (0.1) 13 1 (0.0) 13 2 8 13 13 1 (1.1) 13 1 (1.0) 11 10 13 1 (2.1) 4 5) 4 9) (1 (0.0) 10 2 LAMBDA 14 8 (2 NIL 2 NIL 2 (5) 13 1 (0.1) 1 (0.0) 11 10 13 13 1 (0.0) 11 11 10 13 1 (1.1) 4 13 3 (1 (1.2) 1 (0.0) 13 2 3 13 5) 4 9) (1 (0.0) 10 2 LET 14 8 (2 NIL 2 NIL 1 (0.0) 11 11 13 1 (1.5) 4 13 1 (0.1) 2 NIL 1 (0.0) 11 11 13 1 (1.4) 4 13 13 3 (2 NIL 2 NIL 2 (5) 13 1 (0.0) 13 1 (1.0) 11 10 13 1 (2.1) 4 13 3 (2 NIL 1 (2.2) 2 4 13 1 (0.0) 13 2 3 13 13 1 (2.1) 13 1 (1.1) 13 1 (3.2) 4 5) 4 5) 4 9) (1 (0.0) 10 2 LETREC 14 8 (2 NIL 2 NIL 1 (0.0) 11 11 13 1 (1.5) 4 13 1 (0.1) 2 NIL 1 (0.0) 11 11 13 1 (1.4) 4 13 13 3 (2 NIL 2 NIL 2 (5) 13 1 (0.0) 13 1 (1.0) 11 10 13 1 (2.1) 4 13 3 (2 NIL 1 (2.2) 2 7 13 1 (0.0) 13 2 3 13 13 1 (1.0) 13 1 (1.1) 13 1 (3.2) 4 2 6 13 5) 4 5) 4 9) (2 NIL 2 NIL 1 (0.2) 2 4 13 13 1 (0.1) 13 1 (0.0) 10 13 1 (1.1) 4 13 1 (0.1) 13 1 (0.0) 11 13 1 (1.2) 4 9) 9) 9) 9) 9) 9) 9) 9) 9) 9) 9) 9) 9) 9) 9) 9) 9) 5) 13 3 (2 NIL 2 (4 21) 13 2 NIL 13 1 (0.0) 13 1 (1.1) 4 5) 13 3 (1 (0.0) 5) 7 4 21)"

let compile source = sprintf "(%s)" source |> run compilerCode

let testCompiler source expected = 
    let result = compile source |> print
    if result <> expected then printfn "!!!COMPILER ERROR!!!\nEXPECTED: %s\nRESULT: %s" expected result

testCompiler "(QUOTE A)" "(2 A 4 21)" // (LDC A AP STOP)
testCompiler "(CAR (QUOTE A))" "(2 A 10 4 21)" // (LDC A CAR AP STOP)
testCompiler "(CDR (QUOTE A))" "(2 A 11 4 21)" // (LDC A CDR AP STOP)
testCompiler "(ATOM (QUOTE A))" "(2 A 12 4 21)" // (LDC A ATOM AP STOP)
testCompiler "(CONS (QUOTE A) (QUOTE B))" "(2 B 2 A 13 4 21)" // (LDC B LDC A CONS AP STOP)
testCompiler "(ADD (QUOTE A) (QUOTE B))" "(2 A 2 B 15 4 21)" // (LDC A LDC B ADD AP STOP)
testCompiler "(SUB (QUOTE A) (QUOTE B))" "(2 A 2 B 16 4 21)" // (LDC A LDC B SUB AP STOP)
testCompiler "(MUL (QUOTE A) (QUOTE B))" "(2 A 2 B 17 4 21)" // (LDC A LDC B MUL AP STOP)
testCompiler "(DIV (QUOTE A) (QUOTE B))" "(2 A 2 B 18 4 21)" // (LDC A LDC B DIV AP STOP)
testCompiler "(REM (QUOTE A) (QUOTE B))" "(2 A 2 B 19 4 21)" // (LDC A LDC B REM AP STOP)
testCompiler "(EQ (QUOTE A) (QUOTE B))" "(2 A 2 B 14 4 21)" // (LDC A LDC B EQ AP STOP)
testCompiler "(LEQ (QUOTE A) (QUOTE B))" "(2 A 2 B 20 4 21)" // (LDC A LDC B LEQ AP STOP)
testCompiler "(LAMBDA (X) (QUOTE A))" "(3 (2 A 5) 4 21)" // (LDF (LDC A RTN) AP STOP)
testCompiler "(LAMBDA (X) X)" "(3 (1 (0.0) 5) 4 21)" // (LDF (LD (0.0) RTN) AP STOP)
testCompiler "(LAMBDA (X Y) Y)" "(3 (1 (0.1) 5) 4 21)" // (LDF (LD (0.1) RTN) AP STOP)
testCompiler "((LAMBDA (X) X) (QUOTE A))" "(2 NIL 2 A 13 3 (1 (0.0) 5) 4 4 21)" // (LDC NIL LDC A CONS LDF (LD (0.0) RTN) AP AP STOP)
testCompiler "(LET X (X QUOTE A))" "(2 NIL 2 A 13 3 (1 (0.0) 5) 4 4 21)" // (LDC NIL LDC A CONS LDF (LD (0.0) RTN) AP AP STOP)
testCompiler "(LETREC X (X QUOTE A))" "(6 2 NIL 2 A 13 3 (1 (0.0) 5) 7 4 21)" // (DUM LDC NIL LDC A CONS LDF (LD (0.0) RTN) RAP AP STOP)
testCompiler "(IF (QUOTE A) (QUOTE B) (QUOTE C))" "(2 A 8 (2 B 9) (2 C 9) 4 21)" // (LDC A SEL (LDC B JOIN) (LDC C JOIN) AP STOP)

// ultimate test, compile the compiler - metecircularity baby!
testCompiler compilerSource compilerCode

// REPL

let rec repl output = 
    printf "%s\n> " output 
    try exec (Console.ReadLine() |> compile) (tokenize "((42))" |> parse) |> print |> repl 
    with ex -> repl ex.Message

repl "Welcome to Lispkit Lisp\n\nExample: (LETREC TEST (TEST LAMBDA (X) (CONS (QUOTE HELLO) (QUOTE WORLD))))\n"