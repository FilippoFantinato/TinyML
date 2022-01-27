module TinyML.TinyMLTests

open System.IO
open FSharp.Common
open TinyML.Ast
open Xunit

let compute_prg_str prg =
    let parse_from_TextReader rd filename parser =
        Parsing.parse_from_TextReader SyntaxError rd filename (1, 1) parser Lexer.tokenize Parser.tokenTagToTokenId

    let rd = new StringReader(prg)
    parse_from_TextReader rd "LINE" Parser.program

let interpret_expr tenv venv e =
    TypeInference.reset_tyvar_index ()
    let t, _ = TypeInference.typeinfer_expr tenv e
    let v = Eval.eval_expr venv e
    t, v

let [<Fact>] ``Lambda returning a tuple (int, int)`` () =
    let prg = "fun x -> fun y -> ((if true then x else y), x + 1)"
    let prg = compute_prg_str prg
    
    let tenv, venv = [], []
    let actualType, actualValue = interpret_expr tenv venv prg
    
    let expectedType = TyArrow (TyInt, TyArrow (TyInt, TyTuple [TyInt; TyInt]))
    let expectedValue =
                    let x = "x"
                    let y = "y"
                    Closure([], x,
                          Lambda(y, None,
                                  Tuple [
                                      IfThenElse (Lit (LBool true), Var "x", Some (Var "y"))
                                      BinOp (Var "x", "+", Lit (LInt 1))
                                      ]))
    
    Assert.Equal(expectedType, actualType)
    Assert.Equal(expectedValue, actualValue)
    
let [<Fact>] ``Application of a typed function`` () =
    let prg = """
       let rec f (x: int) (y: int) : (int -> int -> float) =
            if x > 2
            then (-1+x)*(y+1.0)
            else (x+1.0)*(-1+y)

        in f 4 0
    """
    let prg = compute_prg_str prg
    
    let tenv, venv = [], []
    let actualType, actualValue = interpret_expr tenv venv prg

    let expectedType = TyFloat
    let expectedValue = VLit (LFloat 3)

    Assert.Equal(expectedType, actualType)
    Assert.Equal(expectedValue, actualValue)
    
let [<Fact>] ``Application of a high order full polymorphic function`` () =
    let prg = """
        let f x y = x y

        in (f (fun x -> x), f (fun x -> x) 1, f (fun x -> x) "ciao")
    """
    let prg = compute_prg_str prg
    
    let tenv, venv = [], []
    let actualType, actualValue = interpret_expr tenv venv prg
    
    let expectedType = TyTuple [
        TyArrow (TyVar 3, TyVar 3)
        TyInt
        TyString
    ]
    let expectedValue = VTuple [
        Closure([("x", Closure ([], "x", Var "x"))], "y", App (Var "x", Var "y"))
        VLit (LInt 1)
        VLit (LString "ciao")
    ]
    
    Assert.Equal(expectedType, actualType)
    Assert.Equal(expectedValue, actualValue)
    
    
let [<Fact>] ``High order function which receives a polymorphic function`` () =
    let prg = """
        let f = fun x -> 
                    fun y ->
                        if x > 0
                        then y x
                        else y (x + 1)
        
        in f 5 (fun x -> x)
    """
    let prg = compute_prg_str prg

    let tenv, venv = [], []
    let actualType, actualValue = interpret_expr tenv venv prg
    
    let expectedType = TyInt
    let expectedValue = VLit (LInt 5)
    
    Assert.Equal(expectedType, actualType)
    Assert.Equal(expectedValue, actualValue)


let [<Fact>] ``Application of a lambda returning a closure where the argument is shadowed more times`` () =
    let prg = """
        let g = fun x -> ( x + 1, let x = "ciao" in x , fun x -> x ) in g 5
    """
    let prg = compute_prg_str prg
    
    let tenv, venv = [], []
    let actualType, actualValue = interpret_expr tenv venv prg
    
    let alpha = TyVar 2
    let expectedType = TyTuple [TyInt; TyString; TyArrow (alpha, alpha)]
    let expectedValue = VTuple [VLit (LInt 6); VLit (LString "ciao"); Closure([], "x", Var "x")]
    
    Assert.Equal(expectedType, actualType)
    Assert.Equal(expectedValue, actualValue)
    
    
let [<Fact>] ``Polymorphic high order function applied more times on a tuple 1`` () =
    let prg = """
       let f = fun x ->
                    fun y ->
                        if x > 0
                        then y x
                        else y (x+1)
                        
       in (f, f -3 (fun x -> x), f -5 (fun x -> x+1.0), f) 
    """
    let prg = compute_prg_str prg
    
    let tenv, venv = [], []
    let actualType, actualValue = interpret_expr tenv venv prg

    let alpha = TyVar 14
    let beta = TyVar 5
    let expectedType = TyTuple [
        TyArrow (TyInt, TyArrow (TyArrow (TyInt, alpha), alpha))
        TyInt
        TyFloat
        TyArrow (TyInt, TyArrow (TyArrow (TyInt, beta), beta))
    ]
    
    let fValue =
             Closure ([], "x",
                 Lambda ("y", None,
                         IfThenElse (
                             BinOp (Var "x", ">", Lit (LInt 0)),
                             App (Var "y", Var "x"),
                             Some (App (Var "y", BinOp (Var "x", "+", Lit (LInt 1)))))))
    
    let expectedValue = VTuple [
        fValue
        VLit (LInt -2)
        VLit (LFloat -3.0)
        fValue
    ]
    
    Assert.Equal(expectedType, actualType)
    Assert.Equal(expectedValue, actualValue)

let [<Fact>] ``Recursive polymorphic function applied multiple on a tuple 2`` () =
    let prg = """
        let z = 2 in
        let rec f x y = 
            x (y+1.0)
        in (
            f (fun x -> x) 5,
            f,
            f (fun (x: float) -> if (-1.0+x) > 0 then x/z else x*z) -5,
            f (fun (x: float) -> if x > 1.0 then ()) -5,
            f (fun x -> "ciao"),
            f
        )
    """
    let prg = compute_prg_str prg
    
    let tenv, venv = [], []
    let actualType, actualValue = interpret_expr tenv venv prg
    
    let expectedType = TyTuple [
        TyFloat
        TyArrow (TyArrow (TyFloat, TyVar 15), TyArrow (TyInt, TyVar 15))
        TyFloat
        TyUnit
        TyArrow (TyInt, TyString)
        TyArrow (TyArrow (TyFloat, TyVar 5), TyArrow (TyInt, TyVar 5))
    ]
    let expectedValue = VTuple [
        VLit (LFloat 6.0)
        RecClosure ([], "f", "x", Lambda ("y", None, App (Var "x", BinOp (Var "y", "+", Lit (LFloat 1.0)))))
        VLit (LFloat -8.0)
        VLit LUnit
        Closure (
                 [("x", Closure ([], "x", Lit (LString "ciao")))],
                 "y",
                 App (Var "x", BinOp (Var "y", "+", Lit (LFloat 1.0)))
                 )
        RecClosure ([], "f", "x", Lambda ("y", None, App (Var "x", BinOp (Var "y", "+", Lit (LFloat 1.0)))))
    ]
    
    Assert.Equal(expectedType, actualType)
    Assert.Equal(expectedValue, actualValue)

let [<Fact>] ``Recursive function with a lot of bindings `` () =
    let prg = """
        let z = true in
        let r = 7 in
        let x = 7 in
        let c = 8 in
        let f x y = 
                let a = 4 in 
                if y
                then let z = r + 5 in r
                else x  
        in 
        let g x = x + c in
        let g x = x + r in
        let c = 4 in
        let rec f x y = if x > 0 then f (-1+x) (c+1) else y
        in f
    """
    let prg = compute_prg_str prg
    
    let tenv, venv = [], []
    let actualType, actualValue = interpret_expr tenv venv prg

    let expectedType = TyArrow (TyInt, TyArrow (TyInt, TyInt))
    let expectedValue = RecClosure (
        [("c", VLit (LInt 4))],
        "f",
        "x",
        Lambda ("y", None,
                IfThenElse (
                    BinOp (Var "x", ">", Lit (LInt 0)),
                    App (App (Var "f", BinOp (Lit (LInt -1), "+", Var "x")), BinOp (Var "c", "+", Lit (LInt 1))),
                    Some (Var "y")
                )
        )
    )

    Assert.Equal(expectedType, actualType)
    Assert.Equal(expectedValue, actualValue)

let [<Fact>] ``Recursive polymorphic function applied multiple times on let bindings`` () =
    let prg = """
        let z = 2 in
        let rec f x y = 
            x (y+1.0)
        in let g = f (fun x -> x) 5
        in let w = f
        in let z = f (fun (x: float) -> x/z)
        in let s = f (fun x -> "ciao")
        in let a = f
        in (g, w, z, s, a)
    """
    let prg = compute_prg_str prg
    
    let tenv, venv = [], []
    let actualType, actualValue = interpret_expr tenv venv prg

    let expectedType = TyTuple [
        TyFloat
        TyArrow (TyArrow (TyFloat, TyVar 17), TyArrow (TyInt, TyVar 17))
        TyArrow (TyInt, TyFloat)
        TyArrow (TyInt, TyString)
        TyArrow (TyArrow (TyFloat, TyVar 16), TyArrow (TyInt, TyVar 16))
    ]
    let expectedValue = VTuple [
        VLit (LFloat 6.0)
        RecClosure ([], "f", "x", Lambda ("y", None, App (Var "x", BinOp (Var "y", "+", Lit (LFloat 1.0)))))
        Closure (
                 [("x", Closure ([("z", VLit (LInt 2))], "x", BinOp (Var "x", "/", Var "z")))],
                 "y",
                 App (Var "x", BinOp (Var "y", "+", Lit (LFloat 1.0)))
                 )
        Closure (
                 [("x", Closure ([], "x", Lit (LString "ciao")))],
                 "y",
                 App (Var "x", BinOp (Var "y", "+", Lit (LFloat 1.0)))
                 )
        RecClosure ([], "f", "x", Lambda ("y", None, App (Var "x", BinOp (Var "y", "+", Lit (LFloat 1.0)))))
    ]
    
    Assert.Equal(expectedType, actualType)
    Assert.Equal(expectedValue, actualValue)
    

let [<Fact>] ``Recursive function which count how many rec steps it computes before to reach 0 from x`` () =
    let prg = """
        let rec f x y = if x > 0 then f (-1+x) (y+1) else y
        in f 4 0
    """
    let prg = compute_prg_str prg
    
    let tenv, venv = [], []
    let actualType, actualValue = interpret_expr tenv venv prg
    
    let expectedType = TyInt
    let expectedValue = VLit (LInt 4)
    
    Assert.Equal(expectedType, actualType)
    Assert.Equal(expectedValue, actualValue)

let [<Fact>] ``Fibonacci function of 8`` () =
    let prg = """
        let rec fib x =
                if x = 0 then 0
                else if x = 1 then 1
                else (fib (-1+x)) + (fib (-2+x))
        in fib 8
    """
    let prg = compute_prg_str prg
    
    let tenv, venv = [], []
    let actualType, actualValue = interpret_expr tenv venv prg
    
    let expectedType = TyInt
    let expectedValue = VLit (LInt 21)
    
    Assert.Equal(expectedType, actualType)
    Assert.Equal(expectedValue, actualValue)
