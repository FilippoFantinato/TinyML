module TinyML.EvalTests

open TinyML.Ast
open TinyML.Eval
open Xunit

let [<Fact>] ``If then else guard true`` () =
    let ifExpr = IfThenElse(Lit(LBool true), Lit(LInt 5), Some(Lit(LInt 6)))
    let venv = []
    let actual = eval_expr venv ifExpr
    let expected = VLit (LInt 5)
    
    Assert.Equal(expected, actual)

let [<Fact>] ``Tuple with complex ops`` () =
    let tupleExpr = Tuple([
        Lit(LInt 5);
        UnOp("-", Lit(LInt 8));
        App(Lambda("x", None, BinOp(Var("x"), "+", Lit(LInt 1))), Lit(LInt 5))
    ])
    let venv = []
    let actual = eval_expr venv tupleExpr
                            
    let expected = VTuple [VLit (LInt 5); VLit (LInt -8); VLit (LInt 6)]
    
    Assert.Equal(expected, actual)

// Operators


let [<Fact>] ``Not operator with valid value`` () =
    let notExpr = UnOp("not", Lit(LBool true))
    let venv = []
    let actual = eval_expr venv notExpr
                    
    let expected = VLit (LBool false)
    
    Assert.Equal(expected, actual)
    
let [<Fact>] ``Not operator with a non valid value`` () =
    let notExpr = UnOp("not", Lit(LString "true"))
    let venv = []
    
    Assert.Throws<UnexpectedError>(
        fun () -> 
            eval_expr venv notExpr |> ignore
    )
                    
let [<Fact>] ``Minus operator with valid value`` () =
    let minusExpr = UnOp("-", Lit(LInt 5))
    let venv = []
    let actual = eval_expr venv minusExpr
                    
    let expected = VLit (LInt -5)
    
    Assert.Equal(expected, actual)
    
let [<Fact>] ``Minus operator with a non valid value`` () =
    let notExpr = UnOp("-", Lit(LString "-5"))
    let venv = []
    
    Assert.Throws<UnexpectedError>(
        fun () -> 
            eval_expr venv notExpr |> ignore
    )

// number op number -> number 
let [<Fact>] ``+ between int and int`` () =
    let expr = BinOp (Lit (LInt 4), "+", Lit (LInt 4))
    let venv = []

    let actual = eval_expr venv expr
    
    let expected = VLit (LInt 8)
    Assert.Equal(expected, actual)
    
let [<Fact>] ``+ between int and float`` () =
    let expr = BinOp (Lit (LInt 4), "+", Lit (LFloat 4))
    let venv = []

    let actual = eval_expr venv expr
    
    let expected = VLit (LFloat 8)
    Assert.Equal(expected, actual)
    
let [<Fact>] ``+ between float and int`` () =
    let expr = BinOp (Lit (LFloat 4), "+", Lit (LInt 4))
    let venv = []

    let actual = eval_expr venv expr
    
    let expected = VLit (LFloat 8)
    Assert.Equal(expected, actual)
    
let [<Fact>] ``+ between float and float`` () =
    let expr = BinOp (Lit (LFloat 4), "+", Lit (LFloat 4))
    let venv = []

    let actual = eval_expr venv expr
    
    let expected = VLit (LFloat 8)
    Assert.Equal(expected, actual)
    
let [<Fact>] ``+ between not valid lits`` () =
    let expr = BinOp (Lit (LFloat 4), "+", Lit (LString "4"))
    let venv = []

    Assert.Throws<UnexpectedError>(
        fun () ->
            eval_expr venv expr |> ignore
    )

let [<Fact>] ``- between int and int`` () =
    let expr = BinOp (Lit (LInt 4), "-", Lit (LInt 4))
    let venv = []

    let actual = eval_expr venv expr
    
    let expected = VLit (LInt 0)
    Assert.Equal(expected, actual)
    
let [<Fact>] ``* between int and int`` () =
    let expr = BinOp (Lit (LInt 4), "*", Lit (LInt 4))
    let venv = []

    let actual = eval_expr venv expr
 
    let expected = VLit (LInt 16)
    Assert.Equal(expected, actual)
    
let [<Fact>] ``/ between int and int`` () =
    let expr = BinOp (Lit (LInt 4), "/", Lit (LInt 4))
    let venv = []

    let actual = eval_expr venv expr
 
    let expected = VLit (LInt 1)
    Assert.Equal(expected, actual)
    
let [<Fact>] ``% between int and int`` () =
    let expr = BinOp (Lit (LInt 4), "%", Lit (LInt 3))
    let venv = []

    let actual = eval_expr venv expr
 
    let expected = VLit (LInt 1)
    Assert.Equal(expected, actual)
    
 // number op number -> boolean 
    
let [<Fact>] ``< between int and int`` () =
    let expr = BinOp (Lit (LInt 4), "<", Lit (LInt 4))
    let venv = []

    let actual = eval_expr venv expr
 
    let expected = VLit (LBool false)
    Assert.Equal(expected, actual)
    
let [<Fact>] ``< between int and float`` () =
    let expr = BinOp (Lit (LInt 4), "<=", Lit (LFloat 4.0))
    let venv = []

    let actual = eval_expr venv expr
 
    let expected = VLit (LBool true)
    Assert.Equal(expected, actual)

let [<Fact>] ``< between float and int`` () =
    let expr = BinOp (Lit (LFloat 4.0), "<=", Lit (LInt 4))
    let venv = []

    let actual = eval_expr venv expr
 
    let expected = VLit (LBool true)
    Assert.Equal(expected, actual)
    
let [<Fact>] ``< between float and float`` () =
    let expr = BinOp (Lit (LFloat 4.0), "<=", Lit (LFloat 4.0))
    let venv = []

    let actual = eval_expr venv expr
 
    let expected = VLit (LBool true)
    Assert.Equal(expected, actual)
    
let [<Fact>] ``< between non valid lits`` () =
    let expr = BinOp (Lit (LFloat 4.0), "<=", Lit (LString "4.0"))
    let venv = []

    Assert.Throws<UnexpectedError>(
        fun () ->
            eval_expr venv expr |> ignore
    )
 
let [<Fact>] ``<= between int and int`` () =
    let expr = BinOp (Lit (LInt 4), "<=", Lit (LInt 4))
    let venv = []

    let actual = eval_expr venv expr
 
    let expected = VLit (LBool true)
    Assert.Equal(expected, actual)
    
let [<Fact>] ``> between int and int`` () =
    let expr = BinOp (Lit (LInt 4), ">", Lit (LInt 4))
    let venv = []

    let actual = eval_expr venv expr
 
    let expected = VLit (LBool false)
    Assert.Equal(expected, actual)

let [<Fact>] ``>= between int and int`` () =
    let expr = BinOp (Lit (LInt 4), ">=", Lit (LInt 4))
    let venv = []

    let actual = eval_expr venv expr
 
    let expected = VLit (LBool true)
    Assert.Equal(expected, actual)

let [<Fact>] ``= between int and int`` () =
    let expr = BinOp (Lit (LInt 4), "=", Lit (LInt 4))
    let venv = []

    let actual = eval_expr venv expr
 
    let expected = VLit (LBool true)
    Assert.Equal(expected, actual)

let [<Fact>] ``<> between int and int`` () =
    let expr = BinOp (Lit (LInt 4), "<>", Lit (LInt 4))
    let venv = []

    let actual = eval_expr venv expr
 
    let expected = VLit (LBool false)
    Assert.Equal(expected, actual)
    
// boolean op boolean -> boolean 
    
let [<Fact>] ``And between boolean and boolean`` () =
    let expr = BinOp (Lit (LBool true), "and", Lit (LBool false))
    let venv = []

    let actual = eval_expr venv expr
 
    let expected = VLit (LBool false)
    Assert.Equal(expected, actual)
    
let [<Fact>] ``And between non valid lits`` () =
    let expr = BinOp (Lit (LBool true), "and", Lit (LString "false"))
    let venv = []

    Assert.Throws<UnexpectedError>(
        fun () ->
            eval_expr venv expr |> ignore
    )
    
let [<Fact>] ``Or between boolean and boolean`` () =
    let expr = BinOp (Lit (LBool true), "or", Lit (LBool false))
    let venv = []

    let actual = eval_expr venv expr
 
    let expected = VLit (LBool true)
    Assert.Equal(expected, actual)
