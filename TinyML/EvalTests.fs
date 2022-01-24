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

let [<Fact>] ``Unary operator not with valid value`` () =
    let notExpr = UnOp("not", Lit(LBool true))
    let venv = []
    let actual = eval_expr venv notExpr
                    
    let expected = VLit (LBool false)
    
    Assert.Equal(expected, actual)

let [<Fact>] ``Unary operator minus with valid value`` () =
    let minusExpr = UnOp("-", Lit(LInt 5))
    let venv = []
    let actual = eval_expr venv minusExpr
                    
    let expected = VLit (LInt -5)
    
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
