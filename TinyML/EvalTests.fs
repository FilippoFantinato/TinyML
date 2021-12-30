module TinyML.EvalTests

open System.Reflection
open TinyML.Ast
open TinyML.Eval
open Xunit

let [<Fact>] ``If then else guard true`` () =
    let ifExpr = IfThenElse(Lit(LBool true), Lit(LInt 5), Some(Lit(LInt 6)))
    let venv = []
    let actualValue = eval_expr venv ifExpr
    let actual = match actualValue with
                    | VLit(LInt n) -> n
    let expected = 5
    
    Assert.Equal(expected, actual)

let [<Fact>] ``Unary operator not with valid value`` () =
    let notExpr = UnOp("not", Lit(LBool true))
    let venv = []
    let actualValue = eval_expr venv notExpr
    let actual = match actualValue with
                    | VLit(LBool n) -> n
                    
    let expected = false
    
    Assert.Equal(expected, actual)

let [<Fact>] ``Unary operator minus with valid value`` () =
    let minusExpr = UnOp("-", Lit(LInt 5))
    let venv = []
    let actualValue = eval_expr venv minusExpr
    let actual = match actualValue with
                    | VLit(LInt n) -> n
                    
    let expected = -5
    
    Assert.Equal(expected, actual)

let [<Fact>] ``Tuple with complex ops`` () =
    let tupleExpr = Tuple([
        Lit(LInt 5);
        UnOp("-", Lit(LInt 8));
        App(Lambda("x", None, BinOp(Var("x"), "+", Lit(LInt 1))), Lit(LInt 5))
    ])
    let venv = []
    let actualValue = eval_expr venv tupleExpr
    let actual = match actualValue with
                    | VTuple tuple ->
                        match tuple with
                        | (VLit(LInt v1)) :: (VLit(LInt v2)) :: [ VLit(LInt v3) ] ->
                            [v1; v2; v3]
                            
    let expected = [5; -8; 6]
    
    Assert.Equal<int list>(expected, actual)
