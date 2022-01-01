module TinyML.TypingTests

open System
open TinyML.Typing
open TinyML.Ast
open Xunit

let [<Fact>] ``Apply substitutions to an arrow type with free vars`` () =
    let s = [
        (1, TyArrow (TyVar 3, TyVar 4))
        (2, TyVar 5)
        (5, TyArrow (TyVar 3, TyVar 4))
    ]

    let ty = TyArrow (TyVar 1, TyVar 2)
    let actual = apply_subst ty s
    
    let expected = TyArrow (TyArrow (TyVar 3, TyVar 4), TyArrow (TyVar 3, TyVar 4))
        
    Assert.Equal(expected, actual)    
    
let [<Fact>] ``Apply substitutions to an arrow type without free vars`` () =
    let s = [
        (1, TyArrow (TyVar 3, TyVar 4))
        (2, TyVar 5)
        (5, TyArrow (TyVar 3, TyVar 4))
        (3, TyInt)
        (4, TyBool)
    ]
    
    let ty = TyArrow (TyVar 1, TyVar 2)
    let actual = apply_subst ty s
    
    let expected = TyArrow (TyArrow (TyInt, TyBool), TyArrow (TyInt, TyBool))
        
    Assert.Equal(expected, actual)    

let [<Fact>] ``Composition between two substitutions`` () =
    let s1: subst = [
        (1, TyVar 2)
        (2, TyVar 7)
    ]
    let s2: subst = [
        (3, TyVar 1)
        (4, TyVar 5)
        (6, TyVar 6)
    ]
    let actual = compose_subst s1 s2
    
    let expected: subst = [
        (3, TyVar 7)
        (4, TyVar 5)
    ]
    
    Assert.Equal<subst>(expected, actual)
    
let [<Fact>] ``Application with valid expressions`` () =
    let param = "x"
    let app = App (Lambda (param, Some TyInt, BinOp (Var param, "+", Lit (LInt 1))), Lit (LInt 3))
    let env = []
    
    let actualType, actualSubstitutions = typeinfer_expr env app
    
    let expectedType, expectedSubstitutions = TyInt, [(0, TyInt)]
    
    Assert.Equal(expectedType, actualType)
    Assert.Equal<subst>(expectedSubstitutions, actualSubstitutions)
    
let [<Fact>] ``Application with invalid parameter should throw an exception`` () =
    let param = "x"
    let app = App (Lambda (param, Some TyInt, BinOp (Var param, "+", Lit (LInt 1))), Lit (LBool true))
    let env = []
 
    Assert.Throws<TypeError>(fun () -> typeinfer_expr env app |> ignore)
    
let [<Fact>] ``Application without a lambda should throw an exception`` () =
    let param = "x"
    let app = App (BinOp (Lit (LFloat 7.0), "+", Lit (LFloat 7.0)), Lit (LBool true))
    let env = []
 
    Assert.Throws<TypeError>(fun () -> typeinfer_expr env app |> ignore)
    
let [<Fact>] ``If then with valid exprs`` () =
    let ifThen = IfThenElse (
        BinOp (Lit (LInt 5), "<", Lit (LFloat 7.0)),
        Lit LUnit,
        None)
    let env = []
    
    let actualType, actualSubstitutions = typeinfer_expr env ifThen
    let expectedType = TyUnit
    
    Assert.Equal(expectedType, actualType)
    Assert.True(List.isEmpty actualSubstitutions)

let [<Fact>] ``If then else with valid exprs`` () =
    let varX = "x"
    let ifThenElse = IfThenElse (
        BinOp (Lit (LInt 5), "<", Lit (LFloat 7.0)),
        BinOp (Lit (LInt 5), "+", Lit (LFloat 7.0)),
        Some (BinOp (Var varX, "+", Lit (LFloat 7.0)))
        )
    let env = [("x", TyInt)]
    
    let actualType, actualSubstitutions = typeinfer_expr env ifThenElse
    let expectedType = TyFloat
    
    Assert.Equal(expectedType, actualType)
    Assert.True(List.isEmpty actualSubstitutions)
 
let [<Fact>] ``Binary operation with valid parameters of the same type`` () =
    let binop = BinOp (Lit(LInt 5), "+", Lit(LInt 7))
    let env = []
    
    let actualType, actualSubstitutions = typeinfer_expr env binop

    let expectedType = TyInt
    
    Assert.Equal(expectedType, actualType)
    Assert.True(List.isEmpty actualSubstitutions)
    
let [<Fact>] ``Binary operation with valid parameters with different types`` () =
    let binop = BinOp (Lit(LInt 5), "+", Lit(LFloat 7.0))
    let env = []
    
    let actualType, actualSubstitutions = typeinfer_expr env binop
    
    let expectedType = TyFloat
    
    Assert.Equal(expectedType, actualType)
    Assert.True(List.isEmpty actualSubstitutions)

let [<Fact>] ``Binary operation which return a bool with valid parameters of the same type`` () =
    let binop = BinOp (Lit(LInt 5), "<", Lit(LInt 5))
    let env = []
    
    let actualType, actualSubstitutions = typeinfer_expr env binop
    
    let expectedType = TyBool
    
    Assert.Equal(expectedType, actualType)
    Assert.True(List.isEmpty actualSubstitutions)


let [<Fact>] ``Binary operation which return a bool with valid parameters of different types`` () =
    let binop = BinOp (Lit(LInt 5), "<", Lit(LFloat 7.0))
    let env = []
    
    let actualType, actualSubstitutions = typeinfer_expr env binop
    
    let expectedType = TyBool
    
    Assert.Equal(expectedType, actualType)
    Assert.True(List.isEmpty actualSubstitutions)

let [<Fact>] ``Minus unary operation with int parameter`` () =
    let unop = UnOp ("-", Lit(LInt 5))
    let env = []
    
    let actualType, actualSubstitutions = typeinfer_expr env unop

    let expectedType = TyInt
    
    Assert.Equal(expectedType, actualType)
    Assert.True(List.isEmpty actualSubstitutions)
    
    
let [<Fact>] ``Minus unary operation with float parameter`` () =
    let unop = UnOp ("-", Lit(LFloat 5.0))
    let env = []
    
    let actualType, actualSubstitutions = typeinfer_expr env unop

    let expectedType = TyFloat
    
    Assert.Equal(expectedType, actualType)
    Assert.True(List.isEmpty actualSubstitutions)
    
let [<Fact>] ``Minus unary operation with invalid parameter`` () =
    let unop = UnOp ("-", Lit(LBool true))
    let env = []
    
    Assert.Throws<TypeError>(fun () -> typeinfer_expr env unop |> ignore)

let [<Fact>] ``Negation unary operation with bool parameter`` () =
    let unop = UnOp ("not", Lit (LBool true))
    let env = [] 
    
    let actualType, actualSubstitutions = typeinfer_expr env unop

    let expectedType = TyBool
    
    Assert.Equal(expectedType, actualType)
    Assert.True(List.isEmpty actualSubstitutions)
    
let [<Fact>] ``Negation unary operation with variable as parameter`` () =
    let x = "x"
    let xTyVar = 0
    let unop = UnOp ("not", Var x)
    let env = [(x, TyVar xTyVar)] 
    
    let actualType, actualSubstitutions = typeinfer_expr env unop

    let expectedType, expectedSubstitutions = TyBool, [(xTyVar, TyBool)]
    
    Assert.Equal(expectedType, actualType)
    Assert.Equal<subst>(expectedSubstitutions, actualSubstitutions)
        
let [<Fact>] ``Negation unary operation with invalid parameter`` () =
    let unop = UnOp ("not", Lit (LInt 5))
    let env = [] 
    
    Assert.Throws<TypeError>(fun () -> typeinfer_expr env unop |> ignore)
