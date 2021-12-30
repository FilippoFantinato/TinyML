module TinyML.TypingTests

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

