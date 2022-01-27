module TinyML.TypeInferenceTests

open TinyML.TypeInference
open TinyML.Ast
open Xunit

let [<Fact>] ``Apply substitutions to an arrow type with free vars`` () =
    let s = [
        (1, TyArrow (TyVar 4, TyVar 4))
        (2, TyVar 5)
        (5, TyArrow (TyVar 3, TyVar 4))
    ]

    let ty = TyArrow (TyVar 1, TyVar 2)
    let actual = apply_subst ty s
    
    let expected = TyArrow (TyArrow (TyVar 4, TyVar 4), TyArrow (TyVar 3, TyVar 4))
        
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

// Let
    
let [<Fact>] ``Let typed with valid expressions`` () =
    let x = "x"
    let expr = LetIn ((false, x, Some TyString, Lit (LString "c")), Var x)
    let env = []
    
    let actualType, actualSubstitutions = typeinfer_expr env expr
    
    let expectedType = TyString
    
    Assert.Equal(expectedType, actualType)
    Assert.True(List.isEmpty actualSubstitutions)

let [<Fact>] ``Let untyped with valid expressions`` () =
    let expr = LetIn ((false, "x", None, Lambda ("y", None, Var "y")), App (Var "x", Lit (LInt 5)))
    let env = []
    
    let actualType, _ = typeinfer_expr env expr
    
    let expectedType = TyInt
    
    Assert.Equal(expectedType, actualType)
    
let [<Fact>] ``Let untyped evaluating f int->'a->'a`` () =
    let expr = LetIn((false, "f", None, Lambda ("x", None, App (Var "x", Lit (LInt 5)))), Var "f")
    let env = []
    
    reset_tyvar_index ()

    let actualType, _ = typeinfer_expr env expr

    let alpha = TyVar 3
    let expectedType = TyArrow(TyArrow (TyInt, alpha), alpha)
    
    Assert.Equal(expectedType, actualType)
    
let [<Fact>] ``Let untyped evaluating f (int->int)->int`` () =
    let expr = LetIn((false, "f", None,
                      Lambda ("x", None, BinOp (App (Var "x", Lit (LInt 5)), "+", App (Var "x", Lit (LInt 5))))),
                      Var "f")
    let env = []

    let actualType, _ = typeinfer_expr env expr
    
    let expectedType = TyArrow (TyArrow (TyInt, TyInt), TyInt)
    
    Assert.Equal(expectedType, actualType)

let [<Fact>] ``Let untyped evaluating f where the argument is used in a wrong way`` () =
    let expr = LetIn((false, "f", None,
                      Lambda ("x", None, BinOp (App (Var "x", Lit (LInt 5)), "+", App (Var "x", Lit (LBool true))))),
                      Var "f")
    let env = []

    Assert.Throws<TypeError>(fun () -> typeinfer_expr env expr |> ignore)
    
let [<Fact>] ``Let untyped using the same variable for two types`` () =
    let expr = Lambda ("x", None,
                       LetIn((false, "y", None, BinOp (Var "x", "+", Lit (LInt 5))),
                             LetIn((false, "z", None, UnOp ("not", Var "x")), Var "z")))
    
    let env = []
    
    Assert.Throws<TypeError>(fun () -> typeinfer_expr env expr |> ignore)

// Let rec
let [<Fact>] ``Let rec untyped evaluating f int->'a`` () =
    let expr = LetIn((true, "f", None, Lambda ("x", None, App (Var "f", Lit (LInt 5)))), Var "f")
    let env = []
    
    reset_tyvar_index ()

    let actualType, _ = typeinfer_expr env expr

    let expectedType = TyArrow(TyInt, TyVar 4)

    Assert.Equal(expectedType, actualType)


let [<Fact>] ``Let rec untyped evaluating f int -> int`` () =
    let expr = LetIn((true, "f", None, Lambda ("x", None, BinOp (App (Var "f", Var "x"), "+", Var "x"))), Var "f")
    let env = []
    
    let actualType, _ = typeinfer_expr env expr
    
    let expectedType = TyArrow (TyInt, TyInt)
    
    Assert.Equal(expectedType, actualType)
    
let [<Fact>] ``Let rec untyped applying a wrong argument to f`` () =
    let expr = LetIn((true, "f", None, Lambda ("x", None, BinOp (App (Var "f", Var "x"), "+", Var "x"))),
                     App (Var "f", Lit (LBool true)))
    let env = []

    Assert.Throws<TypeError>(fun () -> typeinfer_expr env expr |> ignore)

let [<Fact>] ``Let rec untyped evaluating an application`` () =
    let expr = LetIn((true, "f", None, Lambda ("x", None, App (Var "f", Lit (LInt 5)))), App (Var "f", Lit (LInt 5)))
    let env = []

    reset_tyvar_index ()

    let actualType, _ = typeinfer_expr env expr
    
    let expectedType = TyVar 3

    Assert.Equal(expectedType, actualType)

let [<Fact>] ``Let rec untyped evaluating a polymorphic function`` () =
    let expr = LetIn((true, "f", None, Lambda ("x", None, App (Var "f", Var "x"))),
                     LetIn ((false, "y", None, App (Var "f", Lit (LInt 5))), Var "f"))
    let env = []
    
    reset_tyvar_index ()
    
    let actualType, _ = typeinfer_expr env expr
    let expectedType = TyArrow (TyVar 7, TyVar 8)
    
    Assert.Equal(expectedType, actualType)

//let [<Fact>] ``Let rec untyped evaluating a function int->int`` () =
//    let expr = L

// Lambda
let [<Fact>] ``Lambda untyped with valid binop`` () =
    let lambda = Lambda("x", None, BinOp(Var "x", "+", BinOp(Lit (LInt 8), "-", UnOp("-", Var "x"))))
    let env = []

    let actualType, _ = typeinfer_expr env lambda
    let expectedType = TyArrow (TyInt, TyInt)
    
    Assert.Equal(expectedType, actualType)
    
let [<Fact>] ``Lambda typed with valid binop`` () =
    let lambda = Lambda("x", Some TyInt, BinOp(Var "x", "+", BinOp(Lit (LInt 8), "-", UnOp("-", Var "x"))))
    let env = []

    let actualType, actualSubstitutions = typeinfer_expr env lambda
    let expectedType = TyArrow (TyInt, TyInt)
    let expectedSubstitutions = []
    
    Assert.Equal(expectedType, actualType)
    Assert.Equal<subst>(expectedSubstitutions, actualSubstitutions)    

let [<Fact>] ``Lambda typed with non valid binop`` () =
    let lambda = Lambda("x", Some TyInt, BinOp(Var "x", "+", BinOp(Lit (LInt 8), "-", UnOp("not", Var "x"))))
    let env = []

    Assert.Throws<TypeError>(
        fun () ->
            typeinfer_expr env lambda |> ignore
    )

let [<Fact>] ``lambda untyped with non valid binop`` () =
    let lambda = Lambda("x", None, BinOp(Var "x", "+", BinOp(Lit (LInt 8), "-", UnOp("not", Var "x"))))
    let env = []
    
    Assert.Throws<TypeError>(
        fun () ->
            typeinfer_expr env lambda |> ignore
    )
    
let [<Fact>] ``Lambda polymorphic with any parameter poly`` () =
    let lambda = Lambda ("x", None, Lambda("y", None, Tuple [Var "y"; Var "x"]))
    let env = []
    
    reset_tyvar_index ()
    
    let actualType, _ = typeinfer_expr env lambda
    
    let alpha = TyVar 1
    let beta =  TyVar 2
    let expectedType = TyArrow(alpha, TyArrow(beta, TyTuple [beta; alpha]))
    
    Assert.Equal(expectedType, actualType)

let [<Fact>] ``Lambda polymorphic with application`` () =
    let lambda = Lambda ("x", None, Lambda("y", None, App (Var "x", Var "y")))
    let env = []
    
    reset_tyvar_index ()
    
    let actualType, _ = typeinfer_expr env lambda

    let alpha = TyVar 2
    let beta =  TyVar 3
    let expectedType = TyArrow(TyArrow (alpha, beta), TyArrow(alpha, beta))
    
    Assert.Equal(expectedType, actualType)

// Application

let [<Fact>] ``Application with valid expressions`` () =
    let param = "x"
    let app = App (Lambda (param, Some TyInt, BinOp (Var param, "+", Lit (LInt 1))), Lit (LInt 3))
    let env = []
    
    let actualType, _ = typeinfer_expr env app
    
    let expectedType = TyInt
    
    Assert.Equal(expectedType, actualType)
    
let [<Fact>] ``Application with invalid parameter should throw an exception`` () =
    let param = "x"
    let app = App (Lambda (param, Some TyInt, BinOp (Var param, "+", Lit (LInt 1))), Lit (LBool true))
    let env = []
 
    Assert.Throws<TypeError>(
        fun () ->
            typeinfer_expr env app |> ignore
    )
    
let [<Fact>] ``Application without a lambda should throw an exception`` () =
    let app = App (BinOp (Lit (LFloat 7.0), "+", Lit (LFloat 7.0)), Lit (LBool true))
    let env = []
 
    Assert.Throws<TypeError>(fun () -> typeinfer_expr env app |> ignore)
    
// If then else    

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
    let env = [("x", ForAll ([], TyInt))]
    
    let actualType, actualSubstitutions = typeinfer_expr env ifThenElse
    let expectedType = TyFloat
    
    Assert.Equal(expectedType, actualType)
    Assert.True(List.isEmpty actualSubstitutions)
 
 // Binary operations between numbers
 
let [<Fact>] ``Number binary operation between int and int`` () =
    let binop = BinOp (Lit(LInt 5), "+", Lit(LInt 7))
    let env = []
    
    let actualType, actualSubstitutions = typeinfer_expr env binop

    let expectedType = TyInt
    
    Assert.Equal(expectedType, actualType)
    Assert.True(List.isEmpty actualSubstitutions)
    
let [<Fact>] ``Number binary operation between int and float`` () =
    let binop = BinOp (Lit(LInt 5), "+", Lit(LFloat 7.0))
    let env = []
    
    let actualType, actualSubstitutions = typeinfer_expr env binop
    
    let expectedType = TyFloat
    
    Assert.Equal(expectedType, actualType)
    Assert.True(List.isEmpty actualSubstitutions)
    
let [<Fact>] ``Number binary operation between float and int`` () =
    let binop = BinOp (Lit(LFloat 7.0), "+", Lit(LInt 7))
    let env = []
    
    let actualType, actualSubstitutions = typeinfer_expr env binop
    
    let expectedType = TyFloat
    
    Assert.Equal(expectedType, actualType)
    Assert.True(List.isEmpty actualSubstitutions)
    
let [<Fact>] ``Number binary operation between float and float`` () =
    let binop = BinOp (Lit(LFloat 7.0), "+", Lit(LFloat 7.0))
    let env = []
    
    let actualType, actualSubstitutions = typeinfer_expr env binop
    
    let expectedType = TyFloat
    
    Assert.Equal(expectedType, actualType)
    Assert.True(List.isEmpty actualSubstitutions)
    
let [<Fact>] ``Number binary operation between int and a non valid type`` () =
    let binop = BinOp (Lit(LInt 5), "+", Lit(LString ""))
    let env = []
    
    Assert.Throws<TypeError>(fun () -> typeinfer_expr env binop |> ignore)
    
let [<Fact>] ``Number binary operation between float and a non valid type`` () =
    let binop = BinOp (Lit(LFloat 7.0), "+", Lit(LString ""))
    let env = []
    
    Assert.Throws<TypeError>(fun () -> typeinfer_expr env binop |> ignore)
    
let [<Fact>] ``Number binary operation between a non valid type and int`` () =
    let binop = BinOp (Lit(LString ""), "+", Lit(LInt 5))
    let env = []
    
    Assert.Throws<TypeError>(fun () -> typeinfer_expr env binop |> ignore)

let [<Fact>] ``Number binary operation between a non valid type and float`` () =
    let binop = BinOp (Lit(LString ""), "+", Lit(LFloat 5.0))
    let env = []
    
    Assert.Throws<TypeError>(fun () -> typeinfer_expr env binop |> ignore)

let [<Fact>] ``Boolean binary operation between int and int`` () =
    let binop = BinOp (Lit(LInt 5), "<", Lit(LInt 5))
    let env = []
    
    let actualType, actualSubstitutions = typeinfer_expr env binop
    
    let expectedType = TyBool
    
    Assert.Equal(expectedType, actualType)
    Assert.True(List.isEmpty actualSubstitutions)


let [<Fact>] ``Boolean binary operation between int and float`` () =
    let binop = BinOp (Lit(LInt 5), "<", Lit(LFloat 5.0))
    let env = []
    
    let actualType, actualSubstitutions = typeinfer_expr env binop
    
    let expectedType = TyBool
    
    Assert.Equal(expectedType, actualType)
    Assert.True(List.isEmpty actualSubstitutions)
    
let [<Fact>] ``Boolean binary operation between float and int`` () =
    let binop = BinOp (Lit(LFloat 5.0), "<", Lit(LInt 5))
    let env = []
    
    let actualType, actualSubstitutions = typeinfer_expr env binop
    
    let expectedType = TyBool
    
    Assert.Equal(expectedType, actualType)
    Assert.True(List.isEmpty actualSubstitutions)
    
let [<Fact>] ``Boolean binary operation between float and float`` () =
    let binop = BinOp (Lit(LFloat 5.0), "<", Lit(LFloat 5.0))
    let env = []
    
    let actualType, actualSubstitutions = typeinfer_expr env binop
    
    let expectedType = TyBool
    
    Assert.Equal(expectedType, actualType)
    Assert.True(List.isEmpty actualSubstitutions)
    
let [<Fact>] ``Boolean binary operation between int and a non valid type`` () =
    let binop = BinOp (Lit(LInt 5), "<", Lit(LString "5.0"))
    let env = []
    
    Assert.Throws<TypeError>(fun () -> typeinfer_expr env binop |> ignore)
    
let [<Fact>] ``Boolean binary operation between float and a non valid type`` () =
    let binop = BinOp (Lit(LFloat 5.0), "<", Lit(LString "5.0"))
    let env = []
    
    Assert.Throws<TypeError>(fun () -> typeinfer_expr env binop |> ignore)
    
let [<Fact>] ``Boolean binary operation between a non valid type and int`` () =
    let binop = BinOp (Lit(LString "5.0"), "<", Lit(LInt 5))
    let env = []
    
    Assert.Throws<TypeError>(fun () -> typeinfer_expr env binop |> ignore)    
    
let [<Fact>] ``Boolean binary operation between a non valid type and float`` () =
    let binop = BinOp (Lit(LString "5.0"), "<", Lit(LFloat 5.0))
    let env = []
    
    Assert.Throws<TypeError>(fun () -> typeinfer_expr env binop |> ignore)
 
// Binary operations between booleans
    
let [<Fact>] ``And operation with valid parameters`` () =
    let binop = BinOp (Lit(LBool true), "and", Lit(LBool false))
    let env = []
    
    let actualType, actualSubstitutions = typeinfer_expr env binop
    
    let expectedType = TyBool
    
    Assert.Equal(expectedType, actualType)
    Assert.True(List.isEmpty actualSubstitutions)
    
let [<Fact>] ``And operation with non valid parameters`` () =
    let binop = BinOp (Lit(LInt 5), "and", Lit(LBool false))
    let env = []
    
    Assert.Throws<TypeError>(
        fun () ->
            typeinfer_expr env binop |> ignore
    )
    
let [<Fact>] ``Or operation with valid parameters`` () =
    let binop = BinOp (Lit(LBool true), "or", Lit(LBool false))
    let env = []
    
    let actualType, actualSubstitutions = typeinfer_expr env binop
    
    let expectedType = TyBool
    
    Assert.Equal(expectedType, actualType)
    Assert.True(List.isEmpty actualSubstitutions)
    
    
let [<Fact>] ``Or operation with non valid parameters`` () =
    let binop = BinOp (Lit(LInt 5), "or", Lit(LBool false))
    let env = []
    
    Assert.Throws<TypeError>(
        fun () ->
            typeinfer_expr env binop |> ignore
    )
    
    
// Non existing binary operation
let [<Fact>] ``Non existing binop`` () =
    let binop = BinOp (Lit(LBool false), "df", Lit(LBool false))
    let env = [] 
    
    Assert.Throws<UnexpectedError>(fun () -> typeinfer_expr env binop |> ignore)

    

// Minus unary operator

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

// Negation unary operator

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
    let env = [(x, ForAll ([], TyVar xTyVar))]
    
    let actualType, actualSubstitutions = typeinfer_expr env unop

    let expectedType, expectedSubstitutions = TyBool, [(xTyVar, TyBool)]
    
    Assert.Equal(expectedType, actualType)
    Assert.Equal<subst>(expectedSubstitutions, actualSubstitutions)
        
let [<Fact>] ``Negation unary operation with invalid parameter`` () =
    let unop = UnOp ("not", Lit (LInt 5))
    let env = [] 
    
    Assert.Throws<TypeError>(fun () -> typeinfer_expr env unop |> ignore)

// Non existing unary operator

let [<Fact>] ``Non existing unop`` () =
    let unop = UnOp ("/", Lit (LInt 5))
    let env = [] 
    
    Assert.Throws<UnexpectedError>(fun () -> typeinfer_expr env unop |> ignore)

// Tuple
let [<Fact>] ``Tuple with multiple types`` () =
    let tuple = Tuple [
        LetIn((false, "x", None, Lambda ("x", None, BinOp (Var "x", "+", Lit (LInt 5)))), App (Var "x", Lit (LInt 4)))
        UnOp ("not", Lit (LBool true))
        LetIn ((false, "x", None, Lit (LInt 8)), Var "x")
    ]
    
    let env = []

    let actualType, _ = typeinfer_expr env tuple
        
    let expectedType = TyTuple [TyInt; TyBool; TyInt]
    
    Assert.Equal(expectedType, actualType)
    
let [<Fact>] ``Tuple returned by a lambda with valid exprs`` () =
    let expr = LetIn (
                      (false, "x", None, Lambda ("x", None, Tuple [BinOp (Var "x", "+", Lit (LInt 5)); Var "x"])),
                      Var "x"
                     )
    let env = []

    let actualType, _ = typeinfer_expr env expr
        
    let expectedType = TyArrow (TyInt, TyTuple [TyInt; TyInt])
    
    Assert.Equal(expectedType, actualType)

let [<Fact>] ``Tuple returned by a lambda with no valid exprs`` () =
    let expr = LetIn (
                      (false, "x", None, Lambda ("x", None, Tuple [BinOp (Var "x", "+", Lit (LInt 5)); UnOp ("not", Var "x")])),
                      Var "x"
                     )
    let env = []

    Assert.Throws<TypeError>(fun () -> typeinfer_expr env expr |> ignore)
