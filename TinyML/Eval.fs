(*
* TinyML
* Eval.fs: evaluator
*)

module TinyML.Eval

open Ast

let get_cleaned_env (env : value env) id e =
    let rec get_used_variables e  =
        match e with
        | Lit _ -> Set.empty
        | Var id -> Set.singleton id
        | App (e1, e2) -> Set.union (get_used_variables e1) (get_used_variables e2)
        | Lambda (x, _, e) -> Set.difference (get_used_variables e) (Set.singleton x)
        | Let (x, _, e1, e2) ->
            Set.union
                (get_used_variables e1)
                (Set.difference (get_used_variables e2) (Set.singleton x))
        | LetRec (x, _, e1, e2) ->
            Set.union
                (Set.difference (get_used_variables e1) (Set.singleton x))
                (Set.difference (get_used_variables e2) (Set.singleton x))
        | IfThenElse (e1, e2, e3o) ->
            Set.union
                (Set.union (get_used_variables e1) (get_used_variables e2))
                (match e3o with
                | None -> Set.empty
                | Some e3 -> get_used_variables e3)
        | Tuple es -> es |> List.fold (
                                fun acc el ->
                                    Set.union (get_used_variables el) acc
                            ) Set.empty
        | BinOp (e1, _, e2) -> Set.union (get_used_variables e1) (get_used_variables e2)
        | UnOp (_, e) -> get_used_variables e
        | _ -> unexpected_error "get_cleaned_env: unsupported expression: %s [AST: %A]" (pretty_expr e) e

    let usedVariables = Set.difference (get_used_variables e) (Set.singleton id)
    usedVariables
          |> Seq.map (
            fun el -> List.find (fun (id, _) -> id = el) env
            )
          |> Seq.toList

let rec eval_expr (env : value env) (e : expr) : value =
    match e with
    | Lit lit -> VLit lit

    | Lambda (x, _, e) ->
        Closure (get_cleaned_env env x e, x, e)
    
    | App (e1, e2) ->
        let v1 = eval_expr env e1
        let v2 = eval_expr env e2
        match v1 with
        | Closure (env1, x, e) -> eval_expr ((x, v2) :: env1) e
        | RecClosure (env1, f, x, e) -> eval_expr ((x, v2) :: (f, v1) :: env1) e
        | _ -> unexpected_error "eval_expr: non-closure in left side of application: %s" (pretty_value v1)
        
    | Var x ->
        try
            let _, v = List.find (fun (y, _) -> x = y) env
            v
        with e ->
            unexpected_error $"eval_expr: unbounded variable {x}"
        
    | Let (x, _, e1, e2) ->
        let v1 = eval_expr env e1
        eval_expr ((x, v1) :: env) e2

    | LetRec (f, _, e1, e2) ->
        let v1 = eval_expr ((f, VLit LUnit) :: env) e1
        let v1 = match v1 with
                    | Closure (venv1, x, e) ->
                        RecClosure (
                            venv1 |> List.filter (fun (id, _) -> id <> f),
                            f,
                            x,
                            e
                        )
                    | _ -> unexpected_error "eval_expr: expected closure in rec binding but got: %s" (pretty_value v1)
        eval_expr ((f, v1) :: env) e2

    | IfThenElse (e1, e2, None) ->
        let v1 = eval_expr env e1
        match v1 with
        | VLit (LBool true) -> eval_expr env e2
        | VLit (LBool false) -> VLit LUnit
        | _ -> unexpected_error "eval_expr: non-boolean in if guard: %s" (pretty_value v1)
        

    | IfThenElse (e1, e2, Some e3) ->
        let v1 = eval_expr env e1
        eval_expr env (
                       match v1 with
                       | VLit (LBool true) -> e2
                       | VLit (LBool false) -> e3
                       | _ -> unexpected_error "eval_expr: non-boolean in if guard: %s" (pretty_value v1)
                    )
        
    | Tuple es ->
        VTuple(es |> List.map (eval_expr env))

    | BinOp (e1, "+", e2) -> binop_number_number (+) (+) env e1 e2
    | BinOp (e1, "-", e2) -> binop_number_number (-) (-) env e1 e2
    | BinOp (e1, "*", e2) -> binop_number_number (*) (*) env e1 e2
    | BinOp (e1, "/", e2) -> binop_number_number (/) (/) env e1 e2
    | BinOp (e1, "%", e2) -> binop_number_number (%) (%) env e1 e2
    
    | BinOp (e1, "<", e2) -> binop_number_boolean (<) (<) env e1 e2
    | BinOp (e1, "<=", e2) -> binop_number_boolean (<=) (<=) env e1 e2
    | BinOp (e1, ">", e2) -> binop_number_boolean (>) (>) env e1 e2
    | BinOp (e1, ">=", e2) -> binop_number_boolean (>=) (>=) env e1 e2
    | BinOp (e1, "=", e2) -> binop_number_boolean (=) (=) env e1 e2
    | BinOp (e1, "<>", e2) -> binop_number_boolean (<>) (<>) env e1 e2
    
    | BinOp (e1, "and", e2) -> binop_boolean_boolean (&&) env e1 e2
    | BinOp (e1, "or", e2) -> binop_boolean_boolean (||) env e1 e2
    
    | UnOp("not", e) ->
        let v = eval_expr env e
        match v with
        | VLit(LBool b) -> VLit(LBool (not b))
        | _ -> unexpected_error "eval_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
        
    | UnOp("-", e) ->
        let v = eval_expr env e
        match v with
        | VLit(LInt v) -> VLit(LInt -v)
        | VLit(LFloat v) -> VLit(LFloat -v)
        | _ -> unexpected_error "eval_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
      
    | _ -> unexpected_error "eval_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e

and binop_number_number op_int op_float env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2
    match v1, v2 with
    | VLit (LInt x), VLit (LInt y) -> VLit (LInt (op_int x y))
    | VLit (LFloat x), VLit (LFloat y) -> VLit (LFloat (op_float x y))
    | VLit (LInt x), VLit (LFloat y) -> VLit (LFloat (op_float (float x) y))
    | VLit (LFloat x), VLit (LInt y) -> VLit (LFloat (op_float x (float y)))
    | _ -> unexpected_error "eval_expr: illegal operands in binary operator (%s): %s, %s" (nameof op_int) (pretty_value v1) (pretty_value v2)

and binop_number_boolean op_int op_float env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2
    
    match v1, v2 with
    | VLit (LInt x), VLit (LInt y) -> VLit (LBool (op_int x y))
    | VLit (LFloat x), VLit (LFloat y) -> VLit (LBool (op_float x y))
    | VLit (LInt x), VLit (LFloat y) -> VLit (LBool (op_float (float x) y))
    | VLit (LFloat x), VLit (LInt y) -> VLit (LBool (op_float x (float y)))
    | _ -> unexpected_error "eval_expr: illegal operands in binary operator (%s): %s, %s" (nameof op_int) (pretty_value v1) (pretty_value v2)

and binop_boolean_boolean op env e1 e2 =
    let v1 = eval_expr env e1
    let v2 = eval_expr env e2
    
    match v1, v2 with
    | VLit (LBool x), VLit (LBool y) -> VLit (LBool (op x y))
    | _ -> unexpected_error "eval_expr: illegal operands in binary operator (%s): %s, %s" (nameof op) (pretty_value v1) (pretty_value v2)
