(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.TypeInference

open System.Collections.Generic
open Ast

type subst = (tyvar * ty) list

let rec apply_subst (t : ty) (s : subst) : ty =
    match t with
    | TyName _ -> t
    | TyVar tv ->
                 try
                     let _, t2 = s |>
                                    List.find (
                                     fun el ->
                                         let t1, _ = el
                                         t1 = tv
                                 )
                     apply_subst t2 s
                 with e -> t
    | TyArrow (t1, t2) -> TyArrow (apply_subst t1 s, apply_subst t2 s)
    | TyTuple ts -> TyTuple (List.map (fun t -> apply_subst t s) ts)

let apply_subst_scheme (ForAll(tvs, t)) s =
    let s = s |> List.filter (fun (tyvar, _) -> not (List.contains tyvar tvs))
    ForAll (tvs, apply_subst t s)

let apply_subst_env (env: scheme env) (s: subst) =
    env |> List.map (
        fun (x, sch) ->
            (x, apply_subst_scheme sch s)
   )

let compose_subst (s1 : subst) (s2 : subst) : subst =
    if List.isEmpty s1 then
        s2
    else
        if List.isEmpty s2 then
            s1
        else
            s2
            |> List.fold (
                      fun acc (tv, t) ->
                          let newType = apply_subst t s1
                          
                          match newType with
                          | TyVar newTypeV -> (newTypeV, apply_subst (TyVar tv) s1) :: acc
                          | _ -> (tv, newType) :: acc
                    ) []
            |> (@) (s1 |> List.filter (
                        fun (tvs1, _) ->
                            try
                                s2 |> List.find (fun (tvs2, _) -> tvs1 = tvs2) |> ignore
                                false
                            with
                            | :? KeyNotFoundException -> true
                        ))
            |> List.filter (fun (el1, el2) ->
                match el2 with
                | TyVar tv -> el1 <> tv
                | _ -> true
            )

let rec ty_belongs_to_ty t t2 =
    match t2 with
    | TyName _ -> false
    | TyVar t2 -> t2 = t
    | TyArrow (t1, t2) -> (ty_belongs_to_ty t t1) || (ty_belongs_to_ty t t2)
    | TyTuple tys -> List.fold (fun acc el -> acc || (ty_belongs_to_ty t el)) false tys

let rec unify (t1 : ty) (t2 : ty) : subst =
    match t1, t2 with
    | TyName t1, TyName t2 -> if t1 = t2 then [] else type_error $"unify: impossible to unify {t1} with {t2}"
    | TyVar t1, TyVar t2 -> if t1 <> t2 then [(t1, TyVar t2)] else []
    | TyVar t1, t2
    | t2, TyVar t1 -> if ty_belongs_to_ty t1 t2
                        then
                            type_error $"unify: impossible to unify {t1} with {t2}"
                        else
                            [(t1, t2)]
    | TyArrow(ty1, ty2), TyArrow(ty3, ty4) -> compose_subst (unify ty1 ty3) (unify ty2 ty4)
    | TyTuple ty1s, TyTuple ty2s -> ([], ty1s, ty2s) |||> List.fold2 (fun acc ty1 ty2 -> compose_subst (unify ty1 ty2) acc) 
    | _, _ -> type_error $"unify: impossible to unify {t1} with {t2}"

let rec freevars_ty (t : ty) : tyvar Set =
    match t with
    | TyName _ -> Set.empty
    | TyArrow (t1, t2) -> Set.union (freevars_ty t1) (freevars_ty t2)
    | TyVar tv -> Set.singleton tv
    | TyTuple ts -> List.fold (fun set t -> Set.union set (freevars_ty t)) Set.empty ts 


let freevars_scheme (ForAll (tvs, t)) =
    Set.difference (freevars_ty t) (Set.ofList tvs)


let rec freevars_environment env =
    match env with
    | [] -> Set.empty
    | (_, s) :: xs -> Set.union (freevars_scheme s) (freevars_environment xs)

let mutable private tyVarIndex = 0
let generate_fresh_tyvar () =
    tyVarIndex <- tyVarIndex + 1
    tyVarIndex

let reset_tyvar_index () =
    tyVarIndex <- 0

let generalization env t =
    ForAll (Set.toList (Set.difference (freevars_ty t) (freevars_environment env)), t)


let instantiation (ForAll (tvs, t)) =
    let s = tvs |> List.map (fun el -> (el, TyVar (generate_fresh_tyvar ())))
    
    (apply_subst t s, s)

// type inference
//

let rec unify_binops ops (e1t, e1s) (e2t, e2s) err =
    match ops with
    | [] -> match err with
                | Some err -> raise err
                | None _ -> type_error "unify_operations: there is nothing to with try to unify the operation"
    | (t1, t2, tr) :: ops ->
           try
               let s1 = compose_subst (unify t1 e1t) e1s
               let s2 = compose_subst (unify t2 e2t) e2s

               let s = compose_subst s1 s2

               (apply_subst tr s, compose_subst s1 s2)
           with err ->
               unify_binops ops (e1t, e1s) (e2t, e2s) (Some err)
               
let rec unify_unops ops (et, es) err =
    match ops with
    | [] -> match err with
                | Some err -> raise err
                | None _ -> type_error "unify_operations: there is nothing to with try to unify the operation"
    | (t, tr) :: ops ->
           try
               let s = compose_subst (unify t et) es

               (tr, s)
           with err ->
               unify_unops ops (et, es) (Some err)

let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    match e with
    | Lit (LInt _) -> (TyInt, [])
    | Lit (LFloat _) -> (TyFloat, [])
    | Lit (LString _) -> (TyString, [])
    | Lit (LChar _) -> (TyChar, [])
    | Lit (LBool _) -> (TyBool, [])
    | Lit LUnit -> (TyUnit, [])

    | Var x ->
        try
            let _, t = List.find (fun (y, _) -> x = y) env
            instantiation t
        with e ->
            type_error $"typeinfer_expr: unbounded variable {x}"

    | Let (x, None, e1, e2) ->
        let e1t, e1s = typeinfer_expr env e1

        let env = (((x, generalization env e1t) :: env), e1s) ||> apply_subst_env

        let e2t, e2s = typeinfer_expr env e2

        let s = compose_subst e2s e1s

        (e2t, s)

    | Let (x, Some t1, e1, e2) ->
        let e1t, e1s = typeinfer_expr env e1
        let e1s = compose_subst (unify e1t t1) e1s 

        let env = ((x, generalization env t1) :: env, e1s) ||> apply_subst_env
        
        let e2t, e2s = typeinfer_expr env e2
        
        let s = compose_subst e2s e1s

        (e2t, s)
 
    | LetRec (x, None, e1, e2) ->
        let xT = TyVar (generate_fresh_tyvar ())
        let e1t, e1s = typeinfer_expr ((x, ForAll ([], xT)) :: env) e1

        let e1tInferred = apply_subst xT e1s
        let e1s = compose_subst (unify e1tInferred e1t) e1s
        let e1t = apply_subst e1t e1s

        let env = ((x, generalization env e1t) :: env, e1s) ||> apply_subst_env
        
        let e2t, e2s = typeinfer_expr env e2

        let s = compose_subst e2s e1s

        (e2t, s)

    | LetRec (x, Some t, e1, e2) ->
        let e1t, e1s = typeinfer_expr ((x, ForAll ([], t)) :: env) e1
        let e1s = compose_subst (unify e1t t) e1s

        let env = (((x, generalization env t) :: env), e1s) ||> apply_subst_env
        
        let e2t, e2s = typeinfer_expr env e2
        
        let s = compose_subst e2s e1s
        
        (e2t, s)

    | Lambda(x, None, e) ->
        let parameterT = TyVar (generate_fresh_tyvar ())
        let bodyT, bodyS = typeinfer_expr ((x, ForAll ([], parameterT)) :: env) e

        (apply_subst (TyArrow (parameterT, bodyT)) bodyS, bodyS)
        
    | Lambda (x, Some t1, e) ->
        let env = (x, ForAll ([], t1)) :: env
        let bt, bs = typeinfer_expr env e

        (apply_subst (TyArrow (t1, bt)) bs, bs)

    | App (e1, e2) ->
        let e1t, e1s = typeinfer_expr env e1
        
        let env = apply_subst_env env e1s
        
        let e2t, e2s = typeinfer_expr env e2

        let bt = TyVar (generate_fresh_tyvar ())

        let et = unify e1t (TyArrow (e2t, bt))
        let s = compose_subst (compose_subst et e1s) e2s

        (apply_subst bt s, s)

    | IfThenElse (e1, e2, e3o) ->
        let e1t, e1s = typeinfer_expr env e1
        let e1s = compose_subst (unify TyBool e1t) e1s
        
        let env = apply_subst_env env e1s

        let e2t, e2s = typeinfer_expr env e2
        
        match e3o with
        | None ->
            let e2s = compose_subst (unify TyUnit e2t) e2s

            let s = compose_subst e1s e2s

            (TyUnit, s)
        | Some e3 ->
            let env = apply_subst_env env e2s
            let e3t, e3s = typeinfer_expr env e3
            
            let e3s = compose_subst (unify e2t e3t) e3s
            
            let s = compose_subst (compose_subst e1s e2s) e3s

            (apply_subst e2t s, s)
    
    | Tuple es ->
        List.foldBack (
            fun el (t, s) ->
                let t = match t with
                        | TyTuple t -> t
                        | _ -> unexpected_error "typeinfer_expr: not found a tuple"
                
                let env = apply_subst_env env s
                let et, es = typeinfer_expr env el
                
                let s = compose_subst es s

                (TyTuple (et :: t), s)
            ) es (TyTuple [], [])

    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as _), e2) ->
        let e1t, e1s = typeinfer_expr env e1
        
        let env = apply_subst_env env e1s
        
        let e2t, e2s = typeinfer_expr env e2
        
        let possibleUnifications = [
                 (TyInt, TyInt, TyInt)
                 (TyInt, TyFloat, TyFloat)
                 (TyFloat, TyInt, TyFloat)
                 (TyFloat, TyFloat, TyFloat)
        ]

        unify_binops possibleUnifications (e1t, e1s) (e2t, e2s) None

    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as _), e2) ->
        let e1t, e1s = typeinfer_expr env e1
        
        let env = apply_subst_env env e1s
                
        let e2t, e2s = typeinfer_expr env e2
        
        let possibleUnifications = [
                 (TyInt, TyInt, TyBool)
                 (TyInt, TyFloat, TyBool)
                 (TyFloat, TyInt, TyBool)
                 (TyFloat, TyFloat, TyBool)
        ]

        unify_binops possibleUnifications (e1t, e1s) (e2t, e2s) None

    | BinOp (e1, ("and" | "or" as _), e2) ->
        let e1t, e1s = typeinfer_expr env e1
        
        let env = apply_subst_env env e1s
        
        let e2t, e2s = typeinfer_expr env e2
        
        let s1 = compose_subst (unify TyBool e1t) e1s
        let s2 = compose_subst (unify TyBool e2t) e2s
        let s = compose_subst s1 s2
        
        (TyBool, s)
        
    | BinOp (_, op, _) -> unexpected_error "typeinfer_expr: unsupported binary operator (%s)" op

    | UnOp ("-", e) ->
        let et, es = typeinfer_expr env e
        
        let possibleUnifications = [
                 (TyInt, TyInt)
                 (TyFloat, TyFloat)
        ]

        unify_unops possibleUnifications (et, es) None
 
    | UnOp ("not", e) ->
        let et, es = typeinfer_expr env e
        let s =  compose_subst (unify TyBool et) es
        
        (TyBool, s)
        
    | UnOp (op, _) -> unexpected_error "typeinfer_expr: unsupported unary operator (%s)" op

    | _ -> unexpected_error "typeinfer_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
