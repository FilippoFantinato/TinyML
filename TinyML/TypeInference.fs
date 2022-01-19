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

//let apply_subst_env (env: scheme env) (s: subst) =
//    env |> List.map (
//        fun (x, sch) ->
//            (x, apply_subst_scheme sch s)
//   )

let apply_subst_env (env: scheme env) (s: subst) =
    (env, env) ||> List.fold (
        fun acc (x, sch) ->
            let newEl = (x, apply_subst_scheme sch s)
            let exist = acc |> List.tryFind (fun el -> el = newEl)
            
            match exist with
            | Some _ -> acc
            | None -> newEl :: acc
    )
    
    
let compose_subst (s1 : subst) (s2 : subst) : subst =
    if List.isEmpty s1 then
        s2
    else
        if List.isEmpty s2 then
            s1
        else 
            s1
            |> List.map (
                      fun (tv, t) ->
                          
                          (tv, apply_subst t s2)
                    )
            |> (@) (List.filter (
                        fun (tvs1, _) ->
                            try
                                s1 |> List.find (fun (tvs2, _) -> tvs1 = tvs2) |> ignore
                                false
                            with
                            | :? KeyNotFoundException -> true
                        ) s2)
            |> List.filter (fun el ->
                let el1, el2 = el
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
          
    | TyArrow(ty1, ty2), TyArrow(ty3, ty4) -> compose_subst (unify ty1 ty3) (unify ty4 ty2)
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


let generalization env t =
    ForAll (Set.toList (Set.difference (freevars_ty t) (freevars_environment env)), t)


let instantiation (ForAll (tvs, t)) maxTyVar =
    let s = tvs |> List.map (fun el -> (el, TyVar (maxTyVar + el)))
    
    (apply_subst t s, s)

// type inference
//

//let mutable tyVarReached = 0
//let generate_fresh_tyvar env =
//    tyVarReached <- tyVarReached + 1
//    tyVarReached

let generate_fresh_tyvar env =
    try
        let rec extract_greater_tyvar ty =
            match ty with
            | TyName _ -> 0
            | TyArrow (ty1, ty2) -> max (extract_greater_tyvar ty1) (extract_greater_tyvar ty2)
            | TyTuple tys -> tys |> List.map extract_greater_tyvar |> List.max
            | TyVar ty -> ty

        let max = env
                    |> List.map (fun (_, ForAll (_, t)) -> extract_greater_tyvar t)
                    |> List.max

        max + 1
    with e ->
        1


let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    match e with
    | Lit (LInt _) -> (TyInt, [])
    | Lit (LFloat _) -> (TyFloat, [])
    | Lit (LString _) -> (TyString, [])
    | Lit (LChar _) -> (TyChar, [])
    | Lit (LBool _) -> (TyBool, [])
    | Lit LUnit -> (TyUnit, [])

    | Var x ->
        let _, t = List.find (fun (y, _) -> x = y) env
        instantiation t (generate_fresh_tyvar env)

    | Let (x, None, e1, e2) -> // TOOO: Check if it works
        let e1t, e1s = typeinfer_expr env e1

        let env = (((x, generalization env e1t) :: env), e1s) ||> apply_subst_env

        let e2t, e2s = typeinfer_expr env e2

        let s = compose_subst e2s e1s
        
        (e2t, s)

    | Let (x, Some t1, e1, e2) ->
        let e1t, e1s = typeinfer_expr env e1
        unify e1t t1 |> ignore

        let env = ((x, generalization env e1t) :: env, e1s) ||> apply_subst_env
        
        let e2t, e2s = typeinfer_expr env e2
        
        let s = compose_subst e2s e1s

        (e2t, s)
 
    | LetRec (x, None, e1, e2) ->
        let xT = TyVar (generate_fresh_tyvar env)
        let e1t, e1s = typeinfer_expr ((x, ForAll ([], xT)) :: env) e1

        let e1tInfered = apply_subst xT e1s
        let e1s = compose_subst (unify e1tInfered e1t) e1s
        let e1t = apply_subst e1t e1s

        let env = ((x, generalization env e1t) :: env, e1s) ||> apply_subst_env
        
        let e2t, e2s = typeinfer_expr env e2

        let s = compose_subst e1s e2s
        
        (apply_subst e2t s, s)

    | LetRec (x, Some t, e1, e2) ->
        let xT = TyVar (generate_fresh_tyvar env)
        let e1t, e1s = typeinfer_expr ((x, ForAll ([], xT)) :: env) e1
        unify e1t t |> ignore
        
        let env = (((x, generalization env e1t) :: env), e1s) ||> apply_subst_env
        
        let e2t, e2s = typeinfer_expr env e2
        
        let s = compose_subst e2s e1s
        
        (apply_subst e2t s, s)

    | Lambda(x, None, e) ->
        let parameterT = TyVar (generate_fresh_tyvar env)
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

        let bt = TyVar (generate_fresh_tyvar env)

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
            
            let s = compose_subst e2s e1s

            (TyUnit, s)
        | Some e3 ->
            let env = apply_subst_env env e2s
            let e3t, e3s = typeinfer_expr env e3
            
            let e3s = compose_subst (unify e2t e3t) e3s
            
            let s = compose_subst (compose_subst e1s e2s) e3s

            (e2t, s)
    
    | Tuple es ->
        List.foldBack (
            fun el acc ->
                let t, s = acc
                let t = match t with
                        | TyTuple t -> t
                        | _ -> unexpected_error ""
                
                let env = apply_subst_env env s
                let et, es = typeinfer_expr env el
                
                let s = compose_subst s es

                (TyTuple (et :: t), s)
            ) es (TyTuple [], [])

    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as _), e2) ->
        let e1t, e1s = typeinfer_expr env e1
        
        let env = apply_subst_env env e1s
        
        let e2t, e2s = typeinfer_expr env e2
        
        try 
            let s1 = compose_subst (unify TyInt e1t) e1s
            
            try 
                let s2 = compose_subst (unify TyInt e2t) e2s
                
                (TyInt, compose_subst s1 s2)
            with e ->
                try 
                    let s2 = compose_subst (unify TyFloat e2t) e2s
                    (TyFloat, compose_subst s1 s2)
                with e ->
                    raise e
        with e ->
            try 
                let s1 = compose_subst (unify TyFloat e1t) e1s
                
                let s2 = try
                            compose_subst (unify TyInt e2t) e2s
                         with e ->
                            try 
                                compose_subst (unify TyFloat e2t) e2s
                            with e ->
                                raise e
                
                (TyFloat, compose_subst s1 s2)
            with e -> raise e

    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as _), e2) ->
        let e1t, e1s = typeinfer_expr env e1
        
        let env = apply_subst_env env e1s
        
        let e2t, e2s = typeinfer_expr env e2

        let s = try
                    let s1 = compose_subst (unify TyInt e1t) e1s
                    
                    let s2 = try 
                                compose_subst (unify TyInt e2t) e2s
                             with e ->
                                try 
                                    compose_subst (unify TyFloat e2t) e2s
                                with e ->
                                    raise e
                                    
                    compose_subst s1 s2
                with e ->
                    try 
                        let s1 = compose_subst (unify TyFloat e1t) e1s
                        
                        let s2 = try
                                    compose_subst (unify TyInt e2t) e2s
                                 with e ->
                                    try 
                                        compose_subst (unify TyFloat e2t) e2s
                                    with e ->
                                        raise e

                        compose_subst s1 s2
                    with e -> raise e
        
        (TyBool, s)

    | BinOp (e1, ("and" | "or" as _), e2) ->
        let e1t, e1s = typeinfer_expr env e1
        
        let env = apply_subst_env env e1s
        
        let e2t, e2s = typeinfer_expr env e2
        
        let s1 = compose_subst (unify TyBool e1t) e1s
        let s2 = compose_subst (unify TyBool e2t) e2s
        let s = compose_subst s1 s2
        
        (TyBool, s)
        
    // TODO: Improve or modify the error system
    | BinOp (_, op, _) -> unexpected_error "typecheck_expr: unsupported binary operator (%s)" op

    | UnOp ("-", e) ->
        let et, es = typeinfer_expr env e
        
        try
            (TyInt, compose_subst (unify TyInt et) es)
        with e ->
            try
                (TyFloat, compose_subst (unify TyFloat et) es)
            with e ->
                raise e
 
    | UnOp ("not", e) ->
        let et, es = typeinfer_expr env e
        let s =  compose_subst (unify TyBool et) es
        
        (TyBool, s)
        
    | UnOp (op, _) -> unexpected_error "typein_expr: unsupported unary operator (%s)" op

    | _ -> unexpected_error "typecheck_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
