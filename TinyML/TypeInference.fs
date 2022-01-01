(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

type subst = (tyvar * ty) list

// TODO: Analyze if it can be useful and what's the behaviour of List.map2 
//let rec map_two_lists f l1 l2 =
//    if List.length l1 <> List.length l2 then failwithf "L1 and L2 don't have the same length"
//    
//    match l1, l2 with
//    | [], [] -> []
//    | x1 :: xs1, x2 :: xs2 -> f x1 x2 @ (map_two_lists f xs1 xs2) 

let rec apply_subst (t : ty) (s : subst) : ty =
    match t with
    | TyName _ -> t
    | TyVar tv ->
                 try
                     let _, t2 = List.find (
                                     fun el ->
                                         let t1, _ = el
                                         t1 = tv
                                 ) s
                     
                     apply_subst t2 s
                 with e -> t
    | TyArrow (t1, t2) -> TyArrow (apply_subst t1 s, apply_subst t2 s)
    | TyTuple ts -> TyTuple (List.map (fun t -> apply_subst t s) ts)

let compose_subst (s1 : subst) (s2 : subst) : subst =
    if List.isEmpty s1 then
        s2
    else
        if List.isEmpty s2 then
            s1
        else 
            s2
            |> List.map (
                      fun el ->
                          let tv, t = el
                          
                          (tv, apply_subst t s1)
                    ) 
            |> List.filter (fun el ->
                            let el1, el2 = el
                            match el2 with
                            | TyVar tv -> el1 <> tv
                            | _ -> true
                        )

// TODO: verify if it works
let rec unify (t1 : ty) (t2 : ty) : subst =
    match t1, t2 with
    | TyName t1, TyName t2 -> if t1 = t2 then [] else type_error $"unify: impossible to unify {t1} with {t2}"
    | TyVar t1, t2
    | t2, TyVar t1 -> match t2 with
                      | TyVar t2 -> if t2 = t1 then type_error $"unify: impossible to unify {t1} with {t2}"
                      | _ -> ()
                      [(t1, t2)]
    | TyArrow(ty1, ty2), TyArrow(ty3, ty4) -> compose_subst (unify ty1 ty3) (unify ty2 ty4)
    | _, _ -> type_error $"unify: impossible to unify {t1} with {t2}"
//    | TyTuple t1s, TyTuple t2s -> map_two_lists unify t1s t2s

let rec freevars_ty (t : ty) : tyvar Set =
    match t with
    | TyName _ -> Set.empty
    | TyArrow (t1, t2) -> Set.union (freevars_ty t1) (freevars_ty t2)
    | TyVar tv -> Set.singleton tv
    | TyTuple ts -> List.fold (fun set t -> Set.union set (freevars_ty t)) Set.empty ts 

let freevars_scheme (Forall (tvs, t)) =
    Set.difference (freevars_ty t) (Set.ofList tvs)

// type inference
//

let generate_fresh_tyvar env =
    try 
        let res = env
                   |> List.filter (fun el -> match el with | _, TyVar t -> true | _ -> false)
                   |> List.map (fun el -> match el with | _, TyVar t -> t)
                   |> List.max
        res + 1
        
    with e -> 0
                                                
    
let rec typeinfer_expr (env : ty env) (e : expr) : ty * subst =
    match e with
    | Lit (LInt _) -> (TyInt, [])
    | Lit (LFloat _) -> (TyFloat, [])
    | Lit (LString _) -> (TyString, [])
    | Lit (LChar _) -> (TyChar, [])
    | Lit (LBool _) -> (TyBool, [])
    | Lit LUnit -> (TyUnit, [])

    | Var x ->
        let _, t = List.find (fun (y, _) -> x = y) env
        (t, [])

    | Let (x, None, e1, e2) -> // TOOO: Polymorphic let
        let e1t, e1s = typeinfer_expr env e1
//        let scheme = freevars_scheme (
//                Forall(env
//                       |> List.filter (fun el -> match el with | _, TyVar _ -> true | _ -> false)
//                       |> List.map (fun el -> match el with | _, TyVar t -> t),
//                       e1t)
//            )
        let env = (x, e1t) :: env
        let e2t, e2s = typeinfer_expr env e2
        
        let s = compose_subst e2s e1s
        
        (e2t, s)
        
    | Let (x, Some t1, e1, e2) ->
        let _, e1s = typeinfer_expr env e1
        let env = (x, t1) :: env
        let e2t, e2s = typeinfer_expr env e2
        
        let s = compose_subst e2s e1s
        
        (e2t, s)
        
    // TODO: LerRec type inference

    | Lambda(x, None, e) ->
        let pt = TyVar (generate_fresh_tyvar env)
        let env = (x, pt) :: env
        let bt, bs = typeinfer_expr env e
        
        (apply_subst (TyArrow (bt, pt)) bs, bs)
        
    | Lambda (x, Some t1, e) ->
        let env = (x, t1) :: env
        let bt, bs = typeinfer_expr env e
        
        (apply_subst (TyArrow (bt, t1)) bs, bs)
        
    | App (e1, e2) ->
        let e1t, e1s = typeinfer_expr env e1
        let e2t, e2s = typeinfer_expr env e2
        let bt = TyVar (generate_fresh_tyvar env)
        
        let et = unify e1t (TyArrow (e2t, bt))                
        let s = compose_subst (compose_subst et e1s) e2s
        
        (apply_subst bt s, s)
        
    | IfThenElse (e1, e2, e3o) ->
        let e1t, e1s = typeinfer_expr env e1
        let e2t, e2s = typeinfer_expr env e2
        
        let e1s = compose_subst (unify TyBool e1t) e1s
        
        match e3o with
        | None ->
            let e2s = compose_subst (unify TyUnit e2t) e2s
            
            (TyUnit, compose_subst e1s e2s)
        | Some e3 ->
            let e3t, e3s = typeinfer_expr env e3
            let e3s = compose_subst (unify e2t e3t) e3s
            
            (e2t, compose_subst (compose_subst e1s e2s) e3s)
    
//    TODO: Tuple type inference
    | Tuple es ->
        List.foldBack (
            fun el acc ->
                let t, s = acc
                let t = match t with | TyTuple t -> t
                let et, es = typeinfer_expr env el
                
                (TyTuple (et :: t), compose_subst s es)
            ) es (TyTuple [], [])
        
    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
        let e1t, e1s = typeinfer_expr env e1
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
                

    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
        let e1t, e1s = typeinfer_expr env e1
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

    | BinOp (e1, ("and" | "or" as op), e2) ->
        let e1t, e1s = typeinfer_expr env e1
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
    