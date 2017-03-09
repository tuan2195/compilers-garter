open Types
open Printf
open Instruction
open Expr
open Pretty

(* Add or change these constants as needed *)
let err_COMP_NOT_NUM   = 1
let err_ARITH_NOT_NUM  = 2
let err_LOGIC_NOT_BOOL = 3
let err_IF_NOT_BOOL    = 4
let err_OVERFLOW       = 5
let err_GET_NOT_TUPLE  = 6
let err_GET_LOW_INDEX  = 7
let err_GET_HIGH_INDEX = 8
let err_INDEX_NOT_NUM  = 9


let const_true = HexConst (0xFFFFFFFF)
let const_false = HexConst(0x7FFFFFFF)
let bool_mask = HexConst(0x80000000)
let tag_bool = HexConst(0x00000001)


type 'a envt = (string * 'a) list

let rec is_anf (e : 'a expr) : bool =
  match e with
  | EPrim1(_, e, _) -> is_imm e
  | EPrim2(_, e1, e2, _) -> is_imm e1 && is_imm e2
  | ELet(binds, body, _) ->
     List.for_all (fun (_, e, _) -> is_anf e) binds
     && is_anf body
  | EIf(cond, thn, els, _) -> is_imm cond && is_anf thn && is_anf els
  | _ -> is_imm e
and is_imm e =
  match e with
  | ENumber _ -> true
  | EBool _ -> true
  | EId _ -> true
  | _ -> false
;;


(* FINISH THIS FUNCTION WITH THE WELL-FORMEDNESS FROM FER-DE-LANCE *)
let well_formed (p : (Lexing.position * Lexing.position) program) builtins : exn list =
  let rec wf_E e (env : sourcespan envt) =
    let rec dupe x binds =
        match binds with
        | [] -> None
        | (y, _, pos)::_ when x = y -> Some pos
        | _::rest -> dupe x rest in
    match e with
    | ELet(binds, body, _) ->
        let rec process_binds rem_binds env =
            match rem_binds with
            | [] -> (env, [])
            | (x, e, pos)::rest ->
                let shadow = match dupe x rest with
                    | Some where -> [DuplicateId(x, where, pos)]
                    | None ->
                        try let existing = List.assoc x env in
                            [ShadowId(x, pos, existing)]
                        with Not_found -> [] in
                let errs_e = wf_E e env  in
                let new_env = (x, pos)::env in
                let (newer_env, errs) = process_binds rest new_env in
                (newer_env, (shadow @ errs_e @ errs)) in
        let (env2, errs) = process_binds binds env in
        errs @ wf_E body env2
    | ELetRec(binds, body, _) ->
        let rec build_env b =
            match b with
            | [] -> []
            | (x, _, pos)::rest -> (x, pos)::build_env rest in
        let new_env = env @ build_env binds in
        let rec process_binds rem_binds =
            match rem_binds with
            | [] -> []
            | (x, e, pos)::rest ->
                match e with
                | ELambda _ ->
                    let shadow = match dupe x rest with
                        | Some where -> [DuplicateFun(x, where, pos)]
                        | None ->
                            try let existing = List.assoc x env in
                                [ShadowId(x, pos, existing)]
                            with Not_found -> [] in
                    let errs_e = wf_E e new_env in
                    let errs = process_binds rest in
                    (shadow @ errs_e @ errs)
                | _ ->
                    let errs = process_binds rest in
                    LetRecNonFunction(x, pos)::errs in
        let errs = process_binds binds in
        errs @ wf_E body new_env
    | EBool _ -> []
    | ENumber(n, loc) ->
       if n > 1073741823 || n < -1073741824 then [Overflow(n, loc)] else []
    | EId (x, loc) ->
       (try ignore (List.assoc x env); []
        with Not_found ->
             [UnboundId(x, loc)])
    | EPrim1(_, e, _) -> wf_E e env
    | EPrim2(_, l, r, _) -> wf_E l env @ wf_E r env
    | EIf(c, t, f, _) -> wf_E c env @ wf_E t env @ wf_E f env
    | ETuple(vals, _) -> List.concat (List.map (fun e -> wf_E e env) vals)
    | EGetItem(tup, idx, _) -> wf_E tup env @ wf_E idx env
    | ESetItem(tup, idx, rhs, _) -> wf_E tup env @ wf_E idx env @ wf_E rhs env
    | ESeq(stmts, _) -> List.flatten (List.map (fun s -> wf_E s env) stmts)
    | ELambda(args, body, _) ->
       wf_E body (args @ env)
    | EApp(func, args, loc) ->
       (wf_E func env) @ List.concat (List.map (fun e -> wf_E e env) args)
  in
  wf_E p builtins
;;

type 'a anf_bind =
  | BSeq of 'a cexpr
  | BLet of string * 'a cexpr
  | BLetRec of (string * 'a cexpr) list

let anf (p : tag program) : unit aprogram =
  let rec helpP (p : tag program) : unit aprogram = helpA p
  and helpC (e : tag expr) : (unit cexpr * unit anf_bind list) =
    match e with
    | EPrim1(op, arg, _) ->
       let (arg_imm, arg_setup) = helpI arg in
       (CPrim1(op, arg_imm, ()), arg_setup)
    | EPrim2(op, left, right, _) ->
       let (left_imm, left_setup) = helpI left in
       let (right_imm, right_setup) = helpI right in
       (CPrim2(op, left_imm, right_imm, ()), left_setup @ right_setup)
    | EIf(cond, _then, _else, _) ->
       let (cond_imm, cond_setup) = helpI cond in
       (CIf(cond_imm, helpA _then, helpA _else, ()), cond_setup)
    | ESeq([], _) -> failwith "Impossible by syntax"
    | ESeq([stmt], _) -> helpC stmt
    | ESeq(fst :: rest, tag) ->
       let (fst_ans, fst_setup) = helpC fst in
       let (rest_ans, rest_setup) = helpC (ESeq(rest, tag)) in
       (rest_ans, fst_setup @ [BSeq fst_ans] @ rest_setup)
    | ELet([], body, _) -> helpC body
    | ELet((bind, exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [BLet (bind, exp_ans)] @ body_setup)
    | ELetRec(binds, body, _) ->
       let (names, new_binds_setup) = List.split (List.map (fun (name, rhs, _) -> (name, helpC rhs)) binds) in
       let (new_binds, new_setup) = List.split new_binds_setup in
       let (body_ans, body_setup) = helpC body in
       (body_ans, (BLetRec (List.combine names new_binds)) :: body_setup)
    | ELambda(args, body, _) ->
       (CLambda(List.map fst args, helpA body, ()), [])
    | EApp(func, args, _) ->
       let (new_func, func_setup) = helpI func in
       let (new_args, new_setup) = List.split (List.map helpI args) in
       (CApp(new_func, new_args, ()), func_setup @ List.concat new_setup)
    | ETuple(args, _) ->
       let (new_args, new_setup) = List.split (List.map helpI args) in
       (CTuple(new_args, ()), List.concat new_setup)
    | EGetItem(tup, idx, _) ->
       let (tup_imm, tup_setup) = helpI tup in
       let (idx_imm, idx_setup) = helpI idx in
       (CGetItem(tup_imm, idx_imm, ()), tup_setup @ idx_setup)
    | ESetItem(tup, idx, rhs, _) ->
       let (tup_imm, tup_setup) = helpI tup in
       let (idx_imm, idx_setup) = helpI idx in
       let (rhs_imm, rhs_setup) = helpI rhs in
       (CSetItem(tup_imm, idx_imm, rhs_imm, ()), tup_setup @ idx_setup @ rhs_setup)
    | _ -> let (imm, setup) = helpI e in (CImmExpr imm, setup)

  and helpI (e : tag expr) : (unit immexpr * unit anf_bind list) =
    match e with
    | ENumber(n, _) -> (ImmNum(n, ()), [])
    | EBool(b, _) -> (ImmBool(b, ()), [])
    | EId(name, _) -> (ImmId(name, ()), [])

    | EPrim1(op, arg, tag) ->
       let tmp = sprintf "unary_%d" tag in
       let (arg_imm, arg_setup) = helpI arg in
       (ImmId(tmp, ()), arg_setup @ [BLet(tmp, CPrim1(op, arg_imm, ()))])
    | EPrim2(op, left, right, tag) ->
       let tmp = sprintf "binop_%d" tag in
       let (left_imm, left_setup) = helpI left in
       let (right_imm, right_setup) = helpI right in
       (ImmId(tmp, ()), left_setup @ right_setup @ [BLet(tmp, CPrim2(op, left_imm, right_imm, ()))])
    | EIf(cond, _then, _else, tag) ->
       let tmp = sprintf "if_%d" tag in
       let (cond_imm, cond_setup) = helpI cond in
       (ImmId(tmp, ()), cond_setup @ [BLet(tmp, CIf(cond_imm, helpA _then, helpA _else, ()))])
    | EApp(func, args, tag) ->
       let tmp = sprintf "app_%d" tag in
       let (new_func, func_setup) = helpI func in
       let (new_args, new_setup) = List.split (List.map helpI args) in
       (ImmId(tmp, ()), (func_setup @ List.concat new_setup) @ [BLet(tmp, CApp(new_func, new_args, ()))])
    | ESeq([], _) -> failwith "Impossible by syntax"
    | ESeq([stmt], _) -> helpI stmt
    | ESeq(fst :: rest, tag) ->
       let (fst_ans, fst_setup) = helpC fst in
       let (rest_ans, rest_setup) = helpI (ESeq(rest, tag)) in
       (rest_ans, fst_setup @ [BSeq fst_ans] @ rest_setup)
    | ELet([], body, _) -> helpI body
    | ELet((bind, exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [BLet(bind, exp_ans)] @ body_setup)
    | ELetRec(binds, body, tag) ->
       let tmp = sprintf "lam_%d" tag in
       let (names, new_binds_setup) = List.split (List.map (fun (name, rhs, _) -> (name, helpC rhs)) binds) in
       let (new_binds, new_setup) = List.split new_binds_setup in
       let (body_ans, body_setup) = helpC body in
       (ImmId(tmp, ()), (List.concat new_setup)
                        @ [BLetRec (List.combine names new_binds)]
                        @ body_setup
                        @ [BLet(tmp, body_ans)])
    | ELambda(args, body, tag) ->
       let tmp = sprintf "lam_%d" tag in
       (ImmId(tmp, ()), [BLet(tmp, CLambda(List.map fst args, helpA body, ()))])
    | ETuple(args, tag) ->
       let tmp = sprintf "tup_%d" tag in
       let (new_args, new_setup) = List.split (List.map helpI args) in
       (ImmId(tmp, ()), (List.concat new_setup) @ [BLet(tmp, CTuple(new_args, ()))])
    | EGetItem(tup, idx, tag) ->
       let tmp = sprintf "get_%d" tag in
       let (tup_imm, tup_setup) = helpI tup in
       let (idx_imm, idx_setup) = helpI idx in
       (ImmId(tmp, ()), tup_setup @ idx_setup @ [BLet(tmp, CGetItem(tup_imm, idx_imm, ()))])
    | ESetItem(tup, idx, rhs, tag) ->
       let tmp = sprintf "set_%d" tag in
       let (tup_imm, tup_setup) = helpI tup in
       let (idx_imm, idx_setup) = helpI idx in
       let (rhs_imm, rhs_setup) = helpI rhs in
       (ImmId(tmp, ()), tup_setup @ idx_setup @ rhs_setup @ [BLet(tmp, CSetItem(tup_imm, idx_imm, rhs_imm, ()))])
  and helpA e : unit aexpr =
    let (ans, ans_setup) = helpC e in
    (*List.fold_left*)
      (*(fun body bind ->*)
        (*match bind with*)
        (*| BSeq(exp) -> ASeq(exp, body, ())*)
        (*| BLet(name, exp) -> ALet(name, exp, body, ())*)
        (*| BLetRec(names) -> ALetRec(names, body, ()))*)
      (*(ACExpr ans)*)
      (*ans_setup*)
    List.fold_right
      (fun bind body ->
        match bind with
        | BSeq(exp) -> ASeq(exp, body, ())
        | BLet(name, exp) -> ALet(name, exp, body, ())
        | BLetRec(names) -> ALetRec(names, body, ()))
      ans_setup
      (ACExpr ans)
  in
  helpP p
;;

(*let free_vars (e : 'a aexpr) : string list =*)
  (*let rec helpA (bound : string list) (e : 'a aexpr) : string list =*)
     (*match e with*)
     (*| ASeq(fst, rest, _) ->*)
        (*helpC bound fst @ helpA bound rest*)
     (*| ALet(name, binding, body, _) ->*)
       (*(helpC bound binding) (* all the free variables in the binding, plus *)*)
       (*(* all the free variables in the body, except the name itself *)*)
       (*@ (helpA (name :: bound) body)*)
     (*| ALetRec(bindings, body, _) ->*)
        (*let names = List.map fst bindings in*)
        (*let new_bound = (names @ bound) in*)
        (*(helpA new_bound body) @ List.flatten (List.map (fun binding -> helpC new_bound (snd binding)) bindings)*)
     (*| ACExpr c -> helpC bound c*)
  (*and helpC (bound : string list) (e : 'a cexpr) : string list =*)
    (*match e with*)
    (*| CLambda(args, body, _) ->*)
      (*helpA (args @ bound) body*)
    (*| CIf(cond, thn, els, _) ->*)
      (*helpI bound cond @ helpA bound thn @ helpA bound els*)
    (*| CPrim1(_, arg, _) -> helpI bound arg*)
    (*| CPrim2(_, left, right, _) -> helpI bound left @ helpI bound right*)
    (*| CApp(fn, args, _) ->*)
      (*(helpI bound fn) @ (List.flatten (List.map (fun arg -> helpI bound arg) args))*)
    (*| CTuple(vals, _) -> List.flatten (List.map (fun v -> helpI bound v) vals)*)
    (*| CGetItem(tup, idx, _) -> helpI bound tup @ helpI bound idx*)
    (*| CSetItem(tup, idx, rhs, _) -> helpI bound tup @ helpI bound idx @ helpI bound rhs*)
    (*| CImmExpr i -> helpI bound i*)
  (*and helpI (bound : string list) (e : 'a immexpr) : string list =*)
    (*match e with*)
    (*| ImmId(name, _) ->*)
      (*(* a name is free if it is not bound *)*)
      (*if List.mem name bound then [] else [name]*)
    (*| _ -> []*)
  (*in List.sort_uniq String.compare (helpA [] e)*)
(*;;*)

let reserve size tag =
  let ok = sprintf "$memcheck_%d" tag in
  [
    IMov(Reg(EAX), LabelContents("HEAP_END"));
    ISub(Reg(EAX), Const(size));
    ICmp(Reg(EAX), Reg(ESI));
    IJge(ok);
    IPush(Reg(ESP)); (* stack_top in C *)
    IPush(Reg(EBP)); (* first_frame in C *)
    IPush(Const(size)); (* bytes_needed in C *)
    IPush(Reg(ESI)); (* alloc_ptr in C *)
    ICall(Label("try_gc"));
    IAdd(Reg(ESP), Const(16)); (* clean up after call *)
    (* assume gc success if returning here, so EAX holds the new ESI value *)
    IMov(Reg(ESI), Reg(EAX));
    ILabel(ok);
  ]

(* Commonly used constants and macros *)
let const_true_value   = 0xFFFFFFFF
let const_true         = Sized(DWORD_PTR, HexConst(const_true_value))
let const_false_value  = 0x7FFFFFFF
let const_false        = Sized(DWORD_PTR, HexConst(const_false_value))
let bool_mask          = Sized(DWORD_PTR, HexConst(0x80000000))
let tag_bool           = Sized(DWORD_PTR, HexConst(0x00000007))
let tag_1_bit          = Sized(DWORD_PTR, HexConst(0x00000001))
let tag_3_bit          = Sized(DWORD_PTR, HexConst(0x00000007))
let tag_func           = Sized(DWORD_PTR, HexConst(0x00000005))
let offset_func        = 0x5

let err_COMP_NOT_NUM   = (Const(01), "__err_COMP_NOT_NUM__")
let err_ARITH_NOT_NUM  = (Const(02), "__err_ARITH_NOT_NUM__")
let err_LOGIC_NOT_BOOL = (Const(03), "__err_LOGIC_NOT_BOOL__")
let err_IF_NOT_BOOL    = (Const(04), "__err_IF_NOT_BOOL__")
let err_OVERFLOW       = (Const(05), "__err_OVERFLOW__")
let err_NOT_TUPLE      = (Const(06), "__err_NOT_TUPLE__")
let err_INDEX_NOT_NUM  = (Const(07), "__err_INDEX_NOT_NUM__")
let err_INDEX_LARGE    = (Const(08), "__err_INDEX_LARGE__")
let err_INDEX_SMALL    = (Const(09), "__err_INDEX_SMALL__")
let err_NOT_LAMBDA     = (Const(10), "__err_NOT_LAMBDA__")
let err_WRONG_ARITY    = (Const(11), "__err_WRONG_ARITY__")

let label_func_begin name = sprintf "%s_func_begin__" name

let rec arg_to_const arg =
    match arg with
    | Const(x) | HexConst(x) -> Some(x)
    | Sized(_, a) -> arg_to_const a
    | _ -> None

let rec arg_to_const arg =
    match arg with
    | Const(x) | HexConst(x) -> Some(x)
    | Sized(_, a) -> arg_to_const a
    | _ -> None

let check_bool arg label =
    match arg_to_const arg with
    | Some(x) ->
        if (x = const_false_value || x = const_true_value) then
            [ IMov(Reg(EAX), arg); ]
        else
            [ IJmp(label); ]
    | _ ->
        [ IMov(Reg(EAX), arg);
          ITest(Reg(EAX), tag_bool);
          IJz(label); ]

let check_num arg label =
    match arg_to_const arg with
    | Some(x) ->
        if (x = const_false_value || x = const_true_value) then
            [ IJmp(label); ]
        else
            [ IMov(Reg(EAX), arg); ]
    | _ ->
        [ IMov(Reg(EAX), arg);
          ITest(Reg(EAX), tag_1_bit);
          IJnz(label); ]

let check_logic arg = check_bool arg (snd err_LOGIC_NOT_BOOL)
let check_if arg = check_bool arg (snd err_IF_NOT_BOOL)
let check_arith arg = check_num arg (snd err_ARITH_NOT_NUM)
let check_index arg = check_num arg (snd err_INDEX_NOT_NUM)
let check_compare arg = check_num arg (snd err_COMP_NOT_NUM)

let block_true_false label op = [
    IMov(Reg(EAX), const_true);
    op label;
    IMov(Reg(EAX), const_false);
    ILabel(label);
]

let rec print_str ls =
    match ls with
    | [] -> ()
    | x::rs -> printf "%s | " x; print_str rs

let rec rm_dup ls =
    let rec rm_from ls x =
        (match ls with
        | [] -> []
        | n::rs when n = x -> rm_from rs x
        | _ -> List.hd ls :: rm_from (List.tl ls) x ) in
    match ls with
    | [] -> []
    | x::rs ->
        let new_ls = rm_from rs x in
        x::rm_dup new_ls

let rec free_a ae env =
    match ae with
    | ALet(name, expr, body, _) ->
        free_c expr env @ free_a body (name::env)
    | ALetRec(expr_ls, body, _) ->
        (*let new_env = env @ (List.map fst expr_ls) in*)
        (*let free_ls = List.flatten (List.map (fun x -> free_c x new_env) (List.map snd expr_ls)) in*)
        (*free_ls @ free_a body new_env*)
        free_a body (env @ (List.map fst expr_ls))
    | ASeq(expr, rest, _) ->
        free_c expr env @ free_a rest env
    | ACExpr(e) ->
        free_c e env
and free_c ce env =
    match ce with
    | CIf(con, thn, els, _) ->
        free_i con env @
        free_a thn env @
        free_a els env
    | CPrim1(_, e, _) ->
        free_i e env
    | CPrim2(_, e1, e2, _) ->
        free_i e1 env @
        free_i e2 env
    | CApp(func, args, _) ->
        free_i func env @
        List.flatten (List.map (fun x -> free_i x env) args)
    | CTuple(args, _) ->
        List.flatten (List.map (fun x -> free_i x env) args)
    | CGetItem(tup, idx, _) ->
        free_i tup env @ free_i idx env
    | CLambda(args, expr, _) ->
        free_a expr args
    | CImmExpr(i) ->
        free_i i env
    | CSetItem(tup, idx, expr, _) ->
        free_i tup env @ free_i idx env @ free_i expr env
and free_i ie env =
    match ie with
    | ImmNum _ | ImmBool _ -> []
    | ImmId(x, _) ->
        (try ignore (List.find (fun s -> s = x) env); [] with Not_found -> [x])

let free_vars ae = rm_dup (free_a ae [])

(*let rec count_vars e = 16 (* Temporary fix *)*)
let count_vars e =
  let rec helpA e =
    match e with
    | ALet(_, bind, body, _) -> 1 + (helpC bind) + (helpA body)
    | ALetRec(expr_ls, body, _) -> 1 + (List.length expr_ls) + (helpA body)
    | ASeq(expr, rest, _) -> helpC expr + helpA rest
    | ACExpr e -> helpC e
  and helpC e =
    match e with
    | CIf(_, t, f, _) -> (helpA t) + (helpA f)
    | _ -> 0
  in helpA e + List.length (free_vars e)

let lambda_heap_size e =
    match e with
    | CLambda(args, expr, t) ->
        let size = (List.length (rm_dup (free_a expr args)) + 2) in
        if size mod 2 = 0 then size
        else size + 1
    | _ -> failwith "Not a lambda!"

let rec replicate x i =
  if i = 0 then []
  else x :: (replicate x (i - 1))

let rec find ls x =
  match ls with
  | [] -> failwith (sprintf "Name %s not found" x)
  | (y,v)::rest ->
     if y = x then v else find rest x

let rec print_env e cmt =
    match e with
    | [] -> ()
    | (x, _)::rest -> printf "%s: %s\n" cmt x; print_env rest cmt


let rec compile_fun fun_name env e offset =
    let compiled = (compile_aexpr e (offset + 1) env (List.length env - offset) true) in
    let count_local_vars = count_vars e in
    let optimized = optimize compiled in
    (([
        ILabel(fun_name);
        ILineComment("Function prologue");
        IPush(Reg(EBP));
        IMov(Reg(EBP), Reg(ESP)) ]
        @ replicate (IPush(Sized(DWORD_PTR, Const(0)))) count_local_vars),
        ( [ ILabel(label_func_begin fun_name);
            ILineComment("Function body") ]
        @ optimized), [
        ILineComment("Function epilogue");
        IMov(Reg(ESP), Reg(EBP));
        IPop(Reg(EBP));
        IInstrComment(IRet, sprintf "End of %s" fun_name)
    ])
and compile_aexpr e si env num_args is_tail =
    match e with
    | ALetRec(expr_ls, body, _) ->
        (*let new_env = env @ (List.mapi*)
            (*(fun i x -> (fst x, RegOffset(word_size*(~-(si+i)), EBP)))*)
            (*expr_ls) in*)
        (*let new_si = si + (List.length expr_ls) in*)
        (*let funcs = List.flatten (List.map*)
            (*(fun x ->*)
                (*(compile_cexpr (snd x) new_si new_env num_args false) @*)
                (*[ IMov(find new_env (fst x), Reg(EAX)); ] )*)
            (*expr_ls) in*)
        (*let main = compile_aexpr body new_si new_env num_args true in*)
        (*funcs @ main*)
        let new_env = env @ (List.mapi
            (fun i x -> (fst x, RegOffset(word_size*(~-(si+i)), EBP)))
            expr_ls) in
        let new_si = si + (List.length expr_ls) in
        let (_, load) = List.fold_left
            (fun (heap, prev) x -> (lambda_heap_size (snd x), prev @ [
                ILineComment(sprintf "Preload function %s" (fst x));
                IAdd(Reg(EDX), Const(word_size*heap));
                IMov(find new_env (fst x), Reg(EDX)); ]))
            (0, [])
            expr_ls in
        let preload = [ IMov(Reg(EDX), Reg(ESI)); IAdd(Reg(EDX), tag_func) ] @ load in
        let funcs = List.flatten (List.map
            (fun x -> compile_cexpr (snd x) new_si new_env num_args false)
            expr_ls) in
        let main = compile_aexpr body new_si new_env num_args true in
        preload @ funcs @ main
    | ALet(name, expr, body, _) ->
        let arg = RegOffset(~-si*word_size, EBP) in
        let new_env = (name, arg)::env in
        let setup = compile_cexpr expr si env num_args false in
        let main = compile_aexpr body (si+1) new_env num_args true in
        let cmt = comment expr name in
        cmt @ setup @ [ IMov(arg, Reg(EAX)) ] @ main
    | ASeq(expr, rest, _) ->
        compile_cexpr expr si env num_args false @
        compile_aexpr rest si env num_args false
    | ACExpr(e) ->
        compile_cexpr e si env num_args true
and compile_cexpr e si env num_args is_tail =
    match e with
    | CIf (cnd, thn, els, t) ->
        let label_false = sprintf "__if_%d_false__" t in
        let label = sprintf "__if_%d_done__" t in
        let argCond = compile_imm cnd env in
        check_if argCond @ [
            ICmp(Reg(EAX), const_false);
            IJe(label_false);
        ] @ compile_aexpr thn si env num_args true @ [
            IJmp(label);
            ILabel(label_false);
        ] @ compile_aexpr els si env num_args true @ [
            ILabel(label);
        ]
    | CPrim1(op, e, t) ->
        let arg = compile_imm e env in
        let label = sprintf "__isboolnum_done_%d__" t in
        (match op with
        | Add1 ->
            check_arith arg @ [
            IAdd(Reg(EAX), Const(1 lsl 1));
            IJo(snd err_OVERFLOW);
        ]
        | Sub1 ->
            check_arith arg @ [
            ISub(Reg(EAX), Const(1 lsl 1));
            IJo(snd err_OVERFLOW);
        ]
        | IsBool ->
            [ IMov(Reg(EAX), arg); ITest(Reg(EAX), tag_bool); ] @
            block_true_false label (fun x -> IJnz(x))
        | IsNum ->
            [ IMov(Reg(EAX), arg); ITest(Reg(EAX), tag_bool); ] @
            block_true_false label (fun x -> IJnz(x))
        | Not ->
            check_logic arg @ [
            IXor(Reg(EAX), bool_mask);
        ]
        | PrintStack ->
            failwith "PrintStack not implemented"
        | Print -> [
            IMov(Reg(EAX), arg);
            IPush(Reg(EAX));
            ICallLabel("print");
            IPop(Reg(EAX));
        ]
        | IsTuple ->
            [ IMov(Reg(EAX), arg); IAnd(Reg(EAX), tag_bool); ICmp(Reg(EAX), HexConst(0x1)); ] @
            block_true_false label (fun x -> IJne(x))
        )
    | CPrim2(op, e1, e2, t) ->
        let arg1 = compile_imm e1 env in
        let arg2 = compile_imm e2 env in
        let label = sprintf "__compare_%d__" t in
        let comp op = [ ICmp(Reg(EAX), arg2); ] @ block_true_false label op in
        let prelude = match op with
            | Plus | Minus | Times -> check_arith arg2 @ check_arith arg1
            | Greater | GreaterEq | Less | LessEq -> check_compare arg2 @ check_compare arg1
            | And | Or -> check_logic arg2 @ check_logic arg1
            | _ -> []
        in prelude @ (match op with
        | Plus -> [
            IAdd(Reg(EAX), arg2);
            IJo(snd err_OVERFLOW);
        ]
        | Minus -> [
            ISub(Reg(EAX), arg2);
            IJo(snd err_OVERFLOW);
        ]
        | Times -> [
            IMul(Reg(EAX), arg2);
            IJo(snd err_OVERFLOW);
            ISar(Reg(EAX), Const(1));
        ]
        | And ->
            [ IAnd(Reg(EAX), arg2); ]
        | Or ->
            [ IOr(Reg(EAX), arg2); ]
        | Greater ->
            comp (fun x -> IJg(x))
        | GreaterEq ->
            comp (fun x -> IJge(x))
        | Less ->
            comp (fun x -> IJl(x))
        | LessEq ->
            comp (fun x -> IJle(x))
        | Eq -> [
            IMov(Reg(EAX), arg1);
            ICmp(Reg(EAX), arg2);
            IMov(Reg(EAX), const_true);
            IJe(label);
            IPush(Sized(DWORD_PTR, arg1));
            IPush(Sized(DWORD_PTR, arg2));
            ICallLabel("equal");
            IAdd(Reg(ESP), Const(word_size * 2));
            ILabel(label);
        ]
        )
    | CLambda(args, expr, t) ->
        let free_ls = rm_dup (free_a expr args) in
        let func_name = sprintf "__lambda_%d__" t in
        let label = sprintf "__lambda_%d_done__" t in
        let mov_free_vars = [ ILineComment("Load free variables to heap"); ] @
            List.flatten ( List.mapi
            (fun i id -> [
                IMov(Reg(EDX), compile_imm (ImmId(id, 0)) env);
                IMov(RegOffset((i+2)*word_size, ESI), Reg(EDX)); ])
            free_ls ) in
        let heap_size =
            let size = List.length free_ls + 2 in
            if size mod 2 = 0 then size
            else size + 1 in
        let setup = [
            IMov(Sized(DWORD_PTR, RegOffset(0, ESI)), Const(List.length args));
            IMov(Sized(DWORD_PTR, RegOffset(word_size, ESI)), Label(func_name));
        ] @ mov_free_vars @ [
            IMov(Reg(EAX), Reg(ESI));
            IOr(Reg(EAX), tag_func);
            IAdd(Reg(ESI), Const(word_size * heap_size));
            IJmp(label);
        ] in
        let func_env =
            List.mapi (fun i id -> (id, RegOffset(word_size*(i+2), EBP))) args @
            List.mapi (fun i id -> (id, RegOffset(word_size*(~-(i+1)), EBP))) free_ls in
        let (prologue, body, epilogue) = compile_fun func_name func_env expr (List.length free_ls) in
        let reload = [
            ILineComment("Reload free variables from heap");
            IMov(Reg(ECX), RegOffset(word_size*(List.length args+2), EBP));
        ] @ List.flatten (List.mapi
            (fun i id -> [
                IMov(Reg(EDX), RegOffset(word_size*(i+2)-offset_func, ECX));
                IMov(RegOffset(word_size*(~-(i+1)), EBP), Reg(EDX));
            ])
            free_ls ) in
        let main = prologue @ reload @ body @ epilogue in
        let post = [ ILabel(label); ] in
        setup @ main @ post
    | CApp(func, args, _) ->
        let tests = [
            IMov(Reg(EAX), compile_imm func env);
            IAnd(Reg(EAX), tag_3_bit);
            ICmp(Reg(EAX), tag_func);
            IJne(snd err_NOT_LAMBDA);
            IMov(Reg(EAX), compile_imm func env);
            IMov(Reg(EBX), RegOffset(~-offset_func, EAX));
            ICmp(Reg(EBX), Const(List.length args));
            IJne(snd err_WRONG_ARITY);
        ] in
        let setup = [ IPush(Reg(EAX)); ] @ List.map
            (fun arg -> IPush(Sized(DWORD_PTR, arg)))
            (List.rev_map (fun x -> compile_imm x env) args) in
        let call = [
            IMov(Reg(EAX), RegOffset(word_size-offset_func, EAX));
            ICall(Reg(EAX));
        ] in
        let teardown =
            let len = (List.length args + 1) in
            [ IInstrComment(IAdd(Reg(ESP), Const(word_size * len)), sprintf "Pop %d arguments" len) ] in
        tests @ setup @ call @ teardown
    | CImmExpr(e) ->
        [ IMov(Reg(EAX), compile_imm e env) ]
    | CTuple(expr_ls, _) ->
        let size = List.length expr_ls in
        let prelude = [
            IMov(Reg(EAX), Reg(ESI));
            IOr(Reg(EAX), tag_1_bit);
            IMov(Sized(DWORD_PTR, RegOffset(0, ESI)), Const(size)); ] in
        let (_, load) = List.fold_left
            (fun (offset, ls) arg -> (offset+word_size, ls @ [
                IMov(Sized(DWORD_PTR, Reg(EDX)), compile_imm arg env);
                IMov(Sized(DWORD_PTR, RegOffset(offset, ESI)), Reg(EDX));
            ]) )
            (word_size, [])
            expr_ls in
        let padding =
            if size mod 2 = 0 then [ IAdd(Reg(ESI), Const(word_size*(size+2))); ]
            else [ IAdd(Reg(ESI), Const(word_size*(size+1))); ] in
        prelude @ load @ padding
    | CGetItem(tup, idx, _) ->
        tuple_test tup idx env @ [
        IMov(Reg(EAX), RegOffsetReg(ECX, EAX, word_size, 0));
        ]
    | CSetItem(tup, idx, expr, _) ->
        tuple_test tup idx env @ [
        IMov(Reg(EDX), compile_imm expr env);
        IMov(RegOffsetReg(ECX, EAX, word_size, 0), Reg(EDX));
        ]
and tuple_test tup idx env = [
    IMov(Reg(ECX), compile_imm tup env);
    (* TODO: Better testing *)
    ITest(Reg(ECX), tag_1_bit);
    IJz(snd err_NOT_TUPLE);
    ISub(Reg(ECX), Const(1)); ]
  @ check_index (compile_imm idx env) @ [
    ISar(Reg(EAX), Const(1));
    ICmp(Reg(EAX), Const(0));
    IJl(snd err_INDEX_SMALL);
    IAdd(Reg(EAX), Const(1));
    IMov(Reg(EDX), RegOffset(0, ECX));
    ICmp(Reg(EAX), Reg(EDX));
    IJg(snd err_INDEX_LARGE);
    ]
and compile_imm e env =
    match e with
    | ImmNum(n, _) -> Const(n lsl 1)
    | ImmBool(true, _) -> const_true
    | ImmBool(false, _) -> const_false
    | ImmId(x, _) -> (find env x)
and id_name e =
    match e with
    | ImmId(x, _) -> x
    | _ -> failwith "Not a variable!"
and comment e s =
    match e with
    | CLambda _ -> [ ILineComment(sprintf "Function/Lambda: %s" s); ]
    | CApp(func, _, _) -> [ ILineComment(sprintf "Function/Lambda call: %s" (id_name func)) ;]
    | _ -> []
and strip ls = ls
    (*match ls with*)
    (*| [] -> []*)
    (*| ILineComment(_)::rest -> strip rest*)
    (*| IInstrComment(i, _)::rest -> i::strip rest*)
    (*| i::rest -> i::strip rest*)
and optimize ls =
    let rec opt ls =
        match ls with
        | [] -> []
        | IMov(RegOffset(o1, b1), Reg(r1))::IMov(Reg(r2), RegOffset(o2, b2))::rest ->
            if o1 = o2 && b1 = b2 && r1 = r2 then
                (List.hd ls)::opt rest
            else
                (List.hd ls)::opt (List.tl ls)
        | what::rest ->
            what::opt rest in
    opt (strip ls)
;;

(* IMPLEMENT THIS FROM YOUR PREVIOUS ASSIGNMENT -- THE ONLY NEW CODE IS CSetItem and ALet *)
(*let compile_fun name args body = failwith "NYI: compile_fun"*)

(* UPDATE THIS TO HANDLE FIRST-CLASS FUNCTIONS AS NEEDED *)
let call (label : arg) args =
  let setup = List.rev_map (fun arg ->
                  match arg with
                  | Sized _ -> IPush(arg)
                  | _ -> IPush(Sized(DWORD_PTR, arg))) args in
  let teardown =
    let len = List.length args in
    if len = 0 then []
    else [ IInstrComment(IAdd(Reg(ESP), Const(4 * len)), sprintf "Popping %d arguments" len) ] in
  setup @ [ ICall(label) ] @ teardown

(*let compile_prog anfed =*)
  (*let prelude =*)
    (*"section .text*)
(*extern error*)
(*extern print*)
(*extern equal*)
(*extern try_gc*)
(*extern HEAP_END*)
(*extern STACK_BOTTOM*)
(*global our_code_starts_here" in*)
  (*let suffix = sprintf "*)
(*err_comp_not_num:%s*)
(*err_arith_not_num:%s*)
(*err_logic_not_bool:%s*)
(*err_if_not_bool:%s*)
(*err_overflow:%s*)
(*err_get_not_tuple:%s*)
(*err_get_low_index:%s*)
(*err_get_high_index:%s*)
(*err_index_not_num:%s"*)
                       (*(* If you modified `call` above, then fix these up, too *)*)
                       (*(to_asm (call (Label "error") [Const(err_COMP_NOT_NUM)]))*)
                       (*(to_asm (call (Label "error") [Const(err_ARITH_NOT_NUM)]))*)
                       (*(to_asm (call (Label "error") [Const(err_LOGIC_NOT_BOOL)]))*)
                       (*(to_asm (call (Label "error") [Const(err_IF_NOT_BOOL)]))*)
                       (*(to_asm (call (Label "error") [Const(err_OVERFLOW)]))*)
                       (*(to_asm (call (Label "error") [Const(err_GET_NOT_TUPLE)]))*)
                       (*(to_asm (call (Label "error") [Const(err_GET_LOW_INDEX)]))*)
                       (*(to_asm (call (Label "error") [Const(err_GET_HIGH_INDEX)]))*)
                       (*(to_asm (call (Label "error") [Const(err_INDEX_NOT_NUM)]))*)
  (*in*)
  (*(* $heap is a mock parameter name, just so that compile_fun knows our_code_starts_here takes in 1 parameter *)*)
     (*let (prologue, comp_main, epilogue) = compile_fun "our_code_starts_here" ["$heap"] anfed in*)
     (*let heap_start = [*)
         (*IInstrComment(IMov(LabelContents("STACK_BOTTOM"), Reg(EBP)), "This is the bottom of our Garter stack");*)
         (*ILineComment("heap start");*)
         (*IInstrComment(IMov(Reg(ESI), RegOffset(8, EBP)), "Load ESI with our argument, the heap pointer");*)
         (*IInstrComment(IAdd(Reg(ESI), Const(7)), "Align it to the nearest multiple of 8");*)
         (*IInstrComment(IAnd(Reg(ESI), HexConst(0xFFFFFFF8)), "by adding no more than 7 to it")*)
       (*] in*)
     (*let main = (prologue @ heap_start @ comp_main @ epilogue) in*)

     (*sprintf "%s%s%s\n" prelude (to_asm main) suffix*)

let compile_prog anfed =
  let prelude =
    "section .text
extern error
extern print
extern input
extern equal
extern print_stack
global our_code_starts_here" in
    let suffix =
        let call err = [ ILabel(snd err); IPush(fst err); ICallLabel("error"); ] in
        to_asm (List.flatten [
            call err_COMP_NOT_NUM;
            call err_ARITH_NOT_NUM;
            call err_LOGIC_NOT_BOOL;
            call err_IF_NOT_BOOL;
            call err_OVERFLOW;
            call err_NOT_TUPLE;
            call err_INDEX_NOT_NUM;
            call err_INDEX_LARGE;
            call err_INDEX_SMALL;
            call err_NOT_LAMBDA;
            call err_WRONG_ARITY;
        ]) in
    let (prologue, comp_main, epilogue) = compile_fun "our_code_starts_here" [] anfed 0 in
    let heap_start = [
        ILineComment("heap start");
        IInstrComment(IMov(Reg(ESI), RegOffset(8, EBP)), "Load ESI with our argument, the heap pointer");
        IInstrComment(IAdd(Reg(ESI), Const(7)), "Align it to the nearest multiple of 8");
        IInstrComment(IAnd(Reg(ESI), HexConst(0xFFFFFFF8)), "by adding no more than 7 to it")
    ] in
    let main = strip (prologue @ heap_start @ comp_main @ epilogue) in
    sprintf "%s%s%s" prelude (to_asm main) suffix

let compile_to_string prog : (exn list, string) either =
  let env = [ (* DBuiltin("equal", 2) *) ] in
  let errors = well_formed prog env in
  match errors with
  | [] ->
     let tagged : tag program = tag prog in
     let anfed : tag aprogram = atag (anf tagged) in
     (* printf "Prog:\n%s\n" (ast_of_prog prog); *)
     (* printf "Tagged:\n%s\n" (format_prog tagged string_of_int); *)
     (* printf "ANFed/tagged:\n%s\n" (string_of_aprogram anfed); *)
     Right(compile_prog anfed)
  | _ -> Left(errors)

