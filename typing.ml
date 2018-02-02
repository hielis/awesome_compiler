open Ttree
open Ptree
(* utiliser cette exception pour signaler une erreur de typage *)
exception Error of string


let to_string (a : loc) =  "Implement me";;
let error_message a l = (a ^ (to_string l));;


let eq_type tref = function |Ttypenull -> not (tref = Tvoidstar)
                            |Tvoidstar -> not (tref = Tint || tref = Ttypenull)
                            |Tint -> (tref = Ttypenull) || (tref = Tint)
                            |Tstructp(_) as a-> (a = tref) || (tref = Ttypenull);;
(*checking structure type is not safe yet*)

let is_int = eq_type Tint;;

let string_of_type = function
  | Tvoidstar  -> "void*"
  | Ttypenull  -> "typenull"
  | Tint       -> "int"
  | Tstructp x -> "struct " ^ (x.str_name ^ " *")



let typ_context_opt context (v:Ttree.ident) = Hashtbl.find_opt context.vars v;;

let typ_context context v = match typ_context_opt context v.id with
  |None -> raise (Error(error_message (("Variable" ^ (v.id ^ " is undefined"))) v.id_loc))
  |Some(a) -> a
;;
let define_var context (t, i) = match (typ_context_opt context i.id) with
  |Some(_) -> raise (Error(error_message ("Attempt to redefine variable " ^ i.id) i.id_loc))
  |None -> Hashtbl.add context.vars i.id (convert_type t)
;;
let create_local_context = function
  |None -> {vars = (Hashtbl.create 64)}
  |Some(c) -> {vars = Hashtbl.copy c.vars}
;;



let program p =
  let function_table = Hashtbl.create 64 in (* An hashtable with all the functions ids as keys binded to (typ list * typ) à savoir les types des arguments et le type de retour *)

  let struct_table = Hashtbl.create 64 in (*An hashtable matching the structs id with their structures *)

  let convert_type = function |Ptree.Tstructp(i) -> (try Ttree.Tstructp (Hashtbl.find struct_table i.id)
                                                     with Not_found -> raise(Error(error_message "Typestruct is not defined properly" i.id_loc))
                                                    )
                              |Ptree.Tint -> Ttree.Tint

  in
  
  let rec type_expr (context : local_context) exp = match exp.expr_node with
    |Econst(a) when (Int32.to_int a = 0)-> {expr_node = Econst(a); expr_typ = Ttypenull}
    |Econst(a)-> {expr_node = Econst(a);
                  expr_typ = Tint}
    |Eunop(b, e) ->
      let ep = type_expr context e in
      (match b, ep.expr_typ with
       |Unot, _ -> {expr_node = Eunop(Unot, ep);
                    expr_typ = Tint}
       |Uminus, t when (eq_type t Tint) -> {expr_node = Eunop(Uminus, ep);
                        expr_typ = Tint}
       |_, _ -> raise (Error(error_message "This Unary operator was called by an idiot, you suck" e.expr_loc)))

       |Ebinop(b, e1, e2) ->
      let e1p = type_expr context e1 and e2p = type_expr context e2 in
      (match b, e1p.expr_typ, e2p.expr_typ with
       (*Operations logiques : AND OR*)
      |Band, _, _ -> {expr_node = Ebinop(Band, e1p, e2p);
                            expr_typ = Tint }
      |Bor, _, _ -> {expr_node = Ebinop(Bor, e1p, e2p);
                            expr_typ = Tint }
      (*Operation + - / * *)
      |a, t2, t1 when ((a == Badd) || (a == Bsub) || (a == Bmul) || (a == Bdiv)) && (is_int t1) && (is_int t2)  -> {expr_node = Ebinop(a, e1p, e2p);
                            expr_typ = Tint}
      |a, _, _ when ((a == Badd) || (a == Bsub) || (a == Bmul) || (a == Bdiv)) -> raise (Error(error_message "Typing was wrong, expected Int with operand" exp.expr_loc))
      (* Operation == != < <= > >= *)
      |a, t1, t2 when (eq_type t1 t2) -> {expr_node = Ebinop(a, e1p, e2p);
                                     expr_typ = Tint}
      |_, _, _ -> raise (Error(error_message "This expression is non-sensical, go back to primary school, nerd" exp.expr_loc))
      )
       |Eright(lv) ->
         (match lv with
          |Lident(i) ->
            (*Check if i is an identifier that exists, that is if lvalue(exp) is true in local context*)
            let t = (try typ_context context i
                     with Error(s) -> raise (Error(error_message s exp.expr_loc)))
            in
            {expr_node = Eaccess_local(i.id);
             expr_typ = t}
          |Larrow(e, i) -> failwith "go back here!"
        (*    let ep = type_expr context e in
            {expr_node = Eaccess_field(ep, {field_name : i.id;
                                            field_typ : ep.typ});
             expr_typ = ep.typ}*)
         )
       |Eassign(v, e1) ->
         let e1p = type_expr context e1 in
         (match v with
          |Lident(i) -> 
            (*checks if the variable has been defined, fails otherwise*)
            let t = (try typ_context context i
                     with Error(s) -> raise (Error(error_message s exp.expr_loc)))
            in
            (*checks if the declaration type matches the expression type, fails otherwise*)
            if(eq_type e1p.expr_typ t)
            then ({expr_node = Eassign_local(i.id, e1p);
                   expr_typ = e1p.expr_typ})
            else raise (Error(error_message "Type are unmatched in affectation" exp.expr_loc))
          |Larrow(e2, i) -> failwith "Strutcs aren't implemented yet, can't assign to a field"
         )

       |Ecall(i, l) ->
         let (args, ret_typ) = (try (Hashtbl.find function_table i.id)
                                with Not_found -> raise (Error(error_message "Function unknown" exp.expr_loc))) in
         let compare b ep dv = match b, ep.expr_typ, dv with
           |false, _, _ -> false
           |_,t0,(t1,i) -> (eq_type t0 t1)
         in
         let lp = List.map (type_expr context)l in
         let test = (try List.fold_left2 compare true lp args
                     with Invalid_argument(_) -> raise (Error(error_message "Number of Arguments do not match declaration" exp.expr_loc))) in
         if(test) then {expr_node = Ecall(i.id, lp);
                        expr_typ = ret_typ}
         else raise (Error(error_message "Function was used with the wrong types" exp.expr_loc))

       |Esizeof(i) ->
         let s = (try Hashtbl.find struct_table (i.id)
                  with Not_found -> raise (Error(error_message "The struct used is unbound" exp.expr_loc))) in
         {expr_node = Esizeof(s);
         expr_typ = Tint}
       in

       let rec type_stmt context st = match st.stmt_node with
       |Sskip -> Ttree.Sskip
       |Sexpr(e) -> (try Sexpr(type_expr context e)
                     with Error(s) -> raise (Error(error_message s st.stmt_loc)))
       |Sif(e, s1, s2) ->
         let ep = (try type_expr context e
                   with Error(s) -> raise (Error(error_message s st.stmt_loc)))
         and st1p = (try type_stmt context s1
                     with Error (s) -> raise (Error(error_message s st.stmt_loc)))
         and st2p = (try type_stmt context s2
                     with Error (s) -> raise (Error(error_message s st.stmt_loc))) in
         Sif(ep, st1p, st2p)
       |Swhile(e, s) ->
           let ep = (try type_expr context e
                     with Error(se) -> raise (Error(error_message se st.stmt_loc)))
           and stp = (try type_stmt context s
                      with Error (se) -> raise (Error(error_message se st.stmt_loc))) in
           Swhile(ep, stp)
       |Sblock(b) -> (try Sblock(type_block (Some(context)) b)
                      with Error(s) -> raise (Error(error_message s st.stmt_loc)))
       |Sreturn(e) -> (try Sreturn(type_expr context e)
                       with Error(s) -> raise (Error(error_message s st.stmt_loc)))


       and type_block (context_opt:Ttree.local_context option) ((dvl, stl):Ptree.block) =
         (*Create a context either empty or inheriting definitions from the super block*)
         let context = create_local_context context_opt in
         let process_one_variable = function
           |(t, i) -> (define_var context (t, i); (*the variable is added to the context*)
                      (convert_type t, i.id)) (*and transformed into a ttree.declvar*)
         in
         let process_one_instruction s = type_stmt context s in
         (List.map process_one_variable dvl, List.map process_one_instruction stl)
       in

       let type_struct = function
         |Dstruct i, dvl ->
           ( match Hashtbl.find_opt (struct_table) (i.id) with
             |Some _ -> raise (Error (error_message "Structure is already declared, double declaration is forbidden" i.id_loc))
             |None   -> let t = Hashtbl.create 32 in
                        let f_aux ty,ip =
                          Hashtbl.add t ip.id { field_name = ip.id ;
                                                field_type = convert_type ty }
                        in
                        List.iter f_aux dvl;
                        Hashtbl.add struct_table i.id { str_name   = i.id ;
                                                        str_fields = t }
           )
         |_ -> failwith "Should be some dead code"
       in
       let type_fun = function
         |Dfun df -> (*args, typret *)
           let block_context = create_local_context None
           in
           let f_aux (t, i) =
             define_var block_context (t, i);
             (convert_type t, i.id)
           in
           let l=List.map f_aux df.fun_formals and ty = convert_type df.fun_typ in
           (match Hashtbl.find_opt function_table df.fun_name.id with
            |None   -> Hashtbl.add function_table df.fun_name.id (l, ty)
            |Some _ -> raise(Error(error_message "Function is already defined" df.fun_name.id_loc))
           );
           { fun_typ     = ty ;
             fun_name    = df.fun_name.id ;
             fun_formals = l ;
             fun_body    = type_block (Some(block_context)) (df.fun_body) }
         |_-> failwith "Should be some dead code"
       in
       let type_file f =
         let rec f_aux acc1 acc2 = function
           |[]             -> List.rev acc1, List.rev acc2
           |Dfun(df)::q    -> f_aux (Dfun(df)::acc1) acc2 q
           |Dstruct(ds)::q -> f_aux acc1 (Dstruct(ds)::acc2) q
         in
         let funs,structs = f_aux [] [] f in
         List.iter type_struct structs;
         List.map type_fun funs
       in

       
      ;;

