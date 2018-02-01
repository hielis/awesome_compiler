
open Ttree
open ptree.Ptree
(* utiliser cette exception pour signaler une erreur de typage *)
exception Error of string

let to_string (a : loc) = failwith "Implement me";;
let error_message a l = a ^ (to_string l);;

let eq_type tref = function |Ttypenull -> not (tref = Tvoid)
                            |Tvoid -> not (tref = Tint || tref = Ttypenull)
                            |Tint -> (tref = Ttypenull) || (tref = Tint)
                            |Tstructp(_) as a-> (a = tref) || (tref = Ttypenull);;
(*checking structure type is not safe yet*)

let is_int = eq_type Tint;;


let string_of_type = function
  | Tint       -> "int"
  | Tstructp x -> "struct " ^ x.str_name ^ " *"
  | Tvoidstar  -> "void*"
  | Ttypenull  -> "typenull"

let program p =
  let function_table = Hashtbl.create 64 in


  let rec type_expr exp = match exp.expr_node with
    |Econst(0) -> {expr_node : Econst(0);
                              expr_typ : Ttypenull}
    |Econst(a)-> {expr_node : Econst(a);
                  expr_typ : Tint}
    |Eunop(b, e) ->
      let ep = type_expr e in
      (match b, ep.expr_typ with
       |Unot, _ -> {expr_node : Eunop(Unot, ep);
                    expr_typ : Tint}
       |Uminus, t when (eq_type t Tint) -> {expr_node : Eunop(Uminus, ep);
                        expr_typ : Tint}
       |_, _ -> raise Error(error_message "This Unary operator was called by an idiot, you suck" e.expr_loc)

       |Ebinop(b, e1, e2) ->
      let e1p = type_expr e1 and e2p = type_expr e2 in
      (match b, e1p.expr_typ, e2p.expr_typ with
       (*Operations logiques : AND OR*)
      |Band, _, _ -> {expr_node : Ebinop(Band, e1p, e2p);
                            expr_typ : Tint }
      |Bor, _, _ -> {expr_node : Ebinop(Bor, e1p, e2p);
                            expr_typ : Tint }
      (*Operation + - / * *)
      |a, t2, t1 when ((a == Badd) || (a == Bsub) || (a == Bmul) || (a == Bdiv)) && (is_int t1) && (is_int t2)  -> {expr_node : Ebinop(a, e1p, e2p);
                            expr_typ : Tint}
      |a, _, _ when ((a == Badd) || (a == Bsub) || (a == Bmul) || (a == Bdiv)) -> raise Error(error_message "Typing was wrong, expected Int with operand" exp.expr_loc)
      (* Operation == != < <= > >= *)
      |a, t1, t2 when (eq_type t1 t2) -> {expr_node : Ebinop(a, e1p, e2p);
                                     expr_typ : Tint}
      |_, _, _ -> raise Error(error_message "This expression is non-sensical, go back to primary school, nerd" exp.expr_loc)
      )
    (*Reste Ecall, Esizeof, Eright, Eassign *)
       |Eright(lv) ->
         (match lv with
          |Lident(i) -> {expr_node : Eaccess_local(i.id);
                         expr_typ : Tvoidstar}
          |Larrow(e, i) -> let ep = type_expr e in
            {expr_node : Eaccess_field(ep, {field_name : i.id;
                                            field_typ : ep.typ});
             expr_typ : ep.typ}
         )
       |Eassign(v, e1) -> 
         let e1p = type_expr e1 in
         (match v with
          |Lident(i) -> {expr_node : Eassign_local(i.id, e1p);
                         expr_typ : e1p.expr_typ}
          |Larrow(e2, i) -> failwith "I do not understand"
         )

       |Ecall(i, l) -> 
         let (args, ret_typ) = (try (Hashtbl.find function_table i.id)
                                with Not_found -> raise Error(error_message "Function unknown" exp.expr_loc)) in
         let compare b ep dv = match b, ep.expr_typ, dv with
           |false, _, _ -> false
           |_,t0,(t1,i) -> (eq_type t0 t1)
         in
         let lp = List.map type_expr l in
         let test = (try List.fold_left2 compare lp args
                     with Invalid_argument -> raise Error(error_message "Number of Arguments do not match declaration" exp.expr_loc)) in
         if(test) then {expr_node : Ecall(i.id, lp);
                        expr_typ : ret_typ}
         else raise Error(error_message "Function was used with the wrong types" exp.expr_loc)
       |_ -> failwith  "Not finished"
       in
       ;;
