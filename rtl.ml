open Ttree;;
open Rtltree;;



let struct_tbl = Hashtbl.create 32;;

let rec is_pure expr = match expr.expr_node with
  |Econst(i) -> true
  |Eaccess_local(id) -> true
  |Eaccess_field(e,f) -> is_pure e
  |Eassign_field(e1, f, e2) -> false
  |Eassign_local(id, e) -> false
  |Eunop(op, e) -> is_pure e
  |Ebinop(op, e1, e2) -> (is_pure e1) && (is_pure e2)
  |Ecall(i, el) -> false
  |Esizeof(s) -> true


let lt a b = if Int32.compare a b < 0 then {expr_node = Econst(Int32.one); expr_typ = Tint} else  {expr_node = Econst(Int32.zero); expr_typ = Tint};;
let le a b = if Int32.compare a b <= 0 then {expr_node = Econst(Int32.one); expr_typ = Tint} else  {expr_node = Econst(Int32.zero); expr_typ = Tint};;

let gt a b = if Int32.compare a b > 0 then {expr_node = Econst(Int32.one); expr_typ = Tint} else  {expr_node = Econst(Int32.zero); expr_typ = Tint};;
let ge a b = if Int32.compare a b >= 0 then {expr_node = Econst(Int32.one); expr_typ = Tint} else  {expr_node = Econst(Int32.zero); expr_typ = Tint};;

(*

let fact_eq e (op : Ttree.binop) e11 e12 e21 e22 = match op with
  |Badd->
    (match e11.expr_node, e12.expr_node, e21.expr_node, e22.expr_node with
     |_,Econst(n1), _, Econst(n2) when n1 = n2 -> {expr_node = Ebinop(Beq, e11, e21);
                                                   expr_typ = Tint}
     |_,Econst(n1),Econst(n2),_ when n1 = n2 ->  {expr_node = Ebinop(Beq, e11, e22);
                                                   expr_typ = Tint}
     |Econst(n1),_,Econst(n2),_ when n1 = n2 ->  {expr_node = Ebinop(Beq, e12, e22);
                                                   expr_typ = Tint}
     |Econst(n1),_,_,Econst(n2) when n1 = n2 ->  {expr_node = Ebinop(Beq, e11, e21);
                                                   expr_typ = Tint}
     |_,_,_,_ -> e
    )
  |Bsub ->
    (match e11.expr_node, e12.expr_node, e21.expr_node, e22.expr_node with
     |_,Econst(n1), _, Econst(n2) when n1 = n2 -> {expr_node = Ebinop(Beq, e11, e21);
                                                   expr_typ = Tint}
     |Econst(n1),_,Econst(n2),_ when n1 = n2 ->  {expr_node = Ebinop(Beq, e12, e22);
                                                  expr_typ = Tint}
     |_,_,_,_ -> e
    )
  |_ -> e
;;
let fact_neq e op e11 e12 e21 e22 = match op with
  |Bmul | Badd->
    (match e11.expr_node, e12.expr_node, e21.expr_node, e22.expr_node with
     |_,Econst(n1), _, Econst(n2) when n1 = n2 -> {expr_node = Ebinop(Bneq, e11, e21);
                                                   expr_typ = Tint}
     |_,Econst(n1),Econst(n2),_ when n1 = n2 ->  {expr_node = Ebinop(Bneq, e11, e22);
                                                   expr_typ = Tint}
     |Econst(n1),_,Econst(n2),_ when n1 = n2 ->  {expr_node = Ebinop(Bneq, e12, e22);
                                                   expr_typ = Tint}
     |Econst(n1),_,_,Econst(n2) when n1 = n2 ->  {expr_node = Ebinop(Bneq, e11, e21);
                                                   expr_typ = Tint}
     |_,_,_,_ -> e
    )
  |Bsub ->
    (match e11.expr_node, e12.expr_node, e21.expr_node, e22.expr_node with
     |_,Econst(n1), _, Econst(n2) when n1 = n2 -> {expr_node = Ebinop(Bneq, e11, e21);
                                                   expr_typ = Tint}
     |Econst(n1),_,Econst(n2),_ when n1 = n2 ->  {expr_node = Ebinop(Bneq, e12, e22);
                                                  expr_typ = Tint}
     |_,_,_,_ -> e
    )
  |_ -> e
;;
 *)
let mk_not (e:Ttree.expr) = match e.expr_node with
  |Ttree.Econst(n) when (n = Int32.zero) -> {expr_node = Ttree.Econst(Int32.one);
                                             expr_typ = Tint}
  |Econst(n) -> {expr_node = Ttree.Econst(Int32.zero);
                 expr_typ = Tint}
  |_ -> {expr_node = Eunop(Unot, e) ; expr_typ = Tint}

and mk_minus e = match e.expr_node with
  |Ttree.Econst(n) when (n = Int32.zero) -> {expr_node = Ttree.Econst(Int32.zero);
                                             expr_typ = Tint}
  |Econst(n) -> {expr_node = Econst(Int32.mul Int32.minus_one n);
                 expr_typ = Tint}

  |_ ->  {expr_node = Eunop(Uminus, e) ; expr_typ = Tint}
;;

let mk_add e1 e2 = match e1.expr_node, e2.expr_node with
  |Ttree.Econst(t), _ when t=Int32.zero -> e2
  |_, Ttree.Econst(t) when t=Int32.zero -> e1
  |Econst(n1), Econst(n2) -> {expr_node = Ttree.Econst(Int32.add n1 n2);
                              expr_typ = Tint}
  |_, _ -> {expr_node = Ttree.Ebinop(Badd, e1, e2);
            expr_typ = Tint}
and mk_sub e1 e2 = match e1.expr_node, e2.expr_node with
  |_, Ttree.Econst(t) when t=Int32.zero -> e1
  |Ttree.Econst(t), _ when t=Int32.zero -> {expr_node = Eunop(Uminus, e2);
                                            expr_typ = Tint}
  |Ttree.Econst(n1), Econst(n2) -> {expr_node = Ttree.Econst(Int32.sub n1 n2);
                                    expr_typ = Tint}
  |_, _ -> {expr_node = Ebinop(Bsub, e1, e2);
            expr_typ = Tint}

and mk_div e1 e2 = match e1.expr_node, e2.expr_node with
  |_, Ttree.Econst(t) when t=Int32.one -> e1
  |Ttree.Econst(n1), Ttree.Econst(n2) -> {expr_node = Ttree.Econst(Int32.div n1 n2);
                                          expr_typ = Tint}
   |Econst(t), _ when (t=Int32.zero && is_pure e2) -> {expr_node = Econst(Int32.zero);
                                                      expr_typ = Tint}
  |_, _ -> {expr_node = Ebinop(Bdiv, e1, e2);
            expr_typ = Tint}

and mk_mul e1 e2 = match e1.expr_node, e2.expr_node with
  |_, Econst(t) when t=Int32.one -> e1
  |Econst(t),_ when t=Int32.one -> e2
  |_, Econst(t) when (t=Int32.zero && is_pure e1) -> {expr_node = Econst(Int32.zero);
                                                      expr_typ = Tint}
  |Econst(t), _ when (t=Int32.zero && is_pure e2) -> {expr_node = Econst(Int32.zero);
                                                      expr_typ = Tint} 
  |Econst(t),_ when t=Int32.one -> e2
  |Econst(n1), Econst(n2) -> {expr_node = Econst(Int32.mul n1 n2);
                              expr_typ = Tint}
  |_, _ -> {expr_node = Ebinop(Bmul, e1, e2);
            expr_typ = Tint}

and mk_eq e1 e2 = match e1.expr_node, e2.expr_node with
  |Ttree.Econst(n1), Econst(n2) when n1 = n2 -> {expr_node = Econst(Int32.one);
                                                 expr_typ = Tint}
  |Econst(n1), Econst(n2) -> {expr_node = Econst(Int32.zero); expr_typ = Tint}
  (*|Ebinop(op1, e11, e12), Ebinop(op2, e21, e22) when (op1 = op2)-> fact_eq e op e11 e12 e21 e22 *)
  |_, _ -> {expr_node = Ebinop(Beq, e1, e2); expr_typ = Tint}

and mk_neq e1 e2 = match e1.expr_node, e2.expr_node with
  |Econst(n1), Econst(n2) when n1 = n2 -> {expr_node = Econst(Int32.zero); expr_typ = Tint}
  |Econst(n1), Econst(n2) -> {expr_node = Econst(Int32.one); expr_typ = Tint}
 (* |Ebinop(op1, e11, e12), Ebinop(op2, e21, e22) when (op1 = op2)-> fact_neq e op e11 e12 e21 e22 *)
  |_, _ -> {expr_node = Ebinop(Bneq, e1, e2); expr_typ = Tint}

and mk_lt e1 e2 = match e1.expr_node, e2.expr_node with 
  |Econst(n1), Econst(n2) -> lt n1 n2
  |_, _ -> {expr_node = Ebinop(Blt, e1, e2); expr_typ = Tint}

and mk_le e1 e2 = match e1.expr_node, e2.expr_node with 
  |Econst(n1), Econst(n2) -> le n1 n2
  |_, _ -> {expr_node = Ebinop(Ble, e1, e2); expr_typ = Tint}

and mk_ge e1 e2 = match e1.expr_node, e2.expr_node with 
  |Econst(n1), Econst(n2) -> ge n1 n2
  |_, _ -> {expr_node = Ebinop(Bge, e1, e2); expr_typ = Tint}

and mk_gt e1 e2 = match e1.expr_node, e2.expr_node with
  |Econst(n1), Econst(n2) -> gt n1 n2
  |_, _ -> {expr_node = Ebinop(Bgt, e1, e2); expr_typ = Tint}

and mk_and e1 e2 = match e1.expr_node, e2.expr_node with 
  |Econst(t), _ when t = Int32.zero -> {expr_node = Econst(Int32.zero); 
                                        expr_typ = Tint}
  |_, Econst(t) when (t = Int32.zero && is_pure e1)-> {expr_node = Econst(Int32.zero);
                                        expr_typ = Tint}
  |Econst(_), Econst(r) when r = Int32.zero -> {expr_node = Econst(Int32.zero);
                                                expr_typ = Tint}
  |Econst(_), Econst(_) -> {expr_node = Econst(Int32.one); 
                                        expr_typ = Tint}
  |_,_ -> {expr_node = Ebinop(Band, e1, e2); expr_typ = Tint}



and mk_or e1 e2 = match e1.expr_node, e2.expr_node with 
  |Econst(r), Econst(t) -> 
    let n = if (Int32.logor r t) = Int32.zero then Int32.zero else Int32.one in 
    {expr_node = Econst(n);
     expr_typ = Tint}
  |Econst(r), _ when r != Int32.zero -> {expr_node = Econst(Int32.one);  expr_typ = Tint}
  |_, Econst(r) when (r != Int32.zero && is_pure e1) -> {expr_node = Econst(Int32.one);  expr_typ = Tint}
  |_, _ -> {expr_node = Ebinop(Bor, e1, e2); expr_typ = Tint}
;;

let rec sel_i e = match e.expr_node with
  |Econst i -> {expr_node = Econst i;
                expr_typ = e.expr_typ}
  |Eaccess_local id -> {expr_node = Eaccess_local id;
                        expr_typ = e.expr_typ}
  |Eaccess_field (e0,f) -> {expr_node = Eaccess_field(sel_i e0, f);
                            expr_typ = e.expr_typ}
  |Eassign_local (id,e0) -> {expr_node = Eassign_local(id, sel_i e0);
                             expr_typ = e.expr_typ}
  |Eassign_field (e1,f,e2) -> {expr_node = Eassign_field(sel_i e1, f, sel_i e2);
                               expr_typ = e.expr_typ}
  |Eunop (u,e0) ->
    let e = sel_i e0 in
    (match u with
     |Unot -> mk_not e
     |Uminus -> mk_minus e
    )
  |Ebinop (b,e1,e2) ->
    let e1p = sel_i e1
    and e2p = sel_i e2 in
    (match b with
     |Badd -> mk_add (e1p) (e2p)
     |Bsub -> mk_sub (e1p) (e2p)
     |Bdiv -> mk_div (e1p) (e2p)
     |Bmul -> mk_mul (e1p) (e2p)
     |Beq -> mk_eq (e1p) (e2p)
     |Bneq -> mk_neq (e1p) (e2p)
     |Blt -> mk_lt e1p e2p
     |Ble -> mk_le e1p e2p
     |Bgt -> mk_gt e1p e2p
     |Bge -> mk_ge e1p e2p
     |Band -> mk_and e1p e2p
     |Bor -> mk_or e1p e2p
    )
  |Ecall (id,el) -> {expr_node = Ecall(id, List.map sel_i el);
                     expr_typ = e.expr_typ}
  |Esizeof s -> {expr_node = Esizeof s;
                 expr_typ = e.expr_typ}
and sel_i_stmt = function
  | Sskip -> Sskip
  | Sexpr(e) -> Sexpr(sel_i e)
  | Sif(e, s1, s2) ->
     let ep = sel_i e in
     (match ep.expr_node with
      |Econst(t) when t = Int32.zero -> sel_i_stmt s2
      |Econst(t) -> sel_i_stmt s1
      |_ -> Sif(ep, s1, s2)
     )
  | Swhile(e, s) -> Swhile(sel_i e, s)
  | Sblock(dvl, sl) -> Sblock(dvl, List.map sel_i_stmt sl)
  | Sreturn(e) -> Sreturn(sel_i e)
;;


let deffun (df: decl_fun) =
  let stream = Stream.from (fun i -> Some(i+1))  in
  let get_block_key () = Stream.next stream in
  let block_tbl = Hashtbl.create 32 in
  let current_keys = ref [] in
  let set_vars = ref Register.S.empty in

  let store_new_register () =
    let r = Register.fresh () in
    set_vars:=Register.S.add r !set_vars;
    r
  in
  let new_register () = Register.fresh ()
  in

  let var_tbl = Hashtbl.create 32 in
  let find_register id =
  let rec find_register_aux = function
    |[] -> Hashtbl.find var_tbl id;
    |i::tl -> let tbl = Hashtbl.find block_tbl i in
              (try (Hashtbl.find tbl id)
               with Not_found -> find_register_aux tl) 
  in
  find_register_aux (!current_keys)
  in

  let add_var (t,id) =
    Hashtbl.add var_tbl id (store_new_register ())
  in
  let graph = ref Label.M.empty in
  let generate i =
    let l = Label.fresh () in
    graph := Label.M.add l i !graph;
    l
  in

  let rec expr e destr destl =
    let esp = (sel_i e) in
    match esp.expr_node with
    |Ttree.Econst i -> generate(Econst(i,destr,destl))
    |Eaccess_local id -> let reg_v = find_register id in
                         generate (Embinop(Mmov, reg_v, destr, destl))
    |Eaccess_field (e0,f) ->
      let reg = new_register () in
      let s = (match e0.expr_typ with
               |Tstructp(p) -> p
               |_ ->failwith "Should be some dead code")
      in
      let field_tbl = Hashtbl.find struct_tbl s.str_name in
      let p = Hashtbl.find field_tbl f.field_name in
      let lbl = generate(Eload(reg, p * 8, destr, destl)) in
      expr e0 reg lbl
    |Eassign_local (id,e0) -> let reg = new_register () in
                              let reg_v = find_register id in
                              let lbl_access = generate(Embinop(Mmov, reg, destr, destl)) in
                              let lbl = generate(Embinop(Mmov, reg, reg_v, lbl_access)) in
                              expr e0 reg lbl
    |Eassign_field (e1,f,e2) -> let s = (match e1.expr_typ with
                                         |Tstructp(p) -> p
                                         |_->failwith "Should be some dead code")
                                in
                                let field_tbl = Hashtbl.find struct_tbl s.str_name in
                                let p = Hashtbl.find field_tbl f.field_name in
                                let reg1 = new_register () in
                                let reg2 = new_register () in
                                let lbl = generate(Embinop(Mmov, reg2, destr, destl)) in
                                let lbl1 = generate(Estore(reg2, reg1, p * 8, lbl)) in
                                let lbl2 = expr e1 reg1 lbl1 in
                                expr e2 reg2 lbl2
    |Eunop (u,e0) -> (match u with
                      |Uminus -> let reg = new_register () in
                                 let lbl = generate (Embinop(Msub, reg, destr, destl)) in
                                 let lbl2 = expr e0 reg lbl in
                                 generate (Econst(Int32.zero,destr, lbl2))
                      |Unot ->   let lbl = generate (Emunop(Msetei(Int32.zero), destr, destl)) in
                                 expr e0 destr lbl)
    |Ebinop (b,e1,e2) -> let reg2 = new_register () in
                         (match b with
                          |Badd ->
                            (match e1.expr_node, e2.expr_node with
                             |Econst(n), _ ->
                               let lbl = generate (Emunop(Maddi(n), destr, destl)) in
                               expr e2 destr lbl
                             |_, Econst(n) ->
                               let lbl = generate (Emunop(Maddi(n), destr, destl)) in
                               expr e1 destr lbl
                             |_, _->
                               let lbl = generate (Embinop(Madd,reg2,destr,destl)) in
                               let lbl2 = expr e2 reg2 lbl in
                               expr e1 destr lbl2)
                          |Bsub ->
                            (match e1.expr_node, e2.expr_node with
                             |_, Econst(n) ->
                               let reg2 = new_register () in
                               let lbl = generate (Emunop(Maddi(Int32.mul Int32.minus_one n), destr, destl)) in
                               expr e1 destr lbl
                             |_, _->let lbl = generate (Embinop(Msub,reg2,destr,destl)) in
                                    let lbl2 = expr e2 reg2 lbl in
                                    expr e1 destr lbl2)
                          |Bmul -> let lbl = generate (Embinop(Mmul,reg2,destr,destl)) in
                                   let lbl2 = expr e2 reg2 lbl in
                                   expr e1 destr lbl2
                          |Bdiv -> let lbl = generate (Embinop(Mdiv,reg2,destr,destl)) in
                                   let lbl2 = expr e2 reg2 lbl in
                                   expr e1 destr lbl2
                          |Beq -> let lbl = generate (Embinop(Msete,reg2,destr,destl)) in
                                   let lbl2 = expr e2 reg2 lbl in
                                   expr e1 destr lbl2
                          |Bneq -> let lbl = generate (Embinop(Msetne,reg2,destr,destl)) in
                                   let lbl2 = expr e2 reg2 lbl in
                                   expr e1 destr lbl2
                          |Blt -> let lbl = generate (Embinop(Msetl,reg2,destr,destl)) in
                                   let lbl2 = expr e2 reg2 lbl in
                                   expr e1 destr lbl2
                          |Ble -> let lbl = generate (Embinop(Msetle,reg2,destr,destl)) in
                                   let lbl2 = expr e2 reg2 lbl in
                                   expr e1 destr lbl2
                          |Bgt -> let lbl = generate (Embinop(Msetg,reg2,destr,destl)) in
                                   let lbl2 = expr e2 reg2 lbl in
                                   expr e1 destr lbl2
                          |Bge -> let lbl = generate (Embinop(Msetge,reg2,destr,destl)) in
                                   let lbl2 = expr e2 reg2 lbl in
                                   expr e1 destr lbl2
                          |Band | Bor -> let lbl1 = generate(Econst((Int32.of_int 1), destr, destl))
                                       and lbl0 = generate(Econst(Int32.zero, destr, destl))
                                       in
                                       rtlc e lbl1 lbl0)
    |Ecall (id,el) -> let args_to_regs list_args =
                        let rec __aux acc = function
                          |[]   -> acc
                          |t::q -> __aux ((new_register ())::acc) q
                        in
                        __aux [] list_args
                      in
                      (*let eval_args e r lbl =*)
                      let eval_args lbl e r =
                        expr e r lbl
                      in
                      let list_regs = args_to_regs el in
                      let lbl = generate(Ecall(destr, id, list_regs, destl)) in
                      (*List.fold_right2 eval_args el list_regs lbl*)
                      List.fold_left2 eval_args lbl el list_regs
    |Esizeof s ->
      let p = ref 0 in
      let tbl = Hashtbl.find struct_tbl s.str_name in
      Hashtbl.iter (fun a b -> p := !p + 1;) tbl;
      generate (Econst(Int32.of_int (!p * 8), destr, destl))
  and (*in
  let rec *)rtlc exp lt lf =
    match exp.expr_node with
    |Ebinop(b,e1,e2)-> (match b with
                        |Band -> rtlc e1 (rtlc e2 lt lf) lf
                        |Bor -> rtlc e1 lt (rtlc e2 lt lf)
                        |Ble -> let reg1 = new_register () in
                                let reg2 = new_register () in
                                let lbl = generate (Embbranch(Mjle, reg2, reg1, lt, lf)) in
                                let lbl2 = expr e2 reg2 lbl in
                                expr e1 reg1 lbl2
                        |Blt -> let reg1 = new_register () in
                                let reg2 = new_register () in
                                let lbl = generate (Embbranch(Mjl, reg2, reg1, lt, lf)) in
                                let lbl2 = expr e2 reg2 lbl in
                                expr e1 reg1 lbl2
                        |Bge -> let reg1 = new_register () in
                                let reg2 = new_register () in
                                let lbl = generate (Embbranch(Mjl, reg2, reg1, lf, lt)) in
                                let lbl2 = expr e2 reg2 lbl in
                                expr e1 reg1 lbl2
                        |Bgt -> let reg1 = new_register () in
                                let reg2 = new_register () in
                                let lbl = generate (Embbranch(Mjle, reg2, reg1, lf, lt)) in
                                let lbl2 = expr e2 reg2 lbl in
                                expr e1 reg1 lbl2
                        |_ -> let reg = new_register () in
                              let lbl = generate (Emubranch(Mjz, reg, lf, lt)) in
                              expr exp reg lbl )
    |Eunop(u,e0)-> (match u with
                    |Unot-> rtlc e0 lf lt
                    |_-> let reg = new_register () in
                         let lbl = generate (Emubranch(Mjz, reg, lf, lt)) in
                         expr exp reg lbl )
    |_ -> let reg = new_register () in
          let lbl = generate (Emubranch(Mjz, reg, lf, lt)) in
          expr exp reg lbl
  in
  let rec make_bdy_block (dvl, stl) key lbl rt_reg exit_lbl =
    current_keys := key::!current_keys;
    let __fold_fun l st =
      stmt st l rt_reg exit_lbl
    in
    List.fold_left __fold_fun lbl (List.rev stl)

  and make_dvl_block (dvl,stl) key =
    let local_vars = Hashtbl.create 32 in
    Hashtbl.add block_tbl key local_vars;
    let __aux (t,id) =
      let reg = store_new_register () in
      Hashtbl.add local_vars id reg;
      id
    in
    List.rev_map __aux dvl
  and stmt s destl retr exitl =
    match (sel_i_stmt s) with
    |Sskip -> destl
    |Sexpr e -> expr e retr destl
    |Sif (e,s1,s2) -> let tr_lbl = stmt s1 destl retr exitl
                      and fs_lbl = stmt s2 destl retr exitl
                      in rtlc e tr_lbl fs_lbl
    |Swhile (e,s0) -> let lbl_goto = Label.fresh () in
                      let bdy_lbl = stmt s0 lbl_goto retr exitl in
                      let lbl = rtlc e bdy_lbl destl in
                      graph := Label.M.add lbl_goto (Egoto(lbl)) !graph;
                      lbl
    |Sblock b ->
      let i = get_block_key () in
      let _ = make_dvl_block b i in
      let mem_key = !current_keys in
      let new_label = make_bdy_block b i destl retr exitl in
      current_keys := mem_key;
      new_label
    |Sreturn e -> expr e retr exitl
  in

  let make_bdy (dvl,stl) rt_reg lbl =
    let __fold_fun l st =
      stmt st l rt_reg lbl
    in
    List.fold_left __fold_fun lbl (List.rev stl)
  in

  let make_dvl (dvl,stl) =
    List.iter add_var dvl
  in
  let args_aux (typ, id) =
    let r = Register.fresh () in
    Hashtbl.add var_tbl id r;
    r
  in
  let args_list = List.map args_aux df.fun_formals
  and exit_reg = Register.fresh ()
  and exit_lbl = Label.fresh ()
  in
  make_dvl (df.fun_body);
  let entry_lbl = make_bdy (df.fun_body) exit_reg exit_lbl in
    { fun_name    = df.fun_name ;
      fun_formals = args_list;
      fun_result  = exit_reg ;
      fun_locals  = !set_vars ;
      fun_entry   = entry_lbl ;
      fun_exit    = exit_lbl ;
      fun_body    = !graph }
;;

let program (f: Ttree.file) =
    let add_struct i s =
      let c = ref 0 in
      let field_tbl = Hashtbl.create 16 in
      Hashtbl.add struct_tbl s.str_name field_tbl;
      let aux id f =
        Hashtbl.add field_tbl f.field_name (!c);
        c := !c + 1;
      in
      Hashtbl.iter (aux) s.str_fields;
  in
  Hashtbl.iter add_struct f.structs;
  { funs = (List.map deffun ((f.funs))) };;
