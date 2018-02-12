open Ttree;;
open Rtltree;;

let deffun (df: decl_fun) =
  let var_tbl = Hashtbl.create 32 in
  let add_var (t,id) =
    let r = Register.fresh () in
    Hashtbl.add var_tbl id r;
    r
  in
  let graph = ref Label.M.empty in
  let generate i =
    let l = Label.fresh () in
    graph := Label.M.add l i !graph;
    l
  in

  let rec expr e destr destl =
    match e.expr_node with
    |Econst i -> Econst (i,destr,destl)
    |Eaccess_local id -> let reg_v = Hashtbl.find var_tbl id in
                         Embinop(Mmov, reg_v, destr, destl)
    |Eaccess_field (e0,f) -> failwith "not implemented"
    |Eassign_local (id,e0) -> let reg = Register.fresh () in
                              let reg_v = Hashtbl.find var_tbl id in
                              let lbl = generate(Embinop(Mmov, reg, reg_v, destl)) in
                              let lbl_e0 = generate(expr e0 reg lbl) in
                              Embinop(Mmov, reg, destr, lbl_e0)
    |Eassign_field (e1,f,e2) -> failwith "not implemented"
    |Eunop (u,e0) -> (match u with
                      |Uminus -> let reg2 = Register.fresh () in
                                 let lbl = generate (Embinop(Msub, reg2, destr, destl)) in
                                 let lbl2 = generate(expr e0 reg2 lbl) in
                                 Econst(Int32.zero,destr, lbl2)
                      |Unot -> failwith "not implemented")
    |Ebinop (b,e1,e2) -> let reg2 = Register.fresh () in
                         (match b with
                          |Badd -> let lbl = generate (Embinop(Madd,reg2,destr,destl)) in
                                   let lbl2 = generate (expr e2 reg2 lbl) in
                                   expr e1 destr lbl2
                          |Bsub -> let lbl = generate (Embinop(Msub,reg2,destr,destl)) in
                                   let lbl2 = generate (expr e2 reg2 lbl) in
                                   expr e1 destr lbl2
                          |Bmul -> let lbl = generate (Embinop(Mmul,reg2,destr,destl)) in
                                   let lbl2 = generate (expr e2 reg2 lbl) in
                                   expr e1 destr lbl2
                          |Bdiv -> let lbl = generate (Embinop(Mdiv,reg2,destr,destl)) in
                                   let lbl2 = generate (expr e2 reg2 lbl) in
                                   expr e1 destr lbl2    
                          |_ -> failwith "not implemented")
    |Ecall (id,el) -> failwith "not implemented"
    |Esizeof s -> failwith "not implemented"
  in

  let rec stmt s destl retr exitl =
    match s with
    |Sskip -> failwith "not implemented" 
    |Sexpr e -> failwith "not implemented"
    |Sif (e,s1,s2) -> failwith "not implemented"
    |Swhile (e,s0) -> failwith "not implemented"
    |Sblock b -> failwith "not implemented"
    |Sreturn e -> expr e retr exitl
  in

  let make_bdy (dvl,stl) rt_reg lbl =
    let __fold_fun st l =
      generate (stmt st l rt_reg lbl)
    in
    List.fold_right __fold_fun stl lbl
  in

  let make_dvl (dvl,stl) =
    Register.set_of_list (List.map add_var dvl)
  in
  let args_list = []
  and exit_reg = Register.fresh ()
  and exit_lbl = Label.fresh ()
  and fun_loc = make_dvl (df.fun_body)
  in
  let entry_lbl = make_bdy (df.fun_body) exit_reg exit_lbl in
    { fun_name    = df.fun_name ;
      fun_formals = args_list;
      fun_result  = exit_reg ;
      fun_locals  = fun_loc ;
      fun_entry   = entry_lbl ;
      fun_exit    = exit_lbl ;
      fun_body    = !graph }
;;

let program (f: Ttree.file) =
  { funs = List.map deffun f.funs };;
    
