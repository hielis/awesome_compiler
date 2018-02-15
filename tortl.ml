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
    |Econst i -> generate(Econst (i,destr,destl))
    |Eaccess_local id -> let reg_v = Hashtbl.find var_tbl id in
                         generate (Embinop(Mmov, reg_v, destr, destl))
    |Eaccess_field (e0,f) -> failwith "not implemented"
    |Eassign_local (id,e0) -> let reg = Register.fresh () in
                              let reg_v = Hashtbl.find var_tbl id in
                              let lbl_access = generate(Embinop(Mmov, reg, destr, destl)) in
                              let lbl = generate(Embinop(Mmov, reg, reg_v, lbl_access)) in
                              (*let lbl_e0 = generate(expr e0 reg lbl) in
                              Embinop(Mmov, reg, destr, lbl_e0)*)
                              expr e0 reg lbl
    |Eassign_field (e1,f,e2) -> failwith "not implemented"
    |Eunop (u,e0) -> (match u with
                      |Uminus -> let reg2 = Register.fresh () in
                                 let lbl = generate (Embinop(Msub, reg2, destr, destl)) in
                                 let lbl2 = expr e0 reg2 lbl in
                                 generate (Econst(Int32.zero,destr, lbl2))
                      |Unot -> failwith "not implemented")
    |Ebinop (b,e1,e2) -> let reg2 = Register.fresh () in
                         (match b with
                          |Badd -> let lbl = generate (Embinop(Madd,reg2,destr,destl)) in
                                   let lbl2 = expr e2 reg2 lbl in
                                   expr e1 destr lbl2
                          |Bsub -> let lbl = generate (Embinop(Msub,reg2,destr,destl)) in
                                   let lbl2 = expr e2 reg2 lbl in
                                   expr e1 destr lbl2
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
                          |_ -> failwith "not implemented")
    |Ecall (id,el) -> failwith "not implemented"
    |Esizeof s -> failwith "not implemented"
  in

  let rec rtlc exp lt lf =
    match exp.expr_node with
    |Ebinop(b,e1,e2)-> (match b with
                        |Band -> rtlc e1 (rtlc e2 lt lf) lf
                        |Bor -> rtlc e1 lt (rtlc e2 lt lf)
                        |Ble -> let reg1 = Register.fresh () in
                                let reg2 = Register.fresh () in
                                let lbl = generate (Embbranch(Mjle, reg2, reg1, lt, lf)) in
                                let lbl2 = expr e2 reg2 lbl in
                                expr e1 reg1 lbl2
                        |Blt -> let reg1 = Register.fresh () in
                                let reg2 = Register.fresh () in
                                let lbl = generate (Embbranch(Mjl, reg2, reg1, lt, lf)) in
                                let lbl2 = expr e2 reg2 lbl in
                                expr e1 reg1 lbl2
                        |Bge -> let reg1 = Register.fresh () in
                                let reg2 = Register.fresh () in
                                let lbl = generate (Embbranch(Mjl, reg2, reg1, lf, lt)) in
                                let lbl2 = expr e2 reg2 lbl in
                                expr e1 reg1 lbl2
                        |Bgt -> let reg1 = Register.fresh () in
                                let reg2 = Register.fresh () in
                                let lbl = generate (Embbranch(Mjle, reg2, reg1, lf, lt)) in
                                let lbl2 = expr e2 reg2 lbl in
                                expr e1 reg1 lbl2
                        |_ -> let reg = Register.fresh () in
                              let lbl = generate (Emubranch(Mjz, reg, lf, lt)) in
                              expr exp reg lbl )
    |Eunop(u,e0)-> (match u with
                    |Unot-> rtlc e0 lf lt
                    |_-> let reg = Register.fresh () in
                         let lbl = generate (Emubranch(Mjz, reg, lf, lt)) in
                         expr exp reg lbl )
    |_ -> let reg = Register.fresh () in
          let lbl = generate (Emubranch(Mjz, reg, lf, lt)) in
          expr exp reg lbl 
  in
  let rec make_bdy_block (dvl, stl) lbl rt_reg exit_lbl =
    let __fold_fun st l =
      stmt st l rt_reg exit_lbl
    in
    List.fold_right __fold_fun stl lbl
  and

    make_dvl_block (dvl,stl) =
    (*let rec __aux = function
      |[]->()
      |(t,id)::q-> let r = Register.fresh () in
              Hashtbl.add var_tbl id r;
              __aux q
     in __aux dvl*)
    let __aux (t,id) =
      Hashtbl.add var_tbl id (Register.fresh ());
      id
    in
    List.rev_map __aux dvl

  and remove_var var_list =
    let __aux id =
      Hashtbl.remove var_tbl id;
    in
    List.iter __aux var_list
    
  and stmt s destl retr exitl =
    match s with
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
    |Sblock b -> let vl = make_dvl_block b in
                 let new_label = make_bdy_block b destl retr exitl in
                 remove_var vl; new_label
    |Sreturn e -> expr e retr exitl
  in

  let make_bdy (dvl,stl) rt_reg lbl =
    let __fold_fun st l =
      stmt st l rt_reg lbl
    in
    List.fold_right __fold_fun stl lbl
  in

  let make_dvl (dvl,stl) =
    Register.set_of_list (List.map add_var dvl)
  in
  let args_aux (typ, id) =
    add_var (typ, id)
  in
  let args_list = List.map args_aux df.fun_formals
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

