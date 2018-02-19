open Ttree;;
open Rtltree;;

let struct_tbl = Hashtbl.create 32;;

let deffun (df: decl_fun) =
  let stream = Stream.from (fun i -> Some(i+1))  in
  let get_block_key () = Stream.next stream in
  let block_tbl = Hashtbl.create 32 in
  let current_keys = ref [] in
  let set_vars = ref Register.S.empty in

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
    |Eaccess_local id -> let reg_v = find_register id in
                         generate (Embinop(Mmov, reg_v, destr, destl))
    |Eaccess_field (e0,f) ->
      let reg = Register.fresh() in
      let s = (match e0.expr_typ with
               |Tstructp(p) -> p
               |_ ->failwith "Should be some dead code")
      in
      let field_tbl = Hashtbl.find struct_tbl s.str_name in
      let p = Hashtbl.find field_tbl f.field_name in
      let lbl = generate(Eload(reg, p * 8, destr, destl)) in
      expr e0 reg lbl
    |Eassign_local (id,e0) -> let reg = Register.fresh () in
                              let reg_v = find_register id in
                              let lbl_access = generate(Embinop(Mmov, reg, destr, destl)) in
                              let lbl = generate(Embinop(Mmov, reg, reg_v, lbl_access)) in
                              expr e0 reg lbl
    |Eassign_field (e1,f,e2) ->
      let s = (match e1.expr_typ with
               |Tstructp(p) -> p
               |_->failwith "Should be some dead code")
      in
      let field_tbl = Hashtbl.find struct_tbl s.str_name in
      let p = Hashtbl.find field_tbl f.field_name in
      let reg1 = Register.fresh()
      and reg2 = Register.fresh() in
      let lbl = generate(Embinop(Mmov, reg2, destr, destl)) in
      let lbl1 = generate(Estore(reg2, reg1, p * 8, lbl)) in
      let lbl2 = expr e1 reg1 lbl1 in
      expr e2 reg2 lbl2
    |Eunop (u,e0) -> (match u with
                      |Uminus -> let reg2 = Register.fresh () in
                                 let lbl = generate (Embinop(Msub, reg2, destr, destl)) in
                                 let lbl2 = expr e0 reg2 lbl in
                                 generate (Econst(Int32.zero,destr, lbl2))
                      |Unot ->
                         let lbl = generate (Emunop(Msetei(Int32.zero), destr, destl)) in
                         expr e0 destr lbl)
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
                          |Band | Bor -> let lbl1 = generate(Econst((Int32.of_int 1), destr, destl))
                                       and lbl0 = generate(Econst(Int32.zero, destr, destl))
                                       in
                                       rtlc e lbl1 lbl0)
    |Ecall (id,el) ->
      let args_aux1 e =
        Register.fresh()
      in
      let args_aux e r lbl =
        expr e r lbl
      in
      let list_aux = List.map args_aux1 el in
      let lbl = generate(Ecall(destr, id, list_aux, destl)) in
      List.fold_right2 args_aux el list_aux lbl
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
  let rec make_bdy_block (dvl, stl) key lbl rt_reg exit_lbl =
    current_keys := key::!current_keys;
    let __fold_fun st l =
      stmt st l rt_reg exit_lbl
    in
    List.fold_right __fold_fun stl lbl

  and make_dvl_block (dvl,stl) key =
    let local_vars = Hashtbl.create 32 in
    Hashtbl.add block_tbl key local_vars;
    (*let rec __aux = function
      |[]->()
      |(t,id)::q-> let r = Register.fresh () in
              Hashtbl.add var_tbl id r;
              __aux q
     in __aux dvl*)
    let __aux (t,id) =
      let reg = Register.fresh () in
      Hashtbl.add local_vars id reg;
      set_vars := Register.S.add reg !set_vars;
      id
    in
    List.rev_map __aux dvl
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
    let __fold_fun st l =
      stmt st l rt_reg lbl
    in
    List.fold_right __fold_fun stl lbl
  in

  let make_dvl (dvl,stl) =
    set_vars := Register.set_of_list (List.map add_var dvl);
    !set_vars
  in
  let args_aux (typ, id) =
    add_var (typ, id)
  in
  let args_list = List.map args_aux df.fun_formals
  and exit_reg = Register.fresh ()
  and exit_lbl = Label.fresh ()
  and _ = make_dvl (df.fun_body)
  in
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

