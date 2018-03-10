open Rtltree
open Ertltree
open Register


let deffun (df:Rtltree.deffun) =
  let graph = ref Label.M.empty in
  let locals_reg = ref df.fun_locals in
  let add_to_graph l i =
    graph := Label.M.add l i !graph;
  in

  let is_done = Hashtbl.create 32 in
  
  let manage_args_and_call lbl_ret id r l =

    let __toreg_tostack =
      let rec __aux first_arg i j accr accs = function
        |[]->let rec __aux2 acc = function |i when i>=6-> acc | i -> __aux2 (None::acc) (i+1) in
             (first_arg, i, __aux2 accr i, j, accs)
        |t::q when i=0 -> __aux (Some(t)) (i+1) j (Some(t)::accr) accs q
        |t::q when i<6->__aux first_arg (i+1) j (Some(t)::accr) accs q
        |t::q-> __aux first_arg i (j+1) accr (t::accs) q
      in __aux None 0 0 [] []
    in

    let __store_in_registers =
      let __fold lbl arg reg =
        match arg with
        |None->lbl
        |Some(t)-> let l = Label.fresh () in
                   add_to_graph l (Embinop(Mmov, t, reg, lbl));
                   l
      in List.fold_left2 __fold
    in

    let __store_in_stack =
      let __fold lbl arg =
        let l = Label.fresh () in
        add_to_graph l (Epush_param(arg, lbl));
        l
      in List.fold_left __fold
    in

    (*let __save_caller =
      let __fold lbl reg arg =
        let l = Label.fresh () in
        add_to_graph l (Embinop(Mmov, reg, arg, lbl));
        l
      in List.fold_left2 __fold
    in
    let __restore_caller =
      __save_caller
    in
    let __generate_new_register e =
      let reg=Register.fresh() in
      locals_reg:=Register.S.add reg !locals_reg;
      reg
    in 
    let local_reg = List.rev_map __generate_new_register Register.caller_saved in
    let rev_caller = List.rev Register.caller_saved in
     *)
    let __unstack_args lbldest = function
    |0->lbldest
    |i->let lbl = Label.fresh () in
        add_to_graph lbl (Emunop(Maddi(Int32.of_int(8*i)), rsp, lbldest));
        lbl
    in
        
    let(first_arg, i, l1, j, l2) = __toreg_tostack l in
    let lbl = lbl_ret in (*let lbl = __restore_caller lbl_ret local_reg rev_caller in*)
    let lbl2 = __unstack_args lbl j in
    let lbl3 = Label.fresh() in
    add_to_graph lbl3 (Embinop(Mmov, Register.result, r, lbl2));
    let lbl4 = Label.fresh() in
    add_to_graph lbl4 (Ecall(id, i, lbl3));
    let lbl5 = __store_in_stack lbl4 l2 in
    let lbl6 = __store_in_registers lbl5 l1 (List.rev (Register.parameters)) in
    let lbl7 = lbl6 in (*let lbl7 = __save_caller lbl6 rev_caller local_reg in*)
    Egoto(lbl7);
      
    
  in
  let instr = function
    |Rtltree.Econst(i, r, l) ->
      Ertltree.Econst(i, r, l)
    |Estore(r1, r2, i, l) -> Estore(r1, r2, i, l)
    |Eload(r1, i, r2, l) -> Eload(r1, i, r2, l)
    |Emunop(op, r, l) -> Emunop(op, r, l)
    |Embinop(Mdiv, r1, r2, l) ->
      let l3 = Label.fresh() in
      let l2 = Label.fresh() in
      add_to_graph l2 (Embinop(Mdiv, r1, rax, l3));
      add_to_graph l3 (Embinop(Mmov, rax, r2, l));
      Embinop(Mmov, r2, rax, l2)
    |Embinop(op, r1, r2, l) -> Embinop(op, r1, r2, l)
    |Emubranch(b, r, l1, l2) -> Emubranch(b, r, l1, l2)
    |Embbranch(b, r1, r2, l1, l2) -> Embbranch(b, r1, r2, l1, l2)
    |Egoto(l) -> Egoto(l)
    |Ecall(r, id, rl, l) -> manage_args_and_call l id r rl

  in
  let rec rewrite_from lentry = match Hashtbl.find_opt is_done lentry with
    |Some _ -> ();
    |None ->
      Hashtbl.add is_done lentry true;
      (try (let i = Label.M.find lentry df.fun_body in
           add_to_graph lentry (instr i);
           (match i with
            |Rtltree.Econst(i, r, l) -> rewrite_from l
            |Estore(r1, r2, i, l) -> rewrite_from l
            |Eload(r1, i, r2, l) -> rewrite_from l
            |Emunop(op, r, l) -> rewrite_from l
            |Embinop(op, r1, r2, l) -> rewrite_from l
            |Emubranch(b, r, l1, l2) -> rewrite_from l1; rewrite_from l2
            |Embbranch(b, r1, r2, l1, l2) -> rewrite_from l1; rewrite_from l2
            |Egoto(l) -> rewrite_from l;
            |Ecall(r, id, rl, l) -> rewrite_from l;
           ))
        with Not_found -> if lentry = df.fun_exit then ()
                          else failwith "This doesnt work"
      )
  in

  
  let manage_fun_args lbl_entry lbl_ret exit_reg l =

    let __fromreg_fromstack =
      let rec __aux i j accr accs = function
        |[]->let rec __aux2 acc = function |i when i>=6-> acc | i -> __aux2 (None::acc) (i+1) in
             (i, __aux2 accr i, j, accs)
        |t::q when i<6->__aux (i+1) j (Some(t)::accr) accs q
        |t::q-> __aux i (j+1) accr (t::accs) q
      in __aux 0 0 [] []
    in

    let __load_from_registers =
      let __fold lbl reg = function
        |None-> lbl
        |Some(t)-> let l = Label.fresh () in
                   add_to_graph l (Embinop(Mmov, reg, t, lbl));
                   l
      in List.fold_left2 __fold
    in

    let __load_from_stack =
      let i = ref 16 in
      let __fold lbl arg = 
        let l = Label.fresh () in
        add_to_graph l (Eget_param(!i,arg, lbl));
        i:=8+(!i);
        l
      in List.fold_left __fold
    in

    let __save_callee =
      let __fold lbl reg arg =
        let l = Label.fresh () in
        add_to_graph l (Embinop(Mmov, reg, arg, lbl));
        l
      in List.fold_left2 __fold
    in
    let __restore_callee =
      __save_callee
    in
    let __generate_new_register e =
    let r=Register.fresh() in
    locals_reg:=Register.S.add r !locals_reg;
    r
    in

    let(i, l1, j, l2) = __fromreg_fromstack l in
    let lbl = __load_from_stack lbl_entry l2 in
    let param = List.rev Register.parameters in
    let lbl2 = __load_from_registers lbl param l1 in
    let local_reg = List.rev_map __generate_new_register Register.callee_saved in
    let rev_callee = List.rev Register.callee_saved in
    let lbl3 = __save_callee lbl2 rev_callee local_reg in
    let new_entry = Label.fresh () in
    add_to_graph new_entry (Ealloc_frame(lbl3));

    let new_exit = Label.fresh() in
    add_to_graph new_exit (Ereturn);
    let lbl4 = Label.fresh() in
    add_to_graph lbl4 (Edelete_frame(new_exit));
    let lbl5 = __restore_callee lbl4 local_reg rev_callee in
    add_to_graph lbl_ret (Embinop(Mmov, exit_reg, Register.rax, lbl5));
    new_entry
    
  in

  let new_entry = manage_fun_args df.fun_entry df.fun_exit df.fun_result df.fun_formals in
    
  rewrite_from df.fun_entry;

  {
    fun_name   = df.fun_name;
    fun_formals = List.length (df.fun_formals);
    fun_locals = !locals_reg;
    fun_entry  = new_entry;
    fun_body   = !graph;
  }
;;


let program (p:Rtltree.file) =
  {funs = List.map deffun p.funs}
;;
