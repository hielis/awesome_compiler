open Rtltree
open Ertltree
open Register


let deffun (df:Rtltree.deffun) =
  let graph = ref Label.M.empty in
  let add_to_graph l i =
    graph := Label.M.add l i !graph;
  in

  let is_done = Hashtbl.create 32 in

  
  let rec __store_in_registers i lbl larg lreg =
    match larg, lreg with
    |[], _ -> i,lbl,[]
    |_, [] -> i,lbl,larg
    |ta::qa, tr::qr -> let lbl2 = Label.fresh() in
                       add_to_graph lbl (Embinop(Mmov, ta, tr, lbl2));
                       __store_in_registers (i+1) lbl2 qa qr
  and __store_in_stack j lbl = function
    |[]->j,lbl
    |t::q->let lbl2 = Label.fresh() in
           add_to_graph lbl (Epush_param(t, lbl2));
           __store_in_stack (j+1) lbl2 q
  and __unstack_args lbldest = function
    |0->lbldest
    |i->let lbl = Label.fresh() in
        add_to_graph lbl (Emunop(Maddi(Int32.of_int(8*i)), rsp, lbldest));
        lbl
  in
    
    
    
  let instr = function
    |Rtltree.Econst(i, r, l) ->
      Ertltree.Econst(i, r, l)
    |Estore(r1, r2, i, l) -> Estore(r1, r2, i, l)
    |Eload(r1, i, r2, l) -> Eload(r1, i, r2, l)
    |Emunop(op, r, l) -> Emunop(op, r, l)
    |Embinop(Mdiv, r1, r2, l) ->
      let l2 = Label.fresh()
      and l3 = Label.fresh() in
      add_to_graph l2 (Embinop(Mdiv, r1, rax, l3));
      add_to_graph l3 (Embinop(Mmov, rax, r2, l));
      Embinop(Mmov, r2, rax, l2)
    |Embinop(op, r1, r2, l) -> Embinop(op, r1, r2, l)
    |Emubranch(b, r, l1, l2) -> Emubranch(b, r, l1, l2)
    |Embbranch(b, r1, r2, l1, l2) -> Embbranch(b, r1, r2, l1, l2)
    |Egoto(l) -> Egoto(l)
    |Ecall(r, id, rl, l) ->
      let lbl = Label.fresh() in
      let (i,lbl2,l2) = __store_in_registers 0 lbl rl (Register.parameters) in
      let (j,lbl3) = __store_in_stack 0 lbl2 l2 in
      let lbl4 = Label.fresh() in
      add_to_graph lbl3 (Ecall(id, i, lbl4));
      let lbl5 = __unstack_args l j in
      add_to_graph lbl4 (Embinop(Mmov, Register.result, r, lbl5));
      Egoto(lbl);
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

  (*manips de pseudo-registre avant entrée *)
  let rec __load_from_registers lbl lreg ldest =
    match lreg,ldest with
    |[],_->lbl, List.rev ldest
    |_,[]->lbl, []
    |tr::qr, td::qd->let lbl2 = Label.fresh() in
                     add_to_graph lbl (Embinop(Mmov, tr, td, lbl2));
                     __load_from_registers lbl2 qr qd
  and __load_from_stack j lbl = function
    |[]->lbl
    |t::q->let lbl2 = Label.fresh() in
           add_to_graph lbl (Eget_param(j, t, lbl2));
           __load_from_stack (j+8) lbl2 q
  in
  let new_entry = Label.fresh () in
  let lbl = Label.fresh () in
  let (lbl2, lf) = __load_from_registers lbl (Register.parameters) (df.fun_formals) in
  let lbl3 = __load_from_stack 0 lbl2 lf in
  add_to_graph lbl3 (Egoto(df.fun_entry));
  add_to_graph new_entry (Ealloc_frame(lbl));

  (*manips de pseudo-registre avant sortie*)
  let (_,lbl4,l2) = __store_in_registers 0 (df.fun_exit) (df.fun_formals) (Register.parameters) in
  let (_,lbl5) = __store_in_stack 0 lbl4 l2 in
  let new_exit = Label.fresh() in
  add_to_graph lbl5 (Edelete_frame(new_exit));
  add_to_graph new_exit (Ereturn);
  
  rewrite_from df.fun_entry;

  
  {
    fun_name   = df.fun_name;
    fun_formals = List.length (df.fun_formals);
    fun_locals = df.fun_locals;
    fun_entry  = new_entry;
    fun_body   = !graph;
  }
;;


let program (p:Rtltree.file) =
  {funs = List.map deffun p.funs}
;;
