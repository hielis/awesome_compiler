open Rtltree
open Ertltree
open Register


let deffun (df:Rtltree.deffun) =
  let graph = ref Label.M.empty in
  let add_to_graph l i =
    graph := Label.M.add l i !graph;
  in

  let is_done = Hashtbl.create 32 in

  let rec generate_new_labels acc = function
    |[]->acc
    |t::q->generate_new_labels ((Label.fresh ())::acc) q
  in
  let rec __store_in_registers i lbl_list larg lreg =
    match lbl_list,larg, lreg with
    |_,[], _ -> i,lbl_list,[]
    |_,_, [] -> i,lbl_list,larg
    |[],_,_ -> failwith "larg is shorter, case impossible"
    |t::[],_,_->failwith "larg is shorter, so is []" 
    |tl1::tl2::ql,ta::qa, tr::qr -> add_to_graph tl1 (Embinop(Mmov, ta, tr, tl2));
                              __store_in_registers (i+1) (tl2::ql) qa qr
  and __store_in_stack j lbl_list larg =
    match lbl_list, larg with
    |_,[]->j,lbl_list
    |[],_-> failwith "same thing, already handled"
    |t::[],_->failwith "dead code"
    |tl1::tl2::ql,ta::qa-> add_to_graph tl1 (Epush_param(ta, tl2));
                     __store_in_stack (j+1) (tl2::ql) qa
  and __unstack_args lbl0 lbl1 = function
    |0->lbl0
    |i->add_to_graph lbl1 (Emunop(Maddi(Int32.of_int(8*i)), rsp, lbl0));
        lbl1
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
      try
        (let reg = List.hd rl in
         let len = (List.length rl - 6) in
         let lbl5 = if(len > 0) then (let lr=Label.fresh ()in add_to_graph lr (Emunop(Maddi(Int32.of_int(8*len)), rsp, l)); lr) else l in
         let lbl4 = Label.fresh () in
         let lbl_list = generate_new_labels [] rl in
         let (i,lbl2,l2) = __store_in_registers 1 lbl_list (List.tl rl) (List.tl (Register.parameters)) in
      (*let lbl = Label.fresh() in
      let(i,lbl2,l2) = __store_in_registers 0 lbl rl (Register.parameters) in*)
         let (j,lbl_l) = __store_in_stack 0 lbl2 l2 in
         let lbl3 = (match lbl_l with
                     |t::[]->t
                     |_-> failwith "dead code1")
         in
         add_to_graph lbl3 (Ecall(id, i, lbl4));
         (*let lbl6 = __unstack_args l lbl5 j in*)
         let lbl6 = lbl5 in
         add_to_graph lbl4 (Embinop(Mmov, Register.result, r, lbl6));
         Embinop(Mmov, reg, (List.hd (Register.parameters)), (List.hd lbl_list));)
      with Failure _ ->
        (let lbl = Label.fresh() in
         add_to_graph lbl (Embinop(Mmov, Register.result, r, l));
         Ecall(id, 0, lbl);)
        (*  Egoto(lbl);*)
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
  let rec __load_from_registers lbl_list lreg ldest =
    match lbl_list,lreg,ldest with
    |_,[],_->lbl_list, List.rev ldest
    |_,_,[]->lbl_list, []
    |[],_,_->failwith "dead codeA" 
    |t::[],_,_->failwith "likewiseA"
    |tl1::tl2::ql,tr::qr, td::qd-> add_to_graph tl1 (Embinop(Mmov, tr, td, tl2));
                                   __load_from_registers (tl2::ql) qr qd
  and __load_from_stack j lbl_list ldest =
    match lbl_list, ldest with
    |_,[]->lbl_list
    |[],_->failwith "dead codeB"
    |t::[],_-> failwith "likewiseB"
    |t1::t2::ql,t::q-> add_to_graph t1 (Eget_param(j, t, t2));
                       __load_from_stack (j+8) (t2::ql) q
  in

  let rec new_lbls acc = function
    |[]->acc
    |t::[]->acc
    |t::q->new_lbls ((Label.fresh())::acc) q
  in
  let lbl = generate_new_labels [df.fun_entry] df.fun_formals in
  let (lbl2, lf) = __load_from_registers lbl (Register.parameters) (df.fun_formals) in
  (match (__load_from_stack 16 lbl2 lf) with
   |t::[]->()
   |_-> failwith "dead code3");
  let new_entry = Label.fresh () in
  add_to_graph new_entry (Ealloc_frame(List.hd lbl));

  (*manips de pseudo-registre avant sortie*)
  let new_exit = Label.fresh() in
  let local_reg = df.fun_result::(df.fun_formals) in
  let param = rax::Register.parameters in
  let label_list = df.fun_exit::(generate_new_labels [] local_reg) in
  let (_,lbl4,l2) = __store_in_registers 0 (label_list) local_reg param in
  let (_,lbl5) = __store_in_stack 0 lbl4 l2 in
  let lbl6 = (match lbl5 with
                     |t::[]->t
                     |_-> failwith "dead code2")
  in
  add_to_graph lbl6 (Edelete_frame(new_exit));
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
