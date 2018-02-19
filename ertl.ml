open Rtltree
open Ertltree



let deffun (df:Rtltree.deffun) =
  let graph = ref Label.M.empty in
  let add_to_graph l i =
    graph := Label.M.add l i !graph;
  in

  let is_done = Hashtbl.create 32 in

  let instr = function
    |Rtltree.Econst(i, r, l) ->
      Ertltree.Econst(i, r, l)
    |Estore(r1, r2, i, l) -> Estore(r1, r2, i, l)
    |Eload(r1, i, r2, l) -> Eload(r1, i, r2, l)
    |Emunop(op, r, l) -> Emunop(op, r, l)
    |Embinop(op, r1, r2, l) -> failwith "Not now"
    |Emubranch(b, r, l1, l2) -> Emubranch(b, r, l1, l2)
    |Embbranch(b, r1, r2, l1, l2) -> Embbranch(b, r1, r2, l1, l2)
    |Egoto(l) -> Egoto(l)
    |Ecall(r, id, rl, l) -> failwith "Not now"
  in

  let rec rewrite_from lentry = match Hashtbl.find_opt is_done lentry with
    |Some _ -> ();
    |None ->
      Hashtbl.add is_done lentry true;
      let i = Label.M.find lentry df.fun_body in
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
      )
  in

  graph := Label.M.add df.fun_exit (Ereturn) !graph;
  rewrite_from df.fun_entry;
  {
    fun_name   = df.fun_name;
    fun_formals = List.length (df.fun_formals);
    fun_locals = Register.S.empty;
    fun_entry  = df.fun_entry;
    fun_body   = !graph;
  }
;;


let program (p:Rtltree.file) =
  {funs = List.map deffun p.funs}
