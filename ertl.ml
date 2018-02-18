open Rtltree
open Ertltree



let deffun (df:Rtltree.deffun) =
  let graph = ref Label.M.empty i in
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

  let return = Label.fresh() in
  graph := Label.M.add return (Ereturn(df.fun_exit)) !graph;
  {
    fun_name   = df.fun_name;
    fun_formals = df.fun_formals;
    fun_result = df.fun_result;
    fun_locals = Register.S.empty;
    fun_entry  = df.fun_entry;
    fun_exit   = return;
    fun_body   = !graph;
  }
;;


let program (p:Rtltree.program) =
  {funs = List.map deffuns p.funs}
