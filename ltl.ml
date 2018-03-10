open Lifetime;;
open Ertltree;;
open Ertl;;
open Ltltree;;

type arcs = {prefs: Register.set; intfs: Register.set}
type igraph = arcs Register.map
(*
let make live_map =
  let __fold_pref key info graph =
    match info.instr with
    |Embinop(b,r1,r2,lbl) when (b = Mmov && r1<>r2) ->
      let __add_pref reg = function
        |None->Some({prefs = Register.S.singleton reg; intfs = Register.S.empty})
        |Some(arc) -> Some({prefs = Register.S.add reg arc.prefs ; intfs = arc.intfs})
      in
      Register.M.update r2 (__add_pref r1) (Register.M.update r1 (__add_pref r2) graph)
    |_ -> graph
  in
  let __fold_intf key info graph =
    let __add_intf reg = function
      |None->Some({prefs = Register.S.empty; intfs = Register.S.singleton reg})
      |Some(arc) -> Some({prefs = Register.S.remove reg arc.prefs; intfs = Register.S.add reg arc.intfs})
    in
    match info.instr with
    |Embinop(b,r2,r1,_) when (b = Mmov && r1<>r2) ->
      let __fold_outs r g =
        if (r = r2 ||r = r1) then g
        else
          Register.M.update r (__add_intf r1) (Register.M.update r1 (__add_intf r) g)
      in
      Register.S.fold __fold_outs info.outs graph
    |Econst(_,r1,_)->let __fold_outs r g =
                       if (r = r1) then g
                       else
                         Register.M.update r (__add_intf r1) (Register.M.update r1 (__add_intf r) g)
                     in Register.S.fold __fold_outs info.outs graph
    |Eload(_,_,r1,_)->let __fold_outs r g =
                        if (r = r1) then g
                        else
                          Register.M.update r (__add_intf r1) (Register.M.update r1 (__add_intf r) g)
                     in Register.S.fold __fold_outs info.outs graph
    |Estore(_,r1,_,_)-> let __fold_outs r g =
                          if (r = r1) then g
                          else
                            Register.M.update r (__add_intf r1) (Register.M.update r1 (__add_intf r) g)
                        in Register.S.fold __fold_outs info.outs graph
    |Emunop(_,r1,_)-> let __fold_outs r g =
                        if (r = r1) then g
                        else
                          Register.M.update r (__add_intf r1) (Register.M.update r1 (__add_intf r) g)
                      in Register.S.fold __fold_outs info.outs graph
    |Embinop(_,_,r1,_)-> let __fold_outs r g =
                           if (r = r1) then g
                           else
                             Register.M.update r (__add_intf r1) (Register.M.update r1 (__add_intf r) g)
                         in Register.S.fold __fold_outs info.outs graph
    (*|Emubranch(_,r1,_,_)-> let __fold_outs r g =
                             if (r = r1) then g
                             else
                               Register.M.update r (__add_intf r1) (Register.M.update r1 (__add_intf r) g)
                           in Register.S.fold __fold_outs info.outs graph
    |Embbranch(_,_,r1,_,_)-> let __fold_outs r g =
                               if (r = r1) then g
                               else
                                 Register.M.update r (__add_intf r1) (Register.M.update r1 (__add_intf r) g)
                             in Register.S.fold __fold_outs info.outs graph*)
    |Eget_param(_,r1,_)-> let __fold_outs r g =
                            if (r = r1) then g
                            else
                              Register.M.update r (__add_intf r1) (Register.M.update r1 (__add_intf r) g)
                          in Register.S.fold __fold_outs info.outs graph
    |Epush_param(r1,_)-> let __fold_outs r g =
                           if (r = r1) then g
                           else
                             Register.M.update r (__add_intf r1) (Register.M.update r1 (__add_intf r) g)
                         in Register.S.fold __fold_outs info.outs graph
    |_-> graph
  in
  Label.M.fold __fold_intf live_map (Label.M.fold __fold_pref live_map Register.M.empty)
*)



let make live_map =
  let graph = ref Register.M.empty in
  let add_pref l i = match i.instr with
    |Embinop(op, r1, r2, l) when op = Mmov-> 
      (match Register.M.find_opt r1 !graph with
       |Some(a) -> graph := Register.M.add r1 {prefs = Register.S.add r2 a.prefs; intfs = a.intfs} !graph 
       |None -> graph := Register.M.add r1 {prefs = Register.S.singleton r2;
                                            intfs = Register.S.empty} !graph;);
      (match Register.M.find_opt r2 !graph with
       |Some(a) -> graph := Register.M.add r2 {prefs = Register.S.add r1 a.prefs; intfs = a.intfs} !graph 
       |None -> graph := Register.M.add r2 {prefs = Register.S.singleton r1;
                                                                                   intfs = Register.S.empty} !graph;);
    |_-> ()
  in
  Label.M.iter add_pref live_map;
  let add_intfs l i = 
    let intfs r1 r2 = if r1 = r2 then () else
      (match Register.M.find_opt r1 !graph with
       |Some(a) -> graph := Register.M.add r1 {prefs =  Register.S.remove r2 a.prefs; intfs = Register.S.add r2 a.intfs} !graph 
       |None -> graph := Register.M.add r1 {prefs = Register.S.empty;
                                            intfs = Register.S.singleton r2} !graph;);
       (match Register.M.find_opt r2 !graph with
       |Some(a) -> graph := Register.M.add r2 {prefs =  Register.S.remove r1 a.prefs; intfs = Register.S.add r1 a.intfs} !graph 
       |None -> graph := Register.M.add r2 {prefs = Register.S.empty;
                                            intfs = Register.S.singleton r1} !graph;);
    in
    match i.instr with
     | Econst(c, r, l) -> Register.S.iter (intfs r) i.outs
     | Eload(r1, n, r2, l) ->  Register.S.iter (intfs r1) i.outs;  Register.S.iter (intfs r2) i.outs;
     | Estore(r1, r2, n, l) -> Register.S.iter (intfs r1) i.outs;  Register.S.iter (intfs r2) i.outs;
     | Emunop(op, r, l) -> Register.S.iter (intfs r) i.outs
     | Embinop(op, r1, r2, l) when op <> Mmov -> Register.S.iter (intfs r1) i.outs;  Register.S.iter (intfs r2) i.outs;
     | Emubranch(op, r, l1, l2) ->  Register.S.iter (intfs r) i.outs
     | Embbranch(op, r1, r2, l1, l2) -> Register.S.iter (intfs r1) i.outs;  Register.S.iter (intfs r2) i.outs;
     | Eget_param(n, r, l) -> Register.S.iter (intfs r) i.outs
     | Epush_param(r, l) ->Register.S.iter (intfs r) i.outs
     |_ -> ()
  in
  Label.M.iter add_intfs live_map;
  !graph
;;


type color = Ltltree.operand
type coloring = color Register.map


let color g =
  let rec registers_to_do_aux l a s = match a.instr with
  | Econst(c, r, l) when (Register.is_pseudo r)->
     (Register.S.add r s)
  | Eload(r1, n, r2, l) -> 
     (match Register.is_pseudo r1, Register.is_pseudo r2 with
      |true, true -> Register.S.add r2 (Register.S.add r1 s)
      |true, false -> (Register.S.add r1 s)
      |false, true -> (Register.S.add r2 s)
      |_ -> s)
  | Estore(r1, r2, n, l) ->
     (match Register.is_pseudo r1, Register.is_pseudo r2 with
      |true, true -> Register.S.add r2 (Register.S.add r1 s)
      |true, false -> (Register.S.add r1 s)
      |false, true -> (Register.S.add r2 s)
      |_ -> s)
  | Emunop(op, r, l) when (Register.is_pseudo r)->
     (Register.S.add r s)
  | Embinop(op, r1, r2, l) ->
     (match Register.is_pseudo r1, Register.is_pseudo r2 with
      |true, true -> Register.S.add r2 (Register.S.add r1 s)
      |true, false -> (Register.S.add r1 s)
      |false, true -> (Register.S.add r2 s)
      |_ -> s)
  | Emubranch(op, r, l1, l2) when (Register.is_pseudo r)->
     Register.S.add r s
  | Embbranch(op, r1, r2, l1, l2) ->
      (match Register.is_pseudo r1, Register.is_pseudo r2 with
       |true, true -> Register.S.add r2 (Register.S.add r1 s)
       |true, false -> (Register.S.add r1 s)
       |false, true -> (Register.S.add r2 s)
       |_ -> s)
  | Eget_param(n, r, l) when (Register.is_pseudo r)->
     (Register.S.add r s)
  | Epush_param(r, l) when (Register.is_pseudo r)->
     (Register.S.add r s)

  | _ -> s
  in
  let to_do = ref (Label.M.fold registers_to_do_aux g Register.S.empty) in
  let graph = ref (make g) in
  let tbl_colors = ref Register.M.empty in
  let tmp = Hashtbl.create 257 in
  let colors = ref Register.allocatable in
  let n = ref 8 in
  let add_binding r c =
    tbl_colors := Register.M.add r c !tbl_colors;
  in
  let remove_register r =
    to_do := Register.S.remove r !to_do;
  in
  let init_tbl r =
    let s = Register.M.find r !graph in
    Hashtbl.add tmp r (Register.S.diff !colors s.intfs);
  in
  Register.S.iter init_tbl !to_do;
  let find_singleton () =
    let rec aux = function 
      |[] -> None
      |a::tl -> let s = Hashtbl.find tmp a in 
        if (Register.S.cardinal (s) = 1) then 
          (
            let c = List.hd (Register.S.elements s) in
            Some(a, c))
        else (aux tl)
    in
    aux (Register.S.elements !to_do)
  in
  let find_singleton_with_pref () =
    let rec aux = function
      |[] -> None
      |a::tl -> 
        let s = Hashtbl.find tmp a in
        if (Register.S.cardinal (s) = 1) then
          (let c = List.hd (Register.S.elements s) in
           let h = Register.M.find a !graph in
           if (Register.S.mem c h.prefs) then Some(a, c)
           else (aux tl)
          )
        else (aux tl)
    in
    aux (Register.S.elements !to_do)
  in
  let find_register_with_binded_pref () =
    let has_a_binding r =
        let s = Register.M.find r !graph in
        let test e = (Register.M.mem e !tbl_colors) in
        (Register.S.find_first_opt test s.prefs)
    in
    let rec aux = function
      |[] -> None
      |a::tl -> (
        match has_a_binding a with
        |Some(r) -> Some(a, (Register.M.find r !tbl_colors))
        |None -> aux tl
      )
    in
    aux (Register.S.elements !to_do)
  in
  let find_register_with_one_color () =
    let has_mtoc r =
     let s = Hashtbl.find tmp r in
     (Register.S.cardinal s > 0)
    in
    match Register.S.find_first_opt has_mtoc !to_do with
    |None -> None
    |Some(r) -> 
      let s = Hashtbl.find tmp r in
      Some(r, Reg(Register.S.max_elt s))
  in

  let update_tbl r d =
    match d with
    |Spilled(n) -> ()
    |Reg(c) ->
      let m = Register.M.find r !graph in
      let aux reg s =
        if (Register.S.mem reg m.intfs) then Some(Register.S.remove c s)
        else Some(s)
      in
      Hashtbl.filter_map_inplace aux tmp;
  in
  let put_color r c =
    remove_register r;
    add_binding r c;
    update_tbl r c;
  in

  let rec loop () = match Register.S.is_empty !to_do with
    |true -> ()
    |_ ->
      (match find_singleton_with_pref () with
       |Some(r, c) -> put_color r (Reg(c))
       |None ->
         (match find_singleton () with
          |Some(r, c) -> put_color r (Reg(c))
          |None -> 
            (match find_register_with_binded_pref () with
             |Some(r, c) -> put_color r c
             |None -> 
               (match find_register_with_one_color () with
                |Some(r, c) -> put_color r c
                |None -> put_color (Register.S.max_elt !to_do) (Spilled(-(!n)));
                         n := !n + 8;
               )
            )
         )
      );
     loop ();
  in
  loop ();
  (!tbl_colors, !n - 8)
;;

let deffun (df:Ertltree.deffun) =
  let live_map = liveness df.fun_body in
  let c,space = color live_map in
  let lookup r = 
    if (Register.is_hw r) then Reg(r)
    else Register.M.find r c in
  let graph = ref Label.M.empty in
  let add_to_graph l i =
    graph := Label.M.add l i !graph;
  in

  let is_done = Hashtbl.create 32 in
  
  let instr = function
    |Ertltree.Econst(i, r, l) -> Ltltree.Econst(i, lookup r, l)
    |Estore(r1, r2, i, l) -> (match (lookup r1),(lookup r2) with
                              |Reg(p1),Reg(p2)->Estore(p1, p2, i, l)
                              |Reg(p1),s2->let l2 = Label.fresh() in
                                           let l3 = Label.fresh() in
                                           add_to_graph l3 (Embinop(Mmov, Reg(Register.tmp1), s2, l));
                                           add_to_graph l2 (Estore(p1, Register.tmp1, i, l2));
                                           Embinop(Mmov, s2, Reg(Register.tmp1), l2);
                              |s1,Reg(p2)->let l2 = Label.fresh() in
                                           add_to_graph l2 (Estore(Register.tmp1, p2, i, l));
                                           Embinop(Mmov, s1, Reg(Register.tmp1), l2);
                              |s1,s2->let l2 = Label.fresh() in
                                      let l3 = Label.fresh() in
                                      let l4 = Label.fresh() in
                                      add_to_graph l2 (Embinop(Mmov, Reg(Register.tmp2), s2, l));
                                      add_to_graph l3 (Estore(Register.tmp1, Register.tmp2, i, l2));
                                      add_to_graph l4 (Embinop(Mmov, s2, Reg(Register.tmp2), l3));
                                      Embinop(Mmov, s1, Reg(Register.tmp1), l4)
                             )
    |Eload(r1, i, r2, l) -> (match (lookup r1),(lookup r2) with
                             |Reg(p1),Reg(p2)->Eload(p1, i, p2, l)
                             |Reg(p1),s2->let l2 = Label.fresh() in
                                          add_to_graph l2 (Embinop(Mmov, Reg(Register.tmp1), s2, l));
                                          Eload(p1, i, Register.tmp1, l2);
                             |s1,Reg(p2)->let l2 = Label.fresh() in
                                          add_to_graph l2 (Eload(Register.tmp1, i, p2, l));
                                          Embinop(Mmov, s1, Reg(Register.tmp1), l2);
                             |s1,s2->let l2 = Label.fresh() in
                                     let l3 = Label.fresh() in
                                     add_to_graph l2 (Embinop(Mmov, s1, Reg(Register.tmp1), l));
                                     add_to_graph l3 (Eload(Register.tmp1, i, Register.tmp2, l2));
                                     Embinop(Mmov, Reg(Register.tmp2), s2, l3)
                            )
    |Emunop(op, r, l) -> Emunop(op, lookup r, l)
    |Embinop(op, r1, r2, l) when op = Mmov && (lookup r1)=(lookup r2) -> Egoto(l)
    |Embinop(op, r1, r2, l) when op = Mmul -> let s1 = lookup r1 and s2 = lookup r2 in
                                              (match s2 with
                                              |Reg(_)->Embinop(Mmul, s1, s2, l)
                                              |_->let l2 = Label.fresh() in
                                                  let l3 = Label.fresh() in
                                                  add_to_graph l2 (Embinop(Mmov, Reg(Register.tmp1), s2, l));
                                                  add_to_graph l3 (Embinop(Mmul, s1, Reg(Register.tmp1), l2)); 
                                                  Embinop(Mmov, s2, Reg(Register.tmp1), l3)
                                              )
    |Embinop(op, r1, r2, l) -> let s1 = lookup r1 and s2 = lookup r2 in
                               (match s1,s2 with
                                |Spilled(_),Spilled(_)->let l2 = Label.fresh() in
                                                        let l3 = Label.fresh() in
                                                        add_to_graph l2 (Embinop(Mmov, Reg(Register.tmp1), s2, l));
                                                        add_to_graph l3 (Embinop(op, s1, Reg(Register.tmp1), l2)); 
                                                        Embinop(Mmov, s2, Reg(Register.tmp1), l3)
                                |_,_-> Embinop(op, s1, s2, l)
                               )
    |Emubranch(b, r, l1, l2) -> 
      (match (lookup r) with
       |Spilled(n) -> let lp = Label.fresh() in
                      add_to_graph lp (Emubranch(b, Register.tmp1, l1, l2));
                      Embinop(Mmov, Spilled(n), Reg(Register.tmp1), lp);
       |Reg(rp) -> Emubranch(b, rp, l1, l2)
      )
    |Embbranch(b, r1, r2, l1, l2) -> 
      (match (lookup r1, lookup r2) with
       |Spilled(n1), Spilled(n2)->
         let lp = Label.fresh() in
         let lp1 = Label.fresh () in
         add_to_graph lp1 ( Embinop(Mmov, Spilled(n1), Reg(Register.tmp1), lp1));
         add_to_graph lp (Embbranch(b, Register.tmp1, Register.tmp2, l1, l2));
         Embinop(Mmov, Spilled(n2), Reg(Register.tmp2), lp1)
       |Reg(r1p), Spilled(n2)->
         let lp = Label.fresh() in
         add_to_graph lp (Embbranch(b, r1p, Register.tmp1, l1, l2));
         Embinop(Mmov, Spilled(n2), Reg(Register.tmp1), lp)
       |Spilled(n1), Reg(r2p)->
         let lp = Label.fresh() in
         add_to_graph lp (Embbranch(b, Register.tmp1, r2p, l1, l2));
         Embinop(Mmov, Spilled(n1), Reg(Register.tmp1), lp);
       |Reg(r1p), Reg(r2p) -> Embbranch(b, r1p, r2p, l1, l2)
      )

    |Egoto(l) -> Egoto(l)
    |Ecall(id,n,l) -> Ecall(id,l)
    |Ealloc_frame(l) -> let l2 = Label.fresh() in
                        let l3 = Label.fresh() in
                        add_to_graph l2 (Emunop(Maddi(Int32.of_int((-space))), Reg(Register.rsp), l));
                        add_to_graph l3 (Embinop(Mmov, Reg(Register.rsp), Reg(Register.rbp), l2));
                        Epush(Reg(Register.rbp), l3);
    |Edelete_frame(l) -> let l2 = Label.fresh() in
                         add_to_graph l2 (Epop(Register.rbp, l));
                         Embinop(Mmov, Reg(Register.rbp), Reg(Register.rsp), l2);
    |Eget_param(n,r,l) -> let l2 = Label.fresh() in
                          add_to_graph l2 (Embinop(Mmov, Reg(Register.tmp1), lookup r, l));
                          Embinop(Mmov, Spilled(n), Reg(Register.tmp1), l2) 
    |Epush_param(r,l) -> Epush(lookup r, l)
    |Ereturn -> Ereturn
  in

  let rec rewrite_from lentry = match Hashtbl.find_opt is_done lentry with
    |Some _ -> ();
    |None ->
      Hashtbl.add is_done lentry true;
      let i = Label.M.find lentry df.fun_body in
      add_to_graph lentry (instr i);
      (match i with
       |Ertltree.Econst(i, r, l) -> rewrite_from l
       |Estore(r1, r2, i, l) -> rewrite_from l
       |Eload(r1, i, r2, l) -> rewrite_from l
       |Emunop(op, r, l) -> rewrite_from l
       |Embinop(op, r1, r2, l) -> rewrite_from l
       |Emubranch(b, r, l1, l2) -> rewrite_from l1; rewrite_from l2
       |Embbranch(b, r1, r2, l1, l2) -> rewrite_from l1; rewrite_from l2
       |Egoto(l) -> rewrite_from l;
       |Ecall(id, rl, l) -> rewrite_from l;
       |Ealloc_frame(l)-> rewrite_from l
       |Edelete_frame(l)-> rewrite_from l
       |Eget_param(_,_,l)-> rewrite_from l
       |Epush_param(_,l)-> rewrite_from l
       |Ereturn -> ()
       )
  in
  
  rewrite_from df.fun_entry;
                                
  {
    fun_name = df.fun_name;
    fun_entry = df.fun_entry;
    fun_body = !graph;
  }

let program (p:Ertltree.file) =
  {funs = List.map deffun p.funs}
                                  
open Format
open Pp
   
let print ig =
  Register.M.iter (fun r arcs ->
    Format.printf "%s: prefs=@[%a@] intfs=@[%a@]@." (r :> string)
      Register.print_set arcs.prefs Register.print_set arcs.intfs) ig

let print_deffun (f: Ertltree.deffun) =
  print (make (liveness f.fun_body))

let print_color fmt = function
  | Reg hr    -> fprintf fmt "%a" Register.print hr
  | Spilled n -> fprintf fmt "stack %d" n
let print cm =
  Register.M.iter
    (fun r cr -> printf "%a -> %a@\n" Register.print r print_color cr) cm
  
let print_deffun_colors (f: Ertltree.deffun) =
  let l = liveness f.fun_body in
  let c,_ = color  l in
  print c
  
let print_ltl fmt (p: Ertltree.file) =
  fprintf fmt "=== PREFS & INTFS GRAPH  =============================@\n";
  List.iter print_deffun p.funs;
  Pervasives.print_newline ();
  fprintf fmt "\n=== COLORS ===============================@\n";
  List.iter print_deffun_colors p.funs;
  Pervasives.print_newline ();
  
