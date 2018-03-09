open Lifetime;;
open Ertltree;;
open Ertl;;
open Ltltree;;

type arcs = {prefs: Register.set; intfs: Register.set}
type igraph = arcs Register.map
           
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

type color = Ltltree.operand
type coloring = color Register.map

let colors = Register.allocatable;;

let color graph live_map =
  let costtbl = Hashtbl.create 32 in

  let stream = Stream.from (fun i -> Some(i+1)) in
  let get_spill () = Stream.next stream in
  let necessary_space () = Stream.count stream in
  

  let fill_costtbl lm =
    let __iter key info =
      let __add reg =
        match Hashtbl.find_opt costtbl reg with
        |None-> Hashtbl.add costtbl reg 1.0
        |Some(i)-> Hashtbl.replace costtbl reg (i +. 1.0)
      in
      match info.instr with
      |Econst(_,r1,_)-> __add r1
      |Eload(r2,_,r1,_)-> __add r2; __add r1
      |Estore(r2,r1,_,_)-> __add r2; __add r1
      |Emunop(_,r1,_)->  __add r1
      |Embinop(_,r2,r1,_)->  __add r2; __add r1
      |Emubranch(_,r1,_,_)-> __add r1
      |Embbranch(_,r2,r1,_,_)-> __add r2; __add r1
      |Eget_param(_,r1,_)-> __add r1
      |Epush_param(r1,_)->  __add r1
      |_-> ()
    in
    Label.M.iter __iter lm
  in
  fill_costtbl live_map;
  
  let fusionner g v1 v2 =
    if (v1<>v2) then
      (let e1 = Register.M.find v1 g and e2 = Register.M.find v2 g in
       Hashtbl.replace costtbl v2 ((Hashtbl.find costtbl v1) +. (Hashtbl.find costtbl v2)); 
       let __fold_replace v edge acc =
         let __map_replace vaux =
           if (vaux=v1) then v2 else vaux
         in
         Register.M.add v {prefs = Register.S.map __map_replace edge.prefs;
                           intfs = Register.S.map __map_replace edge.intfs;} acc
       in
       let interf = Register.S.union (Register.S.remove v2 e1.intfs) (Register.S.remove v1 e2.intfs) in
       let __fold_remove_intfs_from_prefs vertice acc =
         if(Register.S.mem vertice interf) then acc else Register.S.add vertice acc
       in
       let g2 = Register.M.remove v1 (Register.M.add v2 {prefs = Register.S.fold __fold_remove_intfs_from_prefs (Register.S.union (Register.S.remove v2 e1.prefs) (Register.S.remove v1 e2.prefs)) Register.S.empty;intfs = interf} g) in
       Register.M.fold __fold_replace g2 Register.M.empty
      )
    else g
  in
  
  let rec simplify k g =
    let __find_vertice v edge acc =
      if (Register.S.is_empty edge.prefs) then
        let c = Register.S.cardinal edge.intfs in
        if(c<k) then
          match acc with
          |None->Some(v,c)
          |Some(v2,i)->if (c<i) then Some(v,c) else acc
        else
          acc
      else
        acc
    in
    match Register.M.fold __find_vertice g None with
    |None-> coalesce k g
    |Some(v,i)-> select k g v
               
  and coalesce k g =
    let __satisfies_george_criteria v1 v2 =
      let e1 = Register.M.find v1 g and e2 = Register.M.find v2 g in
      if (Register.is_pseudo v2) then
        let __fold v acc =
          let edge = Register.M.find v g in
          acc && ((Register.is_pseudo v && ((Register.S.cardinal edge.prefs) + (Register.S.cardinal edge.intfs) < k))||((Register.S.mem v e2.prefs) || (Register.S.mem v e2.intfs)))
        in
        Register.S.fold __fold e1.prefs (Register.S.fold __fold e1.intfs true)
      else
        let __fold v acc =
          let edge = Register.M.find v g in
          acc && ((Register.is_hw v && ((Register.S.cardinal edge.prefs) + (Register.S.cardinal edge.intfs) < k))||((Register.S.mem v e2.prefs) || (Register.S.mem v e2.intfs)))
        in
        Register.S.fold __fold e1.prefs (Register.S.fold __fold e1.intfs true)  
        
    in
    let __fold_pref_edge v edges = function
      |Some(v1,v2) as acc->acc
      |None-> let __fold_aux v2 acc =
                if (__satisfies_george_criteria v v2) then
                  Some(v,v2)
                else
                  acc
              in
              Register.S.fold __fold_aux edges.prefs None
    in
    match (Register.M.fold __fold_pref_edge g None) with
    |None->freeze k g
    |Some(v1,v2)-> let u1,u2 = if (Register.is_hw v1) then v2,v1 else v1,v2 in
                   let c = simplify k (fusionner g u1 u2) in
                   Register.M.add u1 (Register.M.find u2 c) c
                   
  and freeze k g =
    let __find_vertice v edge acc =
      let l = (Register.S.cardinal edge.prefs) + (Register.S.cardinal edge.intfs) in
      if (l<k) then
        match acc with
        |None -> Some(v,l)
        |Some(v2,l2) -> if (l<l2) then Some(v,l) else acc
      else
        acc
    in
    match Register.M.fold __find_vertice g None with
    |None -> spill k g
    |Some(v,_) -> let __remove_pref key e acc =
                     if (key=v) then
                       Register.M.add v {prefs = Register.S.empty; intfs = e.intfs} acc
                     else
                       Register.M.add key {prefs = Register.S.remove v e.prefs; intfs = e.intfs} acc
                   in
                   simplify k (Register.M.fold __remove_pref g Register.M.empty)

  and spill k g =
    if (Register.M.is_empty g) then
      Register.M.empty
    else
      let __fold_minimal v edge acc =
        let c = (Hashtbl.find costtbl v) /. (Pervasives.float_of_int ((Register.S.cardinal edge.prefs) + (Register.S.cardinal edge.intfs))) in
        match acc with
        |None->Some(v,c)
        |Some(v2,c2)-> if (c<c2) then Some(v,c) else acc
      in
      match Register.M.fold __fold_minimal g None with
      |None->failwith "Should be some dead code"
      |Some(v,_)->select k g v

  and select k g v =
    let __fold_remove vaux edge acc =
      Register.M.add vaux {prefs = Register.S.remove v edge.prefs; intfs = Register.S.remove v edge.intfs} acc
    in
    
    let c = simplify k (Register.M.fold __fold_remove (Register.M.remove v g) Register.M.empty) in
    let __find_color v available_colors =
      try (match (Register.M.find v c) with
           |Reg(r)->Register.S.remove r available_colors
           |Spilled(_)->available_colors)
      with Not_found -> available_colors
    in
    let edges = Register.M.find v g in
    let color_set = (*Register.S.fold __find_color edges.prefs *)(Register.S.fold __find_color edges.intfs colors) in
    let couleur = try (Reg (if (Register.S.mem v color_set) then v else Register.S.min_elt color_set))
                  with Not_found -> Spilled (-8*(get_spill ()))
    in
    Register.M.add v couleur c

  in
  let c = simplify (Register.S.cardinal colors) graph in
  (c,8*(necessary_space ()))

let deffun (df:Ertltree.deffun) =
  let live_map = liveness df.fun_body in
  let c,space = color (make (live_map)) live_map in
  let lookup r = 
    (*if (Register.is_hw r) && List.mem r Register.parameters then Reg(r)
    else*) Register.M.find r c in
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
  let c,_ = (color (make l)) l in
  print c
  
let print_ltl fmt (p: Ertltree.file) =
  fprintf fmt "=== PREFS & INTFS GRAPH  =============================@\n";
  List.iter print_deffun p.funs;
  Pervasives.print_newline ();
  fprintf fmt "\n=== COLORS ===============================@\n";
  List.iter print_deffun_colors p.funs;
  Pervasives.print_newline ();
  
