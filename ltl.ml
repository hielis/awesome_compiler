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
    |Embinop(b,r2,r1,_) when (b = Mmov )(*&& r1<>r2)*) ->
      let __fold_outs r g =
        if (r = r2 ||r = r1) then g
        else
          Register.M.update r (__add_intf r1) (Register.M.update r1 (__add_intf r) g)
      in
      Register.S.fold __fold_outs info.outs graph
    |_-> 
      let __fold_outs r g =
        Register.S.fold (fun rdef gp -> if(r<>rdef) then Register.M.update r (__add_intf rdef) (Register.M.update rdef (__add_intf r) gp) else gp) info.defs g
      in
      Register.S.fold __fold_outs info.outs graph
  in
  Label.M.fold __fold_intf live_map (Label.M.fold __fold_pref live_map Register.M.empty)

type color = Ltltree.operand
type coloring = color Register.map

module Color = struct
  type t = color
  let compare c1 c2 =
    match c1,c2 with
    |Reg(_),Spilled(_)-> -1
    |Spilled(_),Reg(_)->1
    |Reg(r1),Reg(r2)->Pervasives.compare (r1:>string) (r2:>string)
    |Spilled(n1),Spilled(n2)-> Pervasives.compare n2 n1
end

module ColorSet = Set.Make(Color)
             
let colors = Register.S.fold (fun elt acc -> ColorSet.add (Reg(elt)) acc) Register.allocatable ColorSet.empty

exception Edge of Register.t * Register.t
exception FoundReg of color
                 
let color graph live_map =
  let h = Hashtbl.create 129 in

  let __fill_hashtable lbl info =
    let __add (reg: Register.t) =
      match Hashtbl.find_opt h reg with
      |None-> Hashtbl.add h reg 1.0;
      |Some(i)-> Hashtbl.replace h reg (i +. 1.0);
    in
    match info.instr with
    |Econst(_,r1,_)-> __add r1
    |Eload(r2,_,r1,_)-> __add r2;__add r1
    |Estore(r2,r1,_,_)-> __add r2; __add r1
    |Emunop(_,r1,_)->  __add r1
    |Embinop(_,r2,r1,_)->  __add r2; __add r1
    |Emubranch(_,r1,_,_)-> __add r1
    |Embbranch(_,r2,r1,_,_)-> __add r2; __add r1
    |Eget_param(_,r1,_)-> __add r1
    |Epush_param(r1,_)->  __add r1
    |_-> ()
  in
  Label.M.iter __fill_hashtable live_map;
  let colors_and_spill = ref colors in
  let __reserve_hw reg acc =
    Register.M.add reg (Reg(reg)) acc
  in
  let initial_cmap = Register.S.fold __reserve_hw Register.allocatable (Register.M.add Register.rsp (Reg(Register.rsp)) (Register.M.add Register.rbp (Reg(Register.rbp)) Register.M.empty)) in
  let find_minimal_cost g =
    let __fold (v:Register.t) e current =
      if (Register.is_hw v) then current
      else (
      let f = try(Hashtbl.find h v) with Not_found -> 0.0 in
      let cost = (f /. Pervasives.float_of_int (Register.S.cardinal (Register.S.union e.prefs e.intfs)))  in
      match current with
      |None->Some(v,cost)
      |Some(v2,c2) when cost<c2 -> Some(v,cost)
      |_->current)
    in
    Register.M.fold __fold g None
  in

  let stream = Stream.from (fun i -> Some(i+1)) in
  let get_spill () = -8*(Stream.next stream) in
  let necessary_space () = 8*Stream.count stream in
  
  let find_minimaldegree k g =
    let __fold_aux vertice edge found =
      if (Register.is_pseudo vertice) then
        (let cardinal = Register.S.cardinal (Register.S.union edge.prefs edge.intfs)  in
         if(cardinal < k) then
           match found with
           |None->Some(vertice, edge, cardinal)
           |Some(vert, e, card)->if(cardinal < card) then Some(vertice, edge, cardinal) else found
         else found)
      else found
    in Register.M.fold __fold_aux g None
  in
  
  let find_nopref_minimaldegree k g =
    let __fold_aux vertice edge found =
      if (Register.is_pseudo vertice) then
        (let cardinal = Register.S.cardinal edge.intfs in
         if(Register.S.is_empty edge.prefs && cardinal < k) then
           match found with
           |None->Some(vertice, cardinal)
           |Some(vert, card)->if(cardinal < card) then Some(vertice, cardinal) else found
         else found)
      else found
    in Register.M.fold __fold_aux g None
  in

  let satisfies_george_criteria k g =
    let __search vertice edge =
      let __test v2 =
        let e2 = Register.M.find v2 g in
        if(Register.is_pseudo v2) then
          let __verify_neighbour vaux =
            let eaux = Register.M.find vaux g in 
            (not((Register.is_hw vaux)||((Register.S.cardinal eaux.prefs) + (Register.S.cardinal eaux.intfs) >= k)))||(Register.S.mem vaux ((*Register.S.union e2.prefs*) e2.intfs))
          in
          Register.S.for_all __verify_neighbour ((*Register.S.union edge.prefs*) edge.intfs) 
        else if (Register.is_pseudo vertice) then
          let __verify_neighbour vaux =
            let eaux = Register.M.find vaux g in 
            (not((Register.is_pseudo vaux)||((Register.S.cardinal eaux.prefs) + (Register.S.cardinal eaux.intfs) >= k)))||(Register.S.mem vaux ((*Register.S.union e2.prefs*) e2.intfs))
          in
          Register.S.for_all __verify_neighbour ((*Register.S.union edge.prefs*) edge.intfs) 
        else false
      in
      try(raise (Edge(vertice, Register.S.find_first __test edge.prefs))) with |Not_found->() 
    in
    Register.M.iter __search g
  in

  let fusionner g v1 v2 =
    Hashtbl.replace h v2 ((Hashtbl.find h v1) +. (Hashtbl.find h v2));
    let e1 = Register.M.find v1 g and e2 = Register.M.find v2 g in
    let interferences = Register.S.remove v1 (Register.S.remove v2 (Register.S.union e1.intfs e2.intfs)) in
    let pref_tmp = Register.S.remove v1 (Register.S.remove v2 (Register.S.union e1.intfs e2.intfs)) in
    let __remove r set =
      Register.S.remove r set
    in
    let preferences = Register.S.fold __remove interferences pref_tmp in
    let g_tmp = Register.M.add v2 {prefs = preferences; intfs = interferences} (Register.M.remove v1 g) in
    let __replace_in_intfs_and_prefs vaux eaux acc =
      let i = if(Register.S.mem v1 eaux.intfs) then
                Register.S.add v2 (Register.S.remove v1 eaux.intfs)
              else eaux.intfs
      in
      let p = if(Register.S.mem v1 eaux.prefs) then
                Register.S.remove v1 (if(Register.S.mem v2 i) then Register.S.remove v2 eaux.prefs else Register.S.add v2 eaux.prefs)
              else
                if(Register.S.mem v2 i) then Register.S.remove v2 eaux.prefs else eaux.prefs
      in
      Register.M.add vaux {prefs = p; intfs = i} acc
    in
    Register.M.fold __replace_in_intfs_and_prefs g_tmp Register.M.empty
  in

  let george_appel card gr =
    let rec simplify k g =
      match find_nopref_minimaldegree k g with
      |None->coalesce k g
      |Some(v,i)-> select k g v
    and coalesce k g =
      try (satisfies_george_criteria k g; freeze k g)
      with Edge(v1,v2)-> (let u1,u2 = if(Register.is_hw v1) then
                                        v2,v1 else v1,v2
                          in
                          let c = simplify k (fusionner g u1 u2) in
                          Pervasives.print_endline ((("copie de "^((u2:>string)^": "))^(u1:>string))^(" -> "^(match (Register.M.find u2 c) with |Reg(r)->(r:>string) |Spilled(n)->"spilled")));
                          Register.M.add u1 (Register.M.find u2 c) c)

    and freeze k g =
      match find_minimaldegree k g with
      |None->spill k g
      |Some(v,e,i)->let __forget_prefs vaux eaux tmp_graph =
                    Register.M.add vaux {prefs = Register.S.remove v eaux.prefs; intfs = eaux.intfs} tmp_graph
                  in
                  simplify k (Register.M.fold __forget_prefs (Register.M.remove v g) (Register.M.singleton v {prefs = Register.S.empty ; intfs = e.intfs}))

    and spill k g =
      match find_minimal_cost g with
      |None-> initial_cmap
      |Some(v,_)-> select k g v

    and select k g v =
      let e = Register.M.find v g in
      let __forget va ea tmp =
        Register.M.add va {prefs = Register.S.remove v ea.prefs; intfs = Register.S.remove v ea.intfs} tmp
      in
      let c = simplify k (Register.M.fold __forget (Register.M.remove v g) Register.M.empty) in
      let possible_color =
        let __find_colors vaux available =
          match (Register.M.find_opt vaux c) with
          |None-> ColorSet.remove (Reg(vaux)) available
          |Some(caux)->ColorSet.remove caux available
        in
        let list = Register.S.fold __find_colors e.intfs !colors_and_spill in
        let __get_pref_color vaux acc =
          match Register.M.find_opt vaux c with
               |None->acc
               |Some(caux)-> (match caux,acc with
                              |Reg(_),_-> if(ColorSet.mem caux list) then raise (FoundReg(caux)) else acc
                              |_,None -> if(ColorSet.mem caux list) then (Some(caux)) else acc
                              |Spilled(_),_->acc )
        in
        let  __print_list (r:Register.t) =
          Pervasives.print_string ((r:>string)^"::")
        in
        let __print_colors_list = function
          |Reg(r)-> __print_list r
          |Spilled(n)-> Pervasives.print_string "Spilled("; Pervasives.print_int n; Pervasives.print_string")::"
        in
        
        Pervasives.print_string (("prefs de ")^((v:>string)^": "));
        Register.S.iter __print_list e.prefs;
        Pervasives.print_string (("  intfs de ")^((v:>string)^": "));
        Register.S.iter __print_list e.intfs;
        Pervasives.print_newline ();
        Pervasives.print_string (("couleurs possibles pour ")^((v:>string)^": "));
        ColorSet.iter __print_colors_list list;
        Pervasives.print_newline ();
        try (match (Register.S.fold __get_pref_color e.prefs None) with
             |Some(coloration) -> (match coloration with
                                   |Reg(_)->coloration
                                   |Spilled(_)-> try (match ColorSet.min_elt list with
                                                      |Reg(pr)->(Reg(pr))
                                                      |_->coloration)
                                                 with Not_found -> coloration)
             |None -> (try ColorSet.min_elt list
                            with Not_found -> let new_color = Spilled(get_spill()) in
                                              colors_and_spill := ColorSet.add new_color !colors_and_spill;
                                              new_color))
        with FoundReg(coloration)->coloration
      in
      
      Pervasives.print_string ((v:>string)^(" -> ")); (match possible_color with |Reg(r) ->  Pervasives.print_endline (r:>string) |Spilled(n)->Pervasives.print_string "Spilled("; Pervasives.print_int n; Pervasives.print_endline ")";);
      Register.M.add v possible_color c
      
    in
    simplify card gr
  in
  let colored_graph = george_appel (ColorSet.cardinal colors) graph in
  (colored_graph,necessary_space ())
                           

let deffun (df:Ertltree.deffun) =
  let live_map = liveness df.fun_body in
  let igraph = make live_map in
  let c,space = color igraph live_map in
  let lookup r =
     try Register.M.find r c with Not_found -> failwith ("Not found : "^ (r :> string)) in
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
                                           add_to_graph l2 (Estore(p1, Register.tmp1, i, l));
                                           Embinop(Mmov, s2, Reg(Register.tmp1), l2);
                              |s1,Reg(p2)->let l2 = Label.fresh() in
                                           add_to_graph l2 (Estore(Register.tmp1, p2, i, l));
                                           Embinop(Mmov, s1, Reg(Register.tmp1), l2);
                              |s1,s2->let l2 = Label.fresh() in
                                      let l3 = Label.fresh() in
                                      add_to_graph l3 (Estore(Register.tmp1, Register.tmp2, i, l));
                                      add_to_graph l2 (Embinop(Mmov, s2, Reg(Register.tmp2), l3));
                                      Embinop(Mmov, s1, Reg(Register.tmp1), l2)
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
                                     add_to_graph l2 (Embinop(Mmov, Reg(Register.tmp2), s2, l));
                                     add_to_graph l3 (Eload(Register.tmp1, i, Register.tmp2, l2));
                                     Embinop(Mmov, s1, Reg(Register.tmp1), l3)
                            )
    |Emunop(op, r, l) -> Emunop(op, lookup r, l)
    |Embinop(op, r1, r2, l) when op = Mmov && (lookup r1)=(lookup r2) -> Egoto(l)
    |Embinop(op, r1, r2, l) when op = Mmov -> let s1 = lookup r1 and s2 = lookup r2 in
                                              (match s1,s2 with
                                               |Spilled(_),Spilled(_)->let l2 = Label.fresh() in
                                                                       add_to_graph l2 (Embinop(Mmov, Reg(Register.tmp1), s2, l));
                                                                       Embinop(Mmov, s1, Reg(Register.tmp1), l2); 
                                               |_,_-> Embinop(Mmov, s1, s2, l)
                                              )

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
         add_to_graph lp (Embbranch(b, Register.tmp1, Register.tmp2, l1, l2));
         add_to_graph lp1 (Embinop(Mmov, Spilled(n2), Reg(Register.tmp2), lp));
         Embinop(Mmov, Spilled(n1), Reg(Register.tmp1), lp1)
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
    |Eget_param(n,r,l) -> (match lookup r with
                          |Reg(p)->Embinop(Mmov, Spilled(n),Reg(p), l)
                          |c->let l2 = Label.fresh() in
                              add_to_graph l2 (Embinop(Mmov, Reg(Register.tmp1), c, l));
                              Embinop(Mmov, Spilled(n), Reg(Register.tmp1), l2)) 
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
       |Ertltree.Econst(_, _, l) -> rewrite_from l
       |Estore(_, _, _, l) -> rewrite_from l
       |Eload(_, _, _, l) -> rewrite_from l
       |Emunop(_, _, l) -> rewrite_from l
       |Embinop(_, _, _, l) -> rewrite_from l
       |Emubranch(_, _, l1, l2) -> rewrite_from l1; rewrite_from l2
       |Embbranch(_, _, _, l1, l2) -> rewrite_from l1; rewrite_from l2
       |Egoto(l) -> rewrite_from l;
       |Ecall(_, _, l) -> rewrite_from l;
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
  Pervasives.print_newline ();
  Pervasives.print_endline (f.fun_name :> string);
  print c
  
let print_ltl fmt (p: Ertltree.file) =
  fprintf fmt "=== PREFS & INTFS GRAPH  =============================@\n";
  Pervasives.print_newline ();
  List.iter print_deffun p.funs;
  Pervasives.print_newline ();
  fprintf fmt "\n=== COLORS ===============================@\n";
  Pervasives.print_newline();
  List.iter print_deffun_colors p.funs;
  Pervasives.print_newline ();
  
