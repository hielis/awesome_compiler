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

(*let colors = Register.allocatable;;*)

exception Edge of Register.t * Register.t
                
let color graph live_map =
  let h = Hashtbl.create 129 in

  let __fill_hashtable lbl info col =
    let __add (reg: Register.t) acc =
      (*Pervasives.print_endline (reg:>string);*)
      match Hashtbl.find_opt h reg with
      |None-> (Hashtbl.add h reg 1.0; if (Register.is_hw reg) then Register.S.add reg acc else acc)
      |Some(i)-> Hashtbl.replace h reg (i +. 1.0); acc
    in
    match info.instr with
    |Econst(_,r1,_)-> __add r1 col
    |Eload(r2,_,r1,_)-> __add r2 (__add r1 col)
    |Estore(r2,r1,_,_)-> __add r2 (__add r1 col)
    |Emunop(_,r1,_)->  __add r1 col
    |Embinop(_,r2,r1,_)->  __add r2 (__add r1 col)
    |Emubranch(_,r1,_,_)-> __add r1 col
    |Embbranch(_,r2,r1,_,_)-> __add r2 (__add r1 col)
    |Eget_param(_,r1,_)-> __add r1 col
    |Epush_param(r1,_)->  __add r1 col
    |_-> col
  in
  let colors = ref (Label.M.fold __fill_hashtable live_map Register.S.empty) in  
  (*let __reserve_hw reg acc =
    Register.M.add reg (Reg(reg)) acc
  in
  let initial_cmap = Register.S.fold __reserve_hw !colors Register.M.empty in*)
  let find_minimal_cost g =
    (*Pervasives.print_newline ();*)
    let __fold (v:Register.t) e current =
      (*Pervasives.print_endline (v:>string);*)
      let f = try(Hashtbl.find h v) with Not_found -> 0.0 in
      let cost = (f /. Pervasives.float_of_int (Register.S.cardinal (Register.S.union e.prefs e.intfs)))  in
      match current with
      |None->Some(v,cost)
      |Some(v2,c2) when cost<c2 -> Some(v,cost)
      |_->current
    in
    Register.M.fold __fold g None
  in

  let stream = Stream.from (fun i -> Some(i+1)) in
  let get_spill () = -8*(Stream.next stream) in
  let necessary_space () = 8*Stream.count stream in
  
  let find_minimaldegree k g =
    let __fold_aux vertice edge found =
      let cardinal = Register.S.cardinal (Register.S.union edge.prefs edge.intfs)  in
      if(cardinal < k) then
        match found with
        |None->Some(vertice, edge, cardinal)
        |Some(vert, e, card)->if(cardinal < card) then Some(vertice, edge, cardinal) else found
      else found
    in Register.M.fold __fold_aux g None
  in
  
  let find_nopref_minimaldegree k g =
    let __fold_aux vertice edge found =
      let cardinal = Register.S.cardinal edge.intfs in
      if(Register.S.is_empty edge.prefs && cardinal < k) then
        match found with
        |None->Some(vertice, cardinal)
        |Some(vert, card)->if(cardinal < card) then Some(vertice, cardinal) else found
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
            (not((Register.is_hw vaux)||((Register.S.cardinal eaux.prefs) + (Register.S.cardinal eaux.intfs) >= k)))||(Register.S.mem vaux (Register.S.union e2.prefs e2.intfs))
          in
          Register.S.for_all __verify_neighbour (Register.S.union edge.prefs edge.intfs) 
        else
          let __verify_neighbour vaux =
            let eaux = Register.M.find vaux g in 
            (not((Register.is_pseudo vaux)||((Register.S.cardinal eaux.prefs) + (Register.S.cardinal eaux.intfs) >= k)))||(Register.S.mem vaux (Register.S.union e2.prefs e2.intfs))
          in
          Register.S.for_all __verify_neighbour (Register.S.union edge.prefs edge.intfs) 
      
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
      with Edge(v1,v2)-> (let u1,u2 = if(Register.is_pseudo v2 || v1=Register.rax) then
                                        v2,v1 else v1,v2
                          in
                          colors := Register.S.remove u1 !colors;
                          let c = simplify k (fusionner g u1 u2) in
                          (*Pervasives.print_endline ((("copie de "^((u2:>string)^": "))^(u1:>string))^(" -> "^(match (Register.M.find u2 c) with |Reg(r)->(r:>string) |Spilled(n)->"spilled")));*)
                          (*eventuellement remettre u1 en couleur dispo*)
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
      |None-> (*initial_cmap*)Register.M.empty
      |Some(v,_)-> select k g v

    and select k g v =
      let e = Register.M.find v g in
      let __forget va ea tmp =
        Register.M.add va {prefs = Register.S.remove v ea.prefs; intfs = Register.S.remove v ea.intfs} tmp
      in
      colors := Register.S.remove v !colors;
      let c = simplify k (Register.M.fold __forget (Register.M.remove v g) Register.M.empty) in
      if(Register.is_hw v) then colors := Register.S.add v !colors else ();
      let possible_color =
        let __find_colors vaux available =
          match (Register.M.find_opt vaux c) with
          |None->(*if(Register.is_hw vaux) then*) Register.S.remove vaux available (*else available*)
          |Some(caux)->(match caux with
                       |Reg(r) -> Register.S.remove r available
                       |_->available)
        in
        let list = Register.S.fold __find_colors e.intfs !colors in
        let __get_pref_color vaux =
          match Register.M.find_opt vaux c with
               |None->false
               |Some(caux)-> (match caux with
                             |Reg(r) -> Register.S.mem r list
                             |_-> false)
        in
        (*let rec __print_list (r:Register.t) =
        Pervasives.print_string ((r:>string)^"::")
        in
        Pervasives.print_string (("prefs de ")^((v:>string)^": "));
        Register.S.iter __print_list e.prefs;
        (*Pervasives.print_newline (); *)
        Pervasives.print_string (("  intfs de ")^((v:>string)^": "));
        Register.S.iter __print_list e.intfs;
        Pervasives.print_newline ();
        Pervasives.print_string (("couleurs possibles pour ")^((v:>string)^": "));
        Register.S.iter __print_list list;
        Pervasives.print_newline ();*)
        try (let reg = (Register.S.find_first __get_pref_color e.prefs)
             in Register.M.find reg c)
        with Not_found -> if(Register.S.mem v list) then Reg(v)
                          else (try Reg(Register.S.choose list)
                                with Not_found -> Spilled(get_spill()))
      in
      
      (*Pervasives.print_endline ((v:>string)^(" -> "^(match possible_color with |Reg(r)->(r:>string) |Spilled(n)->"spilled")));*)
      Register.M.add v possible_color c
      
    in
    simplify card gr
  in
  let colored_graph = george_appel (Register.S.cardinal !colors) graph (*(Register.S.fold Register.M.remove colors graph)*) in
  (colored_graph,necessary_space ())
                           
                                  
    
  
(*
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
    |Some(v1,v2)-> let u1,u2 = if ((Register.is_hw v1)&&(v2<>Register.rax)) then v2,v1 else v1,v2 in
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
      let __fold_minimal v eqdge acc =
        let c = (Hashtbl.find costtbl v) /. (Pervasives.float_of_int ((Register.S.cardinal edge.prefs) + (Register.S.cardinal edge.intfs))) in
        match acc with
        |None->Some(v,c)
        |Some(v2,c2)-> if (c<c2) then Some(v,c) else acc
      in
      match Register.M.fold __fold_minimal g None with
      |None->failwith "Should be some dead code"
      |Some(v,_)->select k g v

  and select k g v =
    let edges = Register.M.find v g in
    let __fold_remove vaux edge acc =
      Register.M.add vaux {prefs = Register.S.remove v edge.prefs; intfs = Register.S.remove v edge.intfs} acc
    in
    
    let c = simplify k (Register.M.fold __fold_remove (Register.M.remove v g) Register.M.empty) in
    let __find_color w available_colors =
      try (match (Register.M.find w c) with
           |Reg(r)->Register.S.remove r available_colors
           |Spilled(_)->available_colors)
      with Not_found -> available_colors
    in
    let color_set = (Register.S.fold __find_color edges.intfs colors) in
    let couleur = try (Reg (if (Register.S.mem v color_set) then v else Register.S.min_elt color_set))
                  with Not_found -> Spilled (-8*(get_spill ()))
    in
    Register.M.add v couleur c

  in
  let c = simplify (Register.S.cardinal colors) graph in
  let crax = Register.M.find (Register.rax) c in
  let __fold_swap v col acc =
    match col with
    |Reg(p) when p=Register.rax -> Register.M.add v crax acc
    |a when a=crax->Register.M.add v (Reg(Register.rax)) acc
    |_->Register.M.add v col acc
  in
  (Register.M.fold __fold_swap c Register.M.empty,8*(necessary_space ()))
 *)


let deffun (df:Ertltree.deffun) =
  let live_map = liveness df.fun_body in
  let igraph = make live_map in
  let c,space = color igraph live_map in
  let lookup r = 
     Register.M.find r c in
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
                                           add_to_graph l2 (Estore(p1, Register.tmp1, i, l3));
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
  
