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
    |Emubranch(_,r1,_,_)-> let __fold_outs r g =
                             if (r = r1) then g
                             else
                               Register.M.update r (__add_intf r1) (Register.M.update r1 (__add_intf r) g)
                           in Register.S.fold __fold_outs info.outs graph
    |Embbranch(_,_,r1,_,_)-> let __fold_outs r g =
                               if (r = r1) then g
                               else
                                 Register.M.update r (__add_intf r1) (Register.M.update r1 (__add_intf r) g)
                             in Register.S.fold __fold_outs info.outs graph
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
    if (not(v1=v2)) then
      (let e1 = Register.M.find v1 g and e2 = Register.M.find v2 g in
       Hashtbl.replace costtbl v2 ((Hashtbl.find costtbl v1) +. (Hashtbl.find costtbl v2)); 
       let __fold_replace v edge acc =
         let __map_replace v =
           if (v=v1) then v2 else v
         in
         Register.M.add v {prefs = Register.S.map __map_replace edge.prefs;
                           intfs = Register.S.map __map_replace edge.intfs;} acc
       in
       let g2 = Register.M.remove v1 (Register.M.add v2 {prefs = Register.S.union (Register.S.remove v2 e1.prefs) (Register.S.remove v1 e2.prefs);intfs = Register.S.union (Register.S.remove v2 e1.intfs) (Register.S.remove v1 e2.intfs)} g) in
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
          acc && ((Register.is_pseudo v && ((Register.S.cardinal edge.prefs) + (Register.S.cardinal edge.intfs) < k))||((Register.S.mem v e1.prefs) || (Register.S.mem v e1.intfs)))
        in
        Register.S.fold __fold e2.prefs (Register.S.fold __fold e2.intfs true)
      else
        let __fold v acc =
          let edge = Register.M.find v g in
          acc && ((Register.is_hw v && ((Register.S.cardinal edge.prefs) + (Register.S.cardinal edge.intfs) < k))||((Register.S.mem v e1.prefs) || (Register.S.mem v e1.intfs)))
        in
        Register.S.fold __fold e2.prefs (Register.S.fold __fold e2.intfs true)  
        
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
    |Some(v1,v2)-> let u1,u2 = if (Register.is_hw v2) then v1,v2 else v2,v1 in
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
    |Some(v,_) -> simplify k (Register.M.add v {prefs = Register.S.empty; intfs = (Register.M.find v g).intfs} g)

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
    let color_set = Register.S.fold __find_color edges.prefs (Register.S.fold __find_color edges.intfs colors) in
    let couleur = try (Reg (Register.S.min_elt color_set))
                  with Not_found -> Spilled (8*(get_spill ()))
    in
    
    Register.M.add v couleur c

    in

  let c = simplify (Register.S.cardinal colors) graph in
  (c,8*(necessary_space ()))
  


  
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
  fprintf fmt "=== LTL =============================@\n";
  List.iter print_deffun p.funs;
  fprintf fmt "\n=== COLORS ===============================@\n";
  List.iter print_deffun_colors p.funs;
  
