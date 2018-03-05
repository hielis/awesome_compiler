open Lifetime;;
open Ertltree;;
open Ertl;;

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

open Format
open Pp
   
let print ig =
  Register.M.iter (fun r arcs ->
    Format.printf "%s: prefs=@[%a@] intfs=@[%a@]@." (r :> string)
      Register.print_set arcs.prefs Register.print_set arcs.intfs) ig

let print_deffun f =
  print (make (liveness f.fun_body))
  
let print_ltl fmt p =
  fprintf fmt "=== LTL =============================@\n";
  List.iter print_deffun p.funs 
  
