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
      Register.M.update r2 (__add_pref r1) (Register.M.update r1 (__aux r2) graph)
    |_ -> graph
  in
  let __fold_intf key info graph =
    let __add_intf reg = function
      |None->Some({prefs = Register.S.empty; intfs = Register.S.singleton})
      |Some(arc) -> Some({prefs = Register.S.remove reg arc.prefs; Register.S.add reg arc.intfs})
    in
    match info.instr with
    |Embinop(b,r1,r2,lbl) when (b = Mmov && r1<>r2) ->
      let __fold_outs r g =
        match r with
        |r2-> g
        |_-> Register.M.update r (__add_intf r1) (Register.M.update r1 (__aux r) g)
      in
      Register.S.fold __fold_outs info.outs graph
    |_-> let _fold_outs r g = Register.M.update r (__add_intf r1) (Register.M.update r1 (__aux r) g) in
         Register.S.fold __fold_outs info.outs graph
  in
  Register.M.fold __fold_intf live_map (Register.M.fold __fold_pref live_map Register.M.empty)

let print ig =
  Register.M.iter (fun r arcs ->
    Format.printf "%s: prefs=@[%a@] intfs=@[%a@]@." (r :> string)
      Register.print_set arcs.prefs Register.print_set arcs.intfs) ig
