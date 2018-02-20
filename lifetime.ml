open Ertltree;;
open Register;;

type live_info = {
         instr: Ertltree.instr;
          succ: Label.t list;    (* successeurs *)
  mutable pred: Label.set;       (* prédécesseurs *)
          defs: Register.set;    (* définitions *)
          uses: Register.set;    (* utilisations *)
  mutable  ins: Register.set;    (* variables vivantes en entrée *)
  mutable outs: Register.set;    (* variables vivantes en sortie *)
  };;

module S = Set.Make(Register.S)

               

let liveness graph =
  let life_table = Hashtbl.create (Label.M.cardinal graph) in
  let fill_table lbl i =
    let s = succ i and (def_set, use_set) = def_use i in
    Hashtbl.add life_table lbl { instr = i;
                                 succ  = s;
                                 pred  = Label.S.empty ;
                                 defs  = Register.S.of_list(def_set) ;
                                 uses  = Register.S.of_list(use_set) ;
                                 ins   = Register.S.empty ;
                                 outs  = Register.S.empty ; };
  in
  Label.M.iter fill_table graph;

  let fill_pred key e =
    let __iter l =
      let p = Hashtbl.find life_table l in
      p.pred<-Label.S.add l p.pred;
      Hashtbl.replace life_table l p;
    in
    List.iter __iter e.succ
  in
  Hashtbl.iter fill_pred life_table;

  let to_key_list m =
    let __map (l,i) = l in
    List.rev_map __map (Label.M.bindings m)
  in
  let rec kildall = function
    |[]-> ()
    |t::q-> let e = Hashtbl.find life_table t in
            let old_ins = e.ins in
            let __get_ins s =
              (Hashtbl.find life_table s).ins
            in
            e.outs <- S.fold (Register.S.fold (Register.S.add)) (S.of_list (List.rev_map __get_ins e.succ)) (Register.S.empty);
            e.ins <- Register.S.union (e.uses) (Register.S.diff (e.outs) (e.defs));
            Hashtbl.replace life_table t e;
            let ws = if (Register.S.equal e.ins old_ins) then
                       q
                     else
                       List.fold_right (List.cons) (Label.S.elements e.pred) q
            in
            kildall ws
  in
  kildall (to_key_list graph);

  Hashtbl.fold (Label.M.add) life_table (Label.M.empty)
  
;;

open Format
open Pp

let print_set = Register.print_set;;

let print_live_info fmt li =
  fprintf fmt "d={%a}@ u={%a}@ i={%a}@ o={%a}"
    print_set li.defs print_set li.uses print_set li.ins print_set li.outs
;;

let print_graph fmt =
  let visit f g entry =
    let visited = Hashtbl.create 97 in
    let rec visit l =
      if not (Hashtbl.mem visited l) then begin
          Hashtbl.add visited l ();
          let i = Label.M.find l g in
          f l i;
          List.iter visit (i.succ)
        end
    in
    visit entry
  in
  visit (fun l i -> fprintf fmt "%a: %a@ %a\n" Label.print l Ertltree.print_instr i.instr print_live_info i)
;;

let print_deffun fmt f =
  fprintf fmt "%s(%d)@\n" f.fun_name f.fun_formals;
  fprintf fmt "  @[";
  fprintf fmt "entry : %a@\n" Label.print f.fun_entry;
  fprintf fmt "locals: @[%a@]@\n" Register.print_set f.fun_locals;
  print_graph fmt (liveness f.fun_body) f.fun_entry;
  fprintf fmt "@]@."

let print_file fmt p =
  fprintf fmt "=== ERTL + live_info  =================================================@\n";
  List.iter (print_deffun fmt) p.funs
