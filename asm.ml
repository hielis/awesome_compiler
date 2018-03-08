open X86_64
open Ltltree

let visited = Hashtbl.create 17
type instr = Code of X86_64.text | Label of Label.t
let code = ref []
let emit l i = code := Code i :: Label l :: !code
let emit_wl i = code := Code i :: !code
let labels = Hashtbl.create 17
let useful = Hashtbl.create 17
let need_label l = Hashtbl.add labels l ()
let weneed_label l = Hashtbl.add useful l ()


let register (r : Register.t) = match (r :> string) with
  | "%rax" -> X86_64.rax
  | "%rbx" -> X86_64.rbx
  |"%rcx" -> X86_64.rcx
  |"%rdx" -> X86_64.rdx
  |"%rsi" -> X86_64.rsi
  |"%rdi" -> X86_64.rdi
  |"%rbp" -> X86_64.rbp
  |"%rsp" -> X86_64.rsp
  |"%r8" -> X86_64.r8
  |"%r9" -> X86_64.r9
  |"%r10" -> X86_64.r10
  |"%r11" -> X86_64.r11
  |"%r12" -> X86_64.r12
  |"%r13" -> X86_64.r13
  |"%r14" -> X86_64.r14
  |"%r15"  -> X86_64.r15
  |_ -> failwith ("Unknown register :" ^ (r :> string))

let operand = function
  |Reg(r) -> reg (register r)
  |Spilled(n) -> (ind ~ofs:n (rbp))


let rec lin g l =
  if not (Hashtbl.mem visited l) then begin
    Hashtbl.add visited l ();
    instr g l (Label.M.find l g)
  end else begin
    need_label l;
    weneed_label l;
    emit_wl (jmp (l :> string))
  end

and instr g l = function
  |Econst (n, r, l1) ->
      emit l (movq (imm32 n) (operand r)); lin g l1
  |Emunop(uop, op, l1) ->
    (match uop with
      |Maddi(c) -> emit l (addq (imm32 c) (operand op))
      |_ ->
        let r = operand op in
        emit l (movq r (reg X86_64.r11));
        (match uop with
         |Msetei(c) ->
           emit_wl (cmpq (imm32 c) (reg X86_64.r11));
           emit_wl (sete (reg X86_64.r11b));
         |Msetnei(c) ->
           emit_wl (cmpq (imm32 c) (reg X86_64.r11));
           emit_wl (setne (reg X86_64.r11b));
         |_-> failwith "dead code"
        );
        emit_wl (movzbq (reg (r11b))  (r15));
        emit_wl (movq (reg r15) (r));
    );
    lin g l1
  |Embinop(bop, op1, op2, l1) ->
    (match bop with
     |Msete | Msetne | Msetl | Msetle | Msetg |Msetge -> 
       let a w =
         (match bop with
          |Msete -> sete w
          |Msetne -> setne w
          |Msetl -> setl w
          |Msetle -> setle w
          |Msetg -> setg w
          |Msetge -> setge w
          |_ -> failwith "deadcode"
         )
       in
       let r1 = operand op1 in
       let r2 = operand op2 in
       emit l (movq r2 (reg X86_64.r11));
       emit_wl (cmpq r1 (reg X86_64.r11));
       emit_wl (a (reg X86_64.r11b));
       emit_wl (movzbq  (reg X86_64.r11b) (r15));
       emit_wl (movq (reg r15) (r2));
     |_ ->
       let a w1 w2=
         (match bop with
          |Mmov -> movq w1 w2
          |Madd -> addq w1 w2
          |Msub -> subq w1 w2
          |Mmul -> imulq w1 w2
          |Mdiv -> idivq w1
          |_-> failwith "dead code"
         )
       in
       emit l (a (operand op1) (operand op2))
    );
    lin g l1
  |Epush(op, l1) -> emit l (pushq (operand op)); lin g l1
  |Eload(r1, n, r2, l1)-> emit l (movq (ind ~ofs:n (register r1)) (reg (register r2))); lin g l1
  |Estore(r1, r2, n, l1)-> emit l (movq (reg (register r1)) (ind ~ofs:n (register r2))); lin g l1
  |Egoto(l1) -> (match (Hashtbl.find_opt visited l1) with 
                 |None -> emit l (label (l1 :> string))
                 |Some _ -> weneed_label l1;
                   emit l (jmp (l1 :> string))
                );
                  lin g l1
  |Ereturn -> emit l (ret);
  |Emubranch(mb, r, l1, l2) -> 
    (match mb with
    |Mjz -> emit l (cmpq (imm 0) (reg (register r)));
            (match (Hashtbl.find_opt visited l1) with
            |None -> weneed_label l1;
              emit_wl (jz (l1 :> string)); lin g l2; lin g l1;
            |Some _-> weneed_label l2;
              emit_wl (jnz (l2 :> string)); lin g l1; lin g l2;
            );
    |Mjnz -> emit l (cmpq (imm 0) (reg (register r)));
            (match (Hashtbl.find_opt visited l1) with
            |None -> weneed_label l1;
              emit_wl (jnz (l1 :> string)); lin g l2; lin g l1;
            |Some _-> weneed_label l2;
              emit_wl (jz (l2 :> string)); lin g l1; lin g l2;
            )
    |Mjlei(c) -> emit l (cmpq (imm32 c) (reg (register r)));
            (match (Hashtbl.find_opt visited l1) with
            |None -> weneed_label l1;
              emit_wl (jle (l1 :> string)); lin g l2; lin g l1;
            |Some _-> weneed_label l2;
              emit_wl (jg (l2 :> string)); lin g l1; lin g l2;
            )
    |Mjgi(c) -> emit l (cmpq (imm32 c) (reg (register r)));
                (match (Hashtbl.find_opt visited l1) with
                 |None -> weneed_label l1;
                   emit_wl (jg (l1 :> string)); lin g l2; lin g l1;
                 |Some _-> weneed_label l2;
                   emit_wl (jle (l2 :> string)); lin g l1; lin g l2;
            )
    );
  |Embbranch(mb, r1, r2, l1, l2) ->
    emit l (cmpq (reg (register r1))  (reg (register r2)));
    (match (Hashtbl.find_opt visited l1) with
    |Some _ ->
      (match mb with
       |Mjl -> weneed_label l2;
         emit_wl (jge (l2 :> string)); lin g l1; lin g l2;
       |Mjle -> weneed_label l2;
         emit_wl (jg (l2 :> string)); lin g l1; lin g l2;
      )
    |None ->
      (match mb with
       |Mjl -> weneed_label l1;
         emit_wl (jl (l1 :> string)); lin g l2; lin g l1;
       |Mjle -> weneed_label l1;
         emit_wl (jle (l1 :> string)); lin g l2; lin g l1;
      )
    )
  |Ecall(i, l1) -> emit l (call (i:>string)); lin g l1
  |Epop(r, l1) -> emit l (popq (register r)); lin g l1

let deffun (df:Ltltree.deffun) =
  code := [];
  lin df.fun_body df.fun_entry;
  let __aux a = function
    |Code(i) -> i ++ a
    |Label(s)->
      if (Hashtbl.mem useful s) then
      (label (s :> string)) ++ a
      else a
  in
  (inline (df.fun_name ^  ":")) ++ (List.fold_left __aux (nop) (!code))
;;

let program f =
  let __aux a b = a++(deffun b) in
{
  text = (inline "        .globl main")++(inline "\n ") ++(List.fold_left __aux (nop) f.funs) ;
  data = nop
}
;;

