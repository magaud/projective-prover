open Pp
open Ppconstr
open EConstr

let message = "Hello world!"

(** Coq constants useful in the tactic *)
            
let coq_eq () = let x = Coqlib.lib_ref "core.eq.type" in
                EConstr.of_constr (Globnames.printable_constr_of_global x)

let coq_nil () = let x = Coqlib.find_reference "Coq" ["Coq";"Init";"Datatypes"] "nil" in  
                EConstr.of_constr (Globnames.printable_constr_of_global x)

let coq_cons () = let x = Coqlib.find_reference "Coq" ["Coq";"Init";"Datatypes"] "cons" in 
                  EConstr.of_constr (Globnames.printable_constr_of_global x)
                  
let coq_O () = let x = Coqlib.find_reference "Coq" ["Coq";"Init";"Datatypes"] "O" in  
                EConstr.of_constr (Globnames.printable_constr_of_global x)

let coq_S () = let x = Coqlib.find_reference "Coq" ["Coq";"Init";"Datatypes"] "S" in  
                EConstr.of_constr (Globnames.printable_constr_of_global x)

let coq_point () = 
  let x = Coqlib.find_reference "Tuto0" ["Tuto0";"basic_matroid_list"] "Point" in 
  EConstr.of_constr (Globnames.printable_constr_of_global x)
(* to be fixed using lib_ref ? *)

let coq_rk () =
  let x = Coqlib.find_reference "Tuto0" ["Tuto0";"basic_matroid_list"] "rk" in
  EConstr.of_constr (Globnames.printable_constr_of_global x)

(* the following 2 variables will be instantiated by the arguments of the tactic *)             
let dimension = 3
let layer = 1
          
let rec list_of_points gl env sigma l =
  match l with
    [] -> []
  | (x,t)::xts -> if Tacmach.New.pf_conv_x gl t (coq_point ())
                  then x::(list_of_points gl env sigma xts)
                  else (list_of_points gl env sigma xts)
        
let rec mk_string l =
  match l with [] -> ""
             | x::xs -> x^" "^(mk_string xs)
    (*                  
let text_to_send gl env sigma l =
  "context\n  dimension "^(string_of_int dimension)^"\n"^
    "  layers "^(string_of_int layer)^"\nendofcontext\n"^"layer 0\n"^
      " points\n"^
(mk_string (List.map Names.Id.to_string (List.rev (list_of_points gl env sigma l))))^"\n"^
    " hypotheses\n"^
      " conclusion\n"^
        (*(interp_rk gl env sigma concl)^(string_of_int (interp_nat gl env sigma *)
        "endoflayer\n"^
          "conclusion\n"^
      "end"
     *)
                      
let send_text text_to_send =
  let file_name = "blabla" in 
  let c = open_out file_name in
  let _ = output_string c text_to_send in
  let _ = flush c in
  let _ = close_out c in 
  Unix.system ("/Users/magaud/prouveur-pascal/bin/main "^file_name)

let rec aff gl env sigma l =
  match l with
    (x,y)::xs ->
    (Feedback.msg_notice (str "*");
     Feedback.msg_notice (pr_id x);
     Feedback.msg_notice (Printer.pr_econstr_env env sigma y);
     Feedback.msg_notice (str "*\n");
    aff gl env sigma xs)
  | [] -> (Feedback.msg_notice (str "end"))


let rec show_points gl env sigma l =
  match l with
    [] -> Feedback.msg_notice (str "\n")
  | x::xs -> (Feedback.msg_notice (pr_id x); show_points gl env sigma xs)
(* (rk (A :: B :: C :: nil) = 3) *)

let rec points gl env sigma l =
  let _ = (Feedback.msg_notice (str "le terme en entree")) in 
  let _ = (Feedback.msg_notice (Printer.pr_econstr_env env sigma (l))) in 
  let (f,a) = destApp sigma l in
  let _ = (Feedback.msg_notice (Printer.pr_econstr_env env sigma (f))) in
  let _ = (Feedback.msg_notice (str "blabla")) in 
  let _ = (Feedback.msg_notice (Printer.pr_econstr_env env sigma (a.(0)))) in
(*  let _ = (Feedback.msg_notice (Printer.pr_econstr_env env sigma (a.(1)))) in
  let _ = (Feedback.msg_notice (Printer.pr_econstr_env env sigma (a.(2)))) in*)
  if Tacmach.New.pf_conv_x gl f (coq_nil()) then []
  else if Tacmach.New.pf_conv_x gl f (coq_cons())
  then (*let _ = (Feedback.msg_notice (Printer.pr_econstr_env env sigma (a.(1)))) in *)
            a.(1)::(points gl env sigma a.(2))
       else let _ = (Feedback.msg_notice (Printer.pr_econstr_env env sigma (f))) in failwith "erreur liste"
(* cons A (cons B (cons C  nil)*)
       
let interp_rk gl env sigma c =
  let (g,b) = destApp sigma c in
       if Tacmach.New.pf_conv_x gl g (coq_rk ())
       then let _ = (Feedback.msg_notice (str "reconnaitre eq + rk : ok")) in 
            let  args = (Array.to_list b) in
            let _ = (Feedback.msg_notice (str ("args of rk : ok length = "^(string_of_int (List.length args))))) in
            let p = points gl env sigma (List.hd args) in
            let _ = (Feedback.msg_notice (str "alles gut")) in
            let _ = (Feedback.msg_notice (str (mk_string (List.map (fun x -> Names.Id.to_string (destVar sigma x)) p))))
            in (mk_string (List.map (fun x -> Names.Id.to_string (destVar sigma x)) p))
       else failwith "not a rank term" (*(Feedback.msg_notice (str "pas rk"))*)
 

let rec interp_nat gl env sigma c =
 let _ = (Feedback.msg_notice (str "entier en entree")) in 
 let _ = (Feedback.msg_notice (Printer.pr_econstr_env env sigma (c))) in
 if Tacmach.New.pf_conv_x gl c (coq_O ())
 then 0
 else let (f,a) = destApp sigma c in
      if  Tacmach.New.pf_conv_x gl f (coq_S ())
      then (1+(interp_nat gl env sigma a.(0)))
      else failwith "error: interp_nat"
   
let interp_hyp_or_concl gl env sigma c =
  let _ = (Feedback.msg_notice (str "interp_hyp_or_concl")) in
  let _ =   (Feedback.msg_notice (Printer.pr_econstr_env env sigma c)) in 
  if isApp sigma c then 
    let (f,a) = destApp sigma c in
    if Tacmach.New.pf_conv_x gl f (coq_eq ())
    then 
      let _ =   (Feedback.msg_notice (Printer.pr_econstr_env env sigma (a.(0)))) in 
      let _ =   (Feedback.msg_notice (Printer.pr_econstr_env env sigma (a.(1)))) in
      let _ =   (Feedback.msg_notice (Printer.pr_econstr_env env sigma (a.(2)))) in
      let r = interp_rk gl env sigma a.(1) in
      let n = interp_nat gl env sigma a.(2) in
      r^" : "^(string_of_int n)
    else
      ""
  else ""

let rec myflatten l = 
          match l with
            [] -> ""
          | x::xs -> if x="" then myflatten xs else x^"\n"^(myflatten xs);;
                           

            let pprove () =
  let _ = Feedback.msg_notice (str "proving...") in
  Proofview.Goal.enter begin fun gl ->
             let env = Proofview.Goal.env gl in
             let sigma = Tacmach.New.project gl in
             let concl = Tacmach.New.pf_concl gl in
             let raw_list = Tacmach.New.pf_hyps_types gl (*(Id.t * types) list*) in
             let points = (mk_string (List.map Names.Id.to_string (List.rev (list_of_points gl env sigma raw_list)))) in 
             let ranks = myflatten (List.map (fun (i,t) -> interp_hyp_or_concl gl env sigma t) raw_list) in
             let conc = (interp_hyp_or_concl gl env sigma concl) in 
             let text_to_send =
               "context\n  dimension "^(string_of_int dimension)^"\n"^
                 "  layers "^(string_of_int layer)^"\nendofcontext\n"^"layer 0\n"^
                   " points\n"^
                     points^"\n"^
                       " hypotheses\n"^
                         ranks^
                         " conclusion\n"^
                           conc^"\n"^
                           "endoflayer\n"^
                             "conclusion\n"^
                               conc^"\n"^
                               "end" in 

               
            (* let list_points = (list_of_points gl env sigma raw_list) in
             let list_ranks = ["";""] in *)
             let _ = aff gl env sigma raw_list      in (*        (Feedback.msg_notice (Printer.pr_named_decl env sigma lh);*)
             let _ = show_points gl env sigma (list_of_points gl env sigma raw_list) in
             (*let _ = interp_rk gl env sigma concl in*)
             (*let n = let (f,a)= destApp sigma concl in a.(2) in 
             let v = interp_nat gl env sigma n in
              let _ =  (Feedback.msg_notice (str (string_of_int v))) in*)
             let _ =  (Feedback.msg_notice (str (interp_hyp_or_concl gl env sigma concl))) in
             let _ = send_text text_to_send in
             Tacticals.New.tclIDTAC
             end

  (*
context
      dimension 3
      layers 1
endofcontext
layer 0
  points
    A B C Ap Bp Cp M N P 
  hypotheses
    A B C : 3
    Ap Bp Cp : 3
    A B C Ap Bp Cp : 4
    M A B C : 3
    N A B C : 3
    P A B C : 3
    M Ap Bp Cp : 3
    N Ap Bp Cp : 3
    P Ap Bp Cp : 3
    M N : 2
    M P : 2
    N P : 2
  conclusion
    M N P : 2
endoflayer
  conclusion
    M N P : 2
end
   *)
