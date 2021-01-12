open Pp
open Ppconstr
open EConstr
(*open Libnames
open Names
open CErrors*)

let debug = ref false
          
let message = "Hello world!"

(** Coq constants useful in the tactic *)
let find_reference = Coqlib.find_reference [@ocaml.warning "-3"]
                   
let coq_eq () = let x = Coqlib.lib_ref "core.eq.type" in
                EConstr.of_constr (Globnames.printable_constr_of_global x)

let coq_nil () = let x = find_reference "Coq" ["Coq";"Init";"Datatypes"] "nil" in  
                EConstr.of_constr (Globnames.printable_constr_of_global x)

let coq_cons () = let x = find_reference "Coq" ["Coq";"Init";"Datatypes"] "cons" in 
                  EConstr.of_constr (Globnames.printable_constr_of_global x)
                  
let coq_O () = let x = find_reference "Coq" ["Coq";"Init";"Datatypes"] "O" in  
                EConstr.of_constr (Globnames.printable_constr_of_global x)

let coq_S () = let x = find_reference "Coq" ["Coq";"Init";"Datatypes"] "S" in  
                EConstr.of_constr (Globnames.printable_constr_of_global x)

let coq_point () = 
  let x = find_reference "Tuto0" ["Tuto0";"basic_matroid_list"] "Point" in 
  EConstr.of_constr (Globnames.printable_constr_of_global x)
(* to be fixed using lib_ref ? *)

let coq_rk () =
  let x = find_reference "Tuto0" ["Tuto0";"basic_matroid_list"] "rk" in
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

(*let my_vernac_flag = "deprecated", Attributes.VernacFlagList ["", Attributes.VernacFlagEmpty]*)
                            
(*let vernac_require' from export qidl =

  Attributes.unsupported_attributes [Attributes.vernac_monomorphic_flag];
  Vernacentries.vernac_require from export qidl*)
(*
let err_notfound_library ?from qid =
  let prefix = match from with
  | None -> str "."
  | Some from ->
    str " with prefix " ++ DirPath.print from ++ str "."
  in
  let bonus =
    if !Flags.load_vos_libraries then " (While searching for a .vos file.)" else "" in
  user_err ?loc:qid.CAst.loc ~hdr:"locate_library"
     (strbrk "Unable to locate library " ++ pr_qualid qid ++ prefix ++ str bonus)

let err_unmapped_library ?from qid =
  let dir = fst (repr_qualid qid) in
  let prefix = match from with
    | None -> str "."
    | Some from ->
       str " and prefix " ++ DirPath.print from ++ str "."
  in
  user_err ?loc:qid.CAst.loc
           ~hdr:"locate_library"
    (strbrk "Cannot find a physical path bound to logical path matching suffix " ++
       DirPath.print dir ++ prefix)
  
let my_vernac_require from import qidl =
  let lib_resolver = Loadpath.try_locate_absolute_library in
  let root = match from with
    | None -> None
    | Some from ->
       let (hd, tl) = Libnames.repr_qualid from in
       Some (Libnames.add_dirpath_suffix hd tl)
  in
  let locate qid =
    let open Loadpath in
    let warn = not !Flags.quiet in
    match locate_qualified_library ?root ~warn qid with
    | Ok (_,dir,f) -> dir, f
    | Error LibUnmappedDir -> err_unmapped_library ?from:root qid
    | Error LibNotFound -> err_notfound_library ?from:root qid
  in let modrefl = List.map locate qidl 
  in Library.require_library_from_dirpath ~lib_resolver modrefl import
 *)
let send_text name text_to_send =
  let already_exists = Sys.file_exists ("theories/pprove_"^name^".vo") in
  if already_exists
  then let _ = Feedback.msg_notice (str ("Already computed and ready to be reused. In case it fails, remove the file theories/pprove_"^name^".vo."))
       in Tacticals.New.tclIDTAC
  else
  (* let _ = Unix.chdir ("theories") in *)
  let input_file = "theories/draft_"^name in
  let result_file = "theories/pprove_"^name in 
  let c = open_out input_file in
  let _ = output_string c text_to_send in
  let _ = flush c in
  let _ = close_out c in
  let prover_name = "/Users/magaud/MatroidIncidenceProver/matroidbasedIGprover/matroid_C_Coq/DevC/bin/main" in
(* alternative prover available:  /Users/magaud/MatroidIncidenceProver/matroidbasedIGprover/matroid_C_Coq/DevC/bin/main *)
  (*let prover_name = "/Users/magaud/prouveur-pascal/bin/main" in *)
  let _ = Unix.system (prover_name^" "^input_file^ " > /dev/null 2> /dev/null") in 
  (*let cmd = Filename.quote_command "echo" ~stdout:(result_file^".v") ["Require Import lemmas_automation_g."] in
  let _ = Unix.system(cmd) in*)
  let _ = Unix.system ("cat "^input_file^".v >> "^result_file^".v") in

  let _ = Unix.system("grep Lemma "^result_file^".v | awk '{print $2}' > tgvqsd48") in
  let _ = Unix.system("tail -1 tgvqsd48 > tgvqsd49") in 
  let c = open_in "tgvqsd49" in
  let lemma_name = input_line c (*"LP1P2P3" *) in
  let _ = if !debug then (Feedback.msg_notice (str lemma_name)) in 
  let _ = Unix.system("rm -f tgvqsd48") in 
  let _ = Unix.system("rm -f tgvqsd49") in 
  (*  let _ = Unix.system ("echo Hint Resolve "^lemma_name^" : ranks. >> "^result_file^".v") in*)

  (*  let _  = Unix.chdir("..") in *)
  let cmd = Filename.quote_command "coqc" ["-q"; "-I"; "src"; "-R"; "theories"; "Tuto0";(result_file^".v")] in
  let _ = Unix.system(cmd) in
  let _ = Unix.system("ls "^result_file^".v") in
  let _ = Unix.system("ls "^result_file^".vo") in
  let (a,b) = match (String.split_on_char '/' result_file) with [a;b] -> (a,b) | _ -> failwith "erreur" in
  let _ = Unix.system("rm -f "^input_file) in
  let _ = Unix.system("rm -f "^input_file^".out") in
  let _ = Unix.system("rm -f "^input_file^".v") in
  

  let _ = (Feedback.msg_notice (str ("Proofs are available in file "^result_file^".v. Please run the followings commands/tactics to complete the proof:\n Require Import "^b^". \n solve_using "^lemma_name^". ") ))
   (*
  let _ = (Feedback.msg_notice (str "require import blabla")) in
    let (a,b) = match (String.split_on_char '/' result_file) with [a;b] -> (a,b) | _ -> failwith "erreur" in
  let qidl = [(Libnames.qualid_of_string b)] in 
  
  let _ = my_vernac_require None (Some true) qidl in *)
  (* let _ = Library.require_library_from_dirpath [ (Stm.get_ldir ()), (result_file^".v")) ] (Some true) in *)
 
(*
VtDefault(fun () ->
        unsupported_attributes atts;
        vernac_require from export qidl)
*)
(*  let _ = vernac_require'
            None (*(Some (Libnames.qualid_of_string ("Tuto0")))*)
            (Some false)
            [(Libnames.qualid_of_string b)] in*)
(*  (Feedback.msg_notice (str "success"))*)
  in Tacticals.New.tclIDTAC
   
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
  let _ = if !debug then (Feedback.msg_notice (str "le terme en entree")) in 
  let _ = if !debug then (Feedback.msg_notice (Printer.pr_econstr_env env sigma (l))) in 
  let (f,a) = destApp sigma l in
  let _ = if !debug then (Feedback.msg_notice (Printer.pr_econstr_env env sigma (f))) in
  let _ = if !debug then (Feedback.msg_notice (str "blabla")) in 
  let _ = if !debug then (Feedback.msg_notice (Printer.pr_econstr_env env sigma (a.(0)))) in
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
       then let _ = if !debug then (Feedback.msg_notice (str "reconnaitre eq + rk : ok")) in 
            let  args = (Array.to_list b) in
            let _ = if !debug then (Feedback.msg_notice (str ("args of rk : ok length = "^(string_of_int (List.length args))))) in
            let p = points gl env sigma (List.hd args) in
            let _ = if !debug then (Feedback.msg_notice (str "alles gut")) in
            let _ = if !debug then (Feedback.msg_notice (str (mk_string (List.map (fun x -> Names.Id.to_string (destVar sigma x)) p))))
            in (mk_string (List.map (fun x -> Names.Id.to_string (destVar sigma x)) p))
       else failwith "not a rank term" (*(Feedback.msg_notice (str "pas rk"))*)
 

let rec interp_nat gl env sigma c =
 let _ = if !debug then (Feedback.msg_notice (str "entier en entree")) in 
 let _ = if !debug then (Feedback.msg_notice (Printer.pr_econstr_env env sigma (c))) in
 if Tacmach.New.pf_conv_x gl c (coq_O ())
 then 0
 else let (f,a) = destApp sigma c in
      if  Tacmach.New.pf_conv_x gl f (coq_S ())
      then (1+(interp_nat gl env sigma a.(0)))
      else failwith "error: interp_nat"
   
let interp_hyp_or_concl gl env sigma c =
  let _ = if !debug then  (Feedback.msg_notice (str "interp_hyp_or_concl")) in
  let _ = if !debug then (Feedback.msg_notice (Printer.pr_econstr_env env sigma c)) in 
  if isApp sigma c then 
    let (f,a) = destApp sigma c in
    if Tacmach.New.pf_conv_x gl f (coq_eq ()) then
      let _ = if !debug then (Feedback.msg_notice (str "bouhbouh")) in
      let _ = if !debug then (Feedback.msg_notice (Printer.pr_econstr_env env sigma a.(1))) in
      let _ = if !debug then (Feedback.msg_notice (Printer.pr_econstr_env env sigma  (fst (destApp sigma a.(1))))) in
      if (isApp sigma a.(1)) then
        if Tacmach.New.pf_conv_x gl (fst (destApp sigma a.(1))) (coq_rk ())
        then 
          let _ =  if !debug then (Feedback.msg_notice (Printer.pr_econstr_env env sigma (a.(0)))) in 
          let _ =  if !debug then (Feedback.msg_notice (Printer.pr_econstr_env env sigma (a.(1)))) in
          let _ =  if !debug then (Feedback.msg_notice (Printer.pr_econstr_env env sigma (a.(2)))) in
          let r = interp_rk gl env sigma a.(1) in
          let n = interp_nat gl env sigma a.(2) in
          r^" : "^(string_of_int n)
        else
        ""
    else
      let _ = if !debug then (Feedback.msg_notice (Printer.pr_econstr_env env sigma c)) in 
      ""
    else ""
  else ""

let rec myflatten l = 
          match l with
            [] -> ""
          | x::xs -> if x="" then myflatten xs else x^"\n"^(myflatten xs);;
  
let pprove () =
  let _ = if !debug then Feedback.msg_notice (str "proving...") in
  Proofview.Goal.enter
    begin fun gl ->
    (*let s = Stm.get_current_state (Stm.get_doc 0) in *)
    (*  let s = Proofview_monad.StateStore.empty in (*Proofview_monad.StateStore.with_empty_state gl in *)*)
    let proof_name = Names.Id.to_string (Vernacstate.Declare.get_current_proof_name ()) in 
    let _ = if !debug then (Feedback.msg_notice (str proof_name)) in
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
    let _ = if !debug then aff gl env sigma raw_list      in (*        (Feedback.msg_notice (Printer.pr_named_decl env sigma lh);*)
    let _ = if !debug then show_points gl env sigma (list_of_points gl env sigma raw_list) in
    (*let _ = interp_rk gl env sigma concl in*)
    (*let n = let (f,a)= destApp sigma concl in a.(2) in 
      let v = interp_nat gl env sigma n in
      let _ =  (Feedback.msg_notice (str (string_of_int v))) in*)
    let _ =  if !debug then (Feedback.msg_notice (str (interp_hyp_or_concl gl env sigma concl))) in
    let _ = send_text proof_name text_to_send in
    (*let ml_load_path, vo_load_path = build_load_path opts in
    let injections = injection_commands opts in
    let stm_options = opts.config.stm_flags in*)
   (* let _ =  (Feedback.msg_notice (str "la stm maintenant...")) in
    (*let open Stm in
    let p = States.freeze ~marshallable:true in *)
    let f = Stm.TopLogical Coqargs.default_toplevel in (*(Stm.TopLogical (Names.DirPath.make [])) in*)
    let open Vernac.State in
    let _ =  (Feedback.msg_notice (str "encore vivante 1...")) in
    let ml_load_path, vo_load_path = Coqargs.build_load_path Coqargs.default in
    let  _ = if (ml_load_path = [])  then (Feedback.msg_notice (str "vide...")) else (Feedback.msg_notice (str "pasvide...")) 
    in 
    let injections = Coqargs.injection_commands Coqargs.default in
    let _ =  (Feedback.msg_notice (str "encore vivante 2...")) in
    let stm_options =  Stm.AsyncOpts.default_opts in
    let _ =  (Feedback.msg_notice (str "encore vivante 2bis...")) in
    let p = Stm.new_doc in
    let _ =  (Feedback.msg_notice (str "encore vivante 2 here...")) in
    
      let doc, sid = Topfmt.(in_phase ~phase:InteractiveLoop)
          p
          Stm.{ doc_type = Interactive f; ml_load_path;
                vo_load_path; injections; stm_options;
                   } in
    let _ =  (Feedback.msg_notice (str "encore vivante 2ter...")) in
    let s = { doc; sid; proof = None; time = true } in
    let _ =  (Feedback.msg_notice (str "encore vivante 3...")) in
    try (
      let _ =  Vernac.load_vernac ~echo:false ~check:false ~interactive:false ~state:s "blublu.v" in *)
    (* grep Lemma theories/blaxbla2.v |  awk '{print $2}' *)
(*
let _ = let x = Coqlib.find_reference "Tuto0" ["Tuto0";"blaxbla2"] "LP1P2P3" in 
            EConstr.of_constr (Globnames.printable_constr_of_global x) in*)
Tacticals.New.tclIDTAC
  (*Tactics.eapply lemma*)
               (*Tacticals.New.tclTHEN (Tactics.eapply lemma) Tacticals.New.tclIDTAC (*(Eauto.e_assumption)*)*)
    end
    (* val load_vernac : echo:bool -> check:bool -> interactive:bool ->
  state:   State.t -> string -> State.t *)

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
