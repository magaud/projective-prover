open Pp

let message = "Hello world!"

let pprove () =
  let _ = Feedback.msg_notice (str "proving...") in Tacticals.New.tclIDTAC;
  
