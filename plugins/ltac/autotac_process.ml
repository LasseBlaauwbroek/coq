
(*
TODO:
   - Test on windows
   - Test on Mac
   - Test in coqtop
   - Test in vscode
*)

module TaskQueue = AsyncTaskQueue.MakeQueue(Autotac_task.TacTask) ()

let auto_tactics = Summary.ref ~name:"AutomaticTacticsProcess" []
let queue = ref None
let state = ref None

let in_auto_tactic = Libobject.(declare_object @@ global_object_nodischarge
    "AutomaticTacticProcess"
    ~cache:(fun (_, t) -> auto_tactics := t)
    ~subst:(Some (fun (s, t) -> t)))

let register_auto_tactic t = Lib.add_anonymous_leaf (in_auto_tactic t)

let pre_known_state id =
  (* Feedback.msg_notice Pp.(str "Pre: " ++ Stateid.print id); *)
  (* let time = Unix.gettimeofday () in *)
  (match !state, !queue with
   | Some id_running, Some q when not @@ Stateid.equal id id_running ->
     (* Feedback.msg_notice Pp.(str "post_join") *)
     (* Feedback.msg_notice Pp.(str "pre destroy"); *)
     TaskQueue.destroy q;
     (* Feedback.msg_notice Pp.(str "post destroy"); *)
     queue := None
   | _ -> ())
(* let time2 = Unix.gettimeofday () in *)
(* Feedback.msg_notice Pp.(str "pre-time: " ++ (str @@ string_of_float (time2 -. time))) *)

let post_known_state id =
  (* Feedback.msg_notice Pp.(str "Post: " ++ Stateid.print id); *)
  (* let time = Unix.gettimeofday () in *)
  let cached = match !state with
    | Some id_running when Stateid.equal id id_running -> true
    | _ -> false in
  state := Some id;
  if not cached then
    (match Stm.is_interactive (), Stm.get_proof ~doc:(Stm.get_doc 0) id, !auto_tactics, !queue with
     | _, _, _, Some queue ->
       CErrors.anomaly Pp.(str "Autotac queue should not exist")
     | true, Some p, (_::_ as tacs), None when not @@ Proof.no_focused_goal p ->
       (* Feedback.msg_info Pp.(str "post autotac" ++ Stateid.print id) *)
       let t_state = Vernacstate.freeze_interp_state ~marshallable:true in
       let q = TaskQueue.create (List.length tacs) CoqworkmgrApi.High in
       let g = Goal_select.get_default_goal_selector () in
       let global = match g with Goal_select.SelectAll | Goal_select.SelectList _ -> true | _ -> false in
       let tacs = List.map (fun ast -> { Tacinterp.global; ast }) tacs in
       let tacs = List.map Tacinterp.hide_interp tacs in
       List.iteri (fun i t_tactic ->
           let task =
             Autotac_task.TacTask.{ t_state
                                  ; t_tactic
                                  ; t_kill = (fun () -> TaskQueue.cancel_all q)
                                  ; t_name = "tactic " ^ string_of_int i } in
           TaskQueue.enqueue_task q task ~cancel_switch:(ref false)
         ) tacs;
       queue := Some q
     | _, _, _, _ -> ())
(* let time2 = Unix.gettimeofday () in *)
(* Feedback.msg_notice Pp.(str "post-time: " ++ (str @@ string_of_float (time2 -. time))) *)
