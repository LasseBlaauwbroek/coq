let stm_pr_err s  = Format.eprintf "%s] %s\n%!"     (Spawned.process_id ()) s

module TacTask : sig

  type task = {
    t_state    : Vernacstate.t;
    t_tactic   : ComTactic.interpretable;
    t_kill     : unit -> unit;
    t_name     : string }

  include AsyncTaskQueue.Task with type task := task

end = struct (* {{{ *)

  let forward_feedback { Feedback.doc_id = did; span_id = id; route; contents } =
    print_endline "forward feedback";
    Feedback.feedback ~did ~id ~route contents

  type task = {
    t_state    : Vernacstate.t;
    t_tactic   : ComTactic.interpretable;
    t_kill     : unit -> unit;
    t_name     : string }

  type request = {
    r_state    : Vernacstate.t;
    r_tactic   : ComTactic.interpretable;
    r_name     : string }

  type response = string

  let name = ref "autotacworker"
  let extra_env () = [||]
  type competence = unit
  type worker_status = Fresh | Old of competence

  let task_match _ _ =
    print_endline "task match";
    true

  (* run by the master, on a thread *)
  let request_of_task _ { t_state; t_tactic; t_kill; t_name } =
    print_endline "request of task";
    Some
      { r_state = t_state
      ; r_tactic = t_tactic
      ; r_name = t_name }

  let use_response _ _ s =
    print_endline s;
    print_endline "use response";
    `End

  let on_marshal_error err { t_name } =
    print_endline "on marshal error";
    stm_pr_err ("Fatal marshal error: " ^ t_name );
    flush_all (); exit 1

  let on_task_cancellation_or_expiration_or_slave_death = function
    | Some { t_kill } ->
      print_endline "killing ba";
      t_kill ()
    | _ -> print_endline "not killing"; ()

  (* let state = ref None *)

  let perform { r_state; r_tactic } =
    Vernacstate.unfreeze_interp_state r_state;
    Vernacstate.LemmaStack.with_top (Option.get r_state.Vernacstate.lemmas) ~f:(fun pstate ->
        let g = Goal_select.get_default_goal_selector () in
        ignore (ComTactic.solve ~pstate g ~info:None r_tactic ~with_end_tac:false));
    "hihi"

  let name_of_task { t_name } = t_name
  let name_of_request { r_name } = r_name

end (* }}} *)
