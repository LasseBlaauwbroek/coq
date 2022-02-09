(* TODO: *)
(*    - This implementation seems fundamentally flawed because the thread is able to modify the state during *)
(*      parsing, which is not allowed and can sometimes lead to real issues. Other invariants may also not be respected. *)
(*    - Test on windows *)
(*    - Test on Mac *)
(*    - Test in coqtop *)
(*    - Test in vscode *)

(* external low_priority : unit -> unit = "low_priority" *)

(* external win32_interrupt : int -> unit = "win32_interrupt" *)

let auto_tactics = Summary.ref ~name:"AutomaticTacticsThread" []
let threads = ref Int.Map.empty
let state = ref None
let terminating_message = Event.new_channel ()

let in_auto_tactic = Libobject.(declare_object @@ global_object_nodischarge
    "AutomaticTacticThread"
    ~cache:(fun (_, t) -> auto_tactics := t)
    ~subst:(Some (fun (s, t) -> List.map (Tacsubst.subst_tactic s) t)))

let register_auto_tactic t = Lib.add_anonymous_leaf (in_auto_tactic t)

let rec drain_sigints () =
  try
    let p = Unix.sigpending () in
    if List.mem Sys.sigint p then
      (let _ = Thread.wait_signal [Sys.sigint] in
       (* Feedback.msg_notice Pp.(str "signal awaited"); *)
       drain_sigints ())
  with _ ->
    ()

let terminate_threads () =
  let rec loop () =
    if not @@ Int.Map.is_empty !threads then begin
      (* We may be sending this signal too much, they are later caught through `drain_sigints`. *)
      (try
         Unix.kill (Unix.getpid ()) Sys.sigint
       with _ ->
         Control.interrupt := true);
      (try
         let e = Event.receive terminating_message in
         let t = Event.sync e in
         Thread.join t;
         (* Feedback.msg_info Pp.(str "sync"); *)
         threads := Int.Map.remove (Thread.id t) !threads;
         Control.interrupt := false;
       with Sys.Break ->
         Control.interrupt := false);
      loop ()
    end
  in
  let prev_signal = Sys.signal Sys.sigint (Sys.Signal_handle (fun _ ->
      (* Feedback.msg_notice Pp.(str "signal received " ++ (int @@ Thread.id @@ Thread.self ())); *)
      raise Sys.Break)) in
  let prev_block =
    try Thread.sigmask Unix.SIG_BLOCK [Sys.sigint]
    with _ -> [] in
  (* Feedback.msg_notice Pp.(str "pre_join"); *)
  loop ();
  drain_sigints ();
  (try
     ignore (Thread.sigmask Unix.SIG_SETMASK prev_block)
   with _ -> ());
  Sys.set_signal Sys.sigint prev_signal;
  (* Allow timeout signals again now that all auto threads have been killed *)
  try
    ignore (Thread.sigmask Unix.SIG_UNBLOCK [Sys.sigalrm])
  with _ -> ()

let pre_known_state id =
  (* Feedback.msg_notice Pp.(str "Pre: " ++ Stateid.print id); *)
  (* let time = Unix.gettimeofday () in *)
  (match !state, !threads with
   | Some id_running, threads when not @@ Stateid.equal id id_running && not @@ Int.Map.is_empty threads ->
     (* Feedback.msg_notice Pp.(str "post_join") *)
     terminate_threads ()
   | _ -> ())
(* let time2 = Unix.gettimeofday () in *)
(* Feedback.msg_notice Pp.(str "pre-time: " ++ (str @@ string_of_float (time2 -. time))) *)

let logger, logger_hook = Hook.make ()

let start_auto_tac p tac =
  let tac = Tacinterp.eval_tactic tac in
  let initialized_message = Event.new_channel () in
  let tfunc () =
    (try
       (* low_priority (); *)
       (* Feedback.msg_notice Pp.(str "runner id: " ++ (int @@ Thread.id @@ Thread.self ())); *)
       Fun.protect ~finally:(fun () ->
           try
             ignore(Thread.sigmask Unix.SIG_BLOCK [Sys.sigint])
           with _ -> ()) @@ fun () ->
       (* Make sure that we have entered the `try` and modified the main state
          before allowing the main thread to move on to another command. *)
       let e = Event.send initialized_message () in
       Event.sync e;
       (* Force the thread to yield for some time in order to give the main thread a chance to
          immediately cancel the thread and move on to the next command. *)
       Unix.sleepf 0.2;
       Vernacstate.System.protect (fun () ->
           ignore (Proof.solve (Goal_select.get_default_goal_selector ()) None tac p)) ();
     with
     | e ->
       (match e with
        | Sys.Break | CErrors.Timeout | Logic_monad.TacticFailure _ -> Hook.get logger ()
        | _ -> ());
       match e with
       | Sys.Break -> ()
       (* Feedback.msg_info Pp.(str "break received") *)
       | CErrors.Timeout -> ()
       | Logic_monad.TacticFailure _ -> ()
       | Logic_monad.Tac_Timeout -> ()
       | any ->
         let (e, info) = Exninfo.capture any in
         let loc = Loc.get_loc info in
         let msg = CErrors.iprint (e, info) in
         let msg = Pp.(str "Automatic Tactic: " ++ msg) in
         Feedback.msg_warning ?loc msg;
    );
    let e = Event.send terminating_message (Thread.self ()) in
    Event.sync e
  in
  let t = Thread.create tfunc () in
  (* Wait until the thread performs the bare minimum initialization. *)
  let e = Event.receive initialized_message in
  Event.sync e;
  threads := Int.Map.add (Thread.id t) t !threads

let post_known_state id =
  (* Feedback.msg_notice Pp.(str "Post: " ++ Stateid.print id); *)
  (* let time = Unix.gettimeofday () in *)
  let cached = match !state with
    | Some id_running when Stateid.equal id id_running -> true
    | _ -> false in
  state := Some id;
  if not cached then
    (match Stm.is_interactive (), Stm.get_proof ~doc:(Stm.get_doc 0) id, !auto_tactics, !threads with
     | _, _, _, threads when not @@ Int.Map.is_empty threads ->
       CErrors.anomaly Pp.(str "Autotac threads should not exist")
     | true, Some p, (_::_ as tacs), _ when not @@ Proof.no_focused_goal p ->
       (* Feedback.msg_info Pp.(str "post autotac" ++ Stateid.print id) *)
       (* Block timeout signals on the main thread, so they arrive at the auto thread *)
       (* TODO: This only works reliable with one auto-thread *)
       List.iter (start_auto_tac p) tacs;
       (try
          ignore (Thread.sigmask Unix.SIG_BLOCK [Sys.sigalrm])
        with _ -> ());
       ()
     | _, _, _, _ -> ())
(* let time2 = Unix.gettimeofday () in *)
(* Feedback.msg_notice Pp.(str "post-time: " ++ (str @@ string_of_float (time2 -. time))) *)
