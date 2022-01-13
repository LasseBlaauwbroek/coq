(*
TODO:
   - This implementation seems fundamentally flawed because the thread is able to modify the state during
     parsing, which is not allowed and can sometimes lead to real issues. Other invariants may also not be respected.
   - Make sure that timeouts are delivered to the correct thread
   - Test on windows
   - Test on Mac
   - Test in coqtop
   - Test in vscode
*)

external low_priority : unit -> unit = "low_priority"

let auto_tactic = Summary.ref ~name:"AutomaticTactic" None
let thread = ref None
let state = ref None

let in_auto_tactic = Libobject.(declare_object @@ global_object_nodischarge
    "AutomaticTactic"
    ~cache:(fun (_, t) -> auto_tactic := Some t)
    ~subst:(Some (fun (s, t) -> Tacsubst.subst_tactic s t)))

let register_auto_tactic t = Lib.add_anonymous_leaf (in_auto_tactic t)

let rec drain_sigints () =
  let p = Unix.sigpending () in
  if List.mem Sys.sigint p then
    (let _ = Thread.wait_signal [Sys.sigint] in
     (* Feedback.msg_notice Pp.(str "signal awaited"); *)
     drain_sigints ())

let () = Hook.set Stm.pre_known_state_hook (fun id ->
    (* Feedback.msg_notice Pp.(str "Pre: " ++ Stateid.print id); *)
    (* let time = Unix.gettimeofday () in *)
    (match !state, !thread with
     | Some id_running, Some t when not @@ Stateid.equal id id_running ->
       let prev_signal = Sys.signal Sys.sigint (Sys.Signal_handle (fun _ ->
           (* Feedback.msg_notice Pp.(str "signal received " ++ (int @@ Thread.id @@ Thread.self ())); *)
           raise Sys.Break)) in
       let prev_block = Thread.sigmask Unix.SIG_BLOCK [Sys.sigint] in
       (* Feedback.msg_notice Pp.(str "pre_join"); *)
       Unix.kill (Unix.getpid ()) Sys.sigint;
       Thread.join t;
       drain_sigints ();
       ignore (Thread.sigmask Unix.SIG_SETMASK prev_block);
       Sys.set_signal Sys.sigint prev_signal
       (* Feedback.msg_notice Pp.(str "post_join") *)
     | _ -> ())
    (* let time2 = Unix.gettimeofday () in *)
    (* Feedback.msg_notice Pp.(str "pre-time: " ++ (str @@ string_of_float (time2 -. time))) *)
  )

let () = Hook.set Stm.post_known_state_hook (fun id ->
    (* Feedback.msg_notice Pp.(str "Post: " ++ Stateid.print id); *)
    (* let time = Unix.gettimeofday () in *)
    let cached = match !state with
      | Some id_running when Stateid.equal id id_running -> true
      | _ -> false in
    state := Some id;
    if not cached then
      (match Stm.is_interactive (), Stm.get_proof ~doc:(Stm.get_doc 0) id, !auto_tactic, !thread with
       | _, _, _, Some _ ->
         CErrors.anomaly Pp.(str "Autotac thread should not exist")
       | true, Some p, Some tac, None when not @@ Proof.no_focused_goal p ->
         let tac = Tacinterp.eval_tactic tac in
         let initialized_message = Event.new_channel () in
         let tfunc () =
           try
             (* low_priority (); *)
             (* Feedback.msg_notice Pp.(str "runner id: " ++ (int @@ Thread.id @@ Thread.self ())); *)
             Fun.protect ~finally:(fun () -> thread := None) @@ fun () ->
             thread := Some (Thread.self ());
             (* Make sure that we have entered the `try` and modified the main state
                before allowing the main thread to move on to another command. *)
             let e = Event.send initialized_message () in
             Event.sync e;
             (* Force the thread to yield for some time in order to give the main thread a chance to
                immediately cancel the thread and move on to the next command. *)
             Unix.sleepf 0.1;
             Vernacstate.System.protect (fun () ->
                 ignore (Proof.solve (Goal_select.get_default_goal_selector ()) None tac p)) ();
           with
           | Sys.Break -> ()
             (* Feedback.msg_info Pp.(str "break received") *)
           | any ->
             let (e, info) = Exninfo.capture any in
             let loc = Loc.get_loc info in
             let msg = CErrors.iprint (e, info) in
             let msg = Pp.(str "Automatic Tactic: " ++ msg) in
             Feedback.msg_warning ?loc msg
         in
         let _ = Thread.create tfunc () in
         (* Wait until the thread performs the bare minimum initialization. *)
         let e = Event.receive initialized_message in
         Event.sync e
         (* Feedback.msg_info Pp.(str "post autotac" ++ Stateid.print id) *)
       | _, _, _, _ -> ())
    (* let time2 = Unix.gettimeofday () in *)
    (* Feedback.msg_notice Pp.(str "post-time: " ++ (str @@ string_of_float (time2 -. time))) *)
  )
