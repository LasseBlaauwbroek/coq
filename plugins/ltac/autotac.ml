
let () = Hook.set Stm.pre_known_state_hook (fun id ->
    Autotac_process.pre_known_state id;
    Autotac_thread.pre_known_state id
  )

let () = Hook.set Stm.post_known_state_hook (fun id ->
    Autotac_process.post_known_state id;
    Autotac_thread.post_known_state id
  )
