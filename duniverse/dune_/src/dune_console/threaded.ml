open Stdune

let spawn_thread = Fdecl.create Dyn.opaque

(** [threaded (module T)] is a backend that renders the user interface in a
    separate thread. The module [T] must implement the [Threaded] interface.
    There are special functions included to handle various functions of a user
    interface. *)
let make (module Base : Threaded_intf.S) : (module Backend_intf.S) =
  let module T = struct
    let mutex = Mutex.create ()

    let finish_cv = Condition.create ()

    let state =
      { Threaded_intf.messages = Queue.create ()
      ; status_line = None
      ; finished = false
      ; finish_requested = false
      }

    let finish () =
      Mutex.lock mutex;
      state.finish_requested <- true;
      while not state.finished do
        Condition.wait finish_cv mutex
      done;
      Mutex.unlock mutex

    let print_user_message m =
      Mutex.lock mutex;
      Queue.push state.messages m;
      Mutex.unlock mutex

    let set_status_line sl =
      Mutex.lock mutex;
      state.status_line <- sl;
      Mutex.unlock mutex

    let print_if_no_status_line _msg = ()

    let reset () =
      Mutex.lock mutex;
      Queue.clear state.messages;
      state.status_line <- None;
      Base.reset ();
      Mutex.unlock mutex

    let reset_flush_history () =
      Mutex.lock mutex;
      Queue.clear state.messages;
      state.status_line <- None;
      Base.reset_flush_history ();
      Mutex.unlock mutex

    let start () =
      Base.start ();
      Fdecl.get spawn_thread @@ fun () ->
      let last = ref (Unix.gettimeofday ()) in
      let frame_rate = 1. /. 60. in
      let cleanup () =
        state.finished <- true;
        Base.finish ();
        Condition.broadcast finish_cv;
        Mutex.unlock mutex
      in
      try
        (* This is the main event loop for a threaded backend.

           Firstly we lock our mutex, to prevent other threads from mutating our
           state. Next we ask our implementation to render the given state,
           afterwards checking if a finish was requested.

           If a finish was requested we exit the loop cleanly.

           We unlock our mutex and go into a time calculation. This calculation
           gets the current time and compares it with the last recorded time.
           This lets us compute the elapsed time.

           Next we check that the elapsed time is larger than our specifed
           [frame_rate]. If this is the case then we can handle any pending user
           events and continue the loop as soon as possible.

           If we have not yet reached the [frame_rate] then we can handle user
           events and sleep for the remaining time. *)
        while true do
          Mutex.lock mutex;
          Base.render state;
          let finish_requested = state.finish_requested in
          if finish_requested then raise_notrace Exit;
          Mutex.unlock mutex;
          let now = Unix.gettimeofday () in
          let elapsed = now -. !last in
          let new_time =
            if elapsed >= frame_rate then
              Base.handle_user_events ~now ~time_budget:0.0 mutex
            else
              let delta = frame_rate -. elapsed in
              Base.handle_user_events ~now ~time_budget:delta mutex
          in
          last := new_time
        done
      with
      | Exit -> cleanup ()
      | exn ->
        (* If any unexpected exceptions are encountered, we catch them, make
           sure we [cleanup] and then re-raise them. *)
        let exn = Exn_with_backtrace.capture exn in
        cleanup ();
        Exn_with_backtrace.reraise exn
  end in
  (module T)
