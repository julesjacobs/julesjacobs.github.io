export const playgroundPreludeSource = `
module Multicore : sig
  val max_domains : unit -> int
  val current_domain : unit -> int
  type 'a spawn_result =
    | Spawned
    | Failed of 'a * exn * Printexc.raw_backtrace
  val spawn_on
    :   domain:int
    -> ('a @ contended once portable unique -> unit) @ once portable unyielding
    -> 'a @ contended once portable unique
    -> 'a spawn_result
  val spawn
    :  ('a @ contended once portable unique -> unit) @ once portable unyielding
    -> 'a @ contended once portable unique
    -> 'a spawn_result
end = struct
  let max_domains () = 1
  let current_domain () = 0
  type 'a spawn_result =
    | Spawned
    | Failed of 'a * exn * Printexc.raw_backtrace
  let spawn_on ~domain:_ f x =
    f x;
    Spawned
  let spawn f x =
    spawn_on ~domain:0 f x
end

module Parallel : sig
  type t
  val fork_join2
    :  t @ local
    -> (t @ local -> 'a) @ shareable
    -> (t @ local -> 'b) @ shareable
    -> #('a * 'b)
  module Scheduler : sig
    module Sequential : sig
      type scheduler
      val create : unit -> scheduler
      val parallel : scheduler -> f:(t @ local -> 'a) -> 'a
    end
  end
end = struct
  type t = unit
  let fork_join2 parallel left right =
    #(left parallel, right parallel)
  module Scheduler = struct
    module Sequential = struct
      type scheduler = unit
      let create () = ()
      let parallel scheduler ~f =
        f scheduler
    end
  end
end

`;

function escapedStringLiteral(text) {
  return String(text).replace(/\\/g, "\\\\").replace(/"/g, '\\"');
}

export function withPlaygroundPrelude(filename, source) {
  return `${playgroundPreludeSource}# 1 "${escapedStringLiteral(filename)}"\n${source}`;
}

export function stripPlaygroundPreludeInterface(output) {
  return String(output)
    .replace(/^module Multicore :\n[\s\S]*?^  end(?: @@ stateless)?\n?/m, "")
    .replace(/^module Parallel :\n[\s\S]*?^  end(?: @@ stateless)?\n?/m, "");
}
