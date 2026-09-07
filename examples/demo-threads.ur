(* Port of the official Ur/Web threads demo.
   Original: http://www.impredicative.com/ur/demo/threads.html
   Source and BSD license: vendor/urweb-demos (55a881ff9b50).
   Buffer is inlined as a module for the single-file playground.
*)

structure Buffer : sig
type t

val create : transaction t
val render : t -> signal xbody
val write : t -> string -> transaction unit
end = struct
datatype lines = End | Line of string * source lines

type t = { Head : source lines, Tail : source (source lines) }

val create =
    head <- source End;
    tail <- source head;
    return {Head = head, Tail = tail}

fun renderL lines =
    case lines of
        End => <xml/>
      | Line (line, linesS) => <xml>{[line]}<br/><dyn signal={renderS linesS}/></xml>

and renderS linesS =
    lines <- signal linesS;
    return (renderL lines)

fun render t = renderS t.Head

fun write t s =
    oldTail <- get t.Tail;
    newTail <- source End;
    set oldTail (Line (s, newTail));
    set t.Tail newTail
end

fun main () =
    buf <- Buffer.create;
    let
        fun loop prefix delay =
            let
                fun loop' n =
                    Buffer.write buf (prefix ^ ": Message #" ^ show n);
                    sleep delay;
                    loop' (n + 1)
            in
                loop'
            end
    in
        return <xml><body onload={spawn (loop "A" 5000 0); spawn (loop "B" 3000 100)}>
          <dyn signal={Buffer.render buf}/>
        </body></xml>
    end
