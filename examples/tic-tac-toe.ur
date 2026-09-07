(* Two players, immutable move history, derived board, and undo. *)
type move = {Cell : int, Mark : string}

fun markAt (moves : list move) cell =
    case moves of
        [] => ""
      | move :: rest => if move.Cell = cell then move.Mark else markAt rest cell

fun winner moves =
    let
        fun line a b c =
            let val mark = markAt moves a in
                if mark <> "" && mark = markAt moves b && mark = markAt moves c
                then mark else ""
            end
        val lines = line 0 1 2 :: line 3 4 5 :: line 6 7 8 ::
                    line 0 3 6 :: line 1 4 7 :: line 2 5 8 ::
                    line 0 4 8 :: line 2 4 6 :: []
    in
        case List.find (fn mark => mark <> "") lines of
            None => ""
          | Some mark => mark
    end

fun nextPlayer moves = if List.length moves % 2 = 0 then "X" else "O"

fun main () : transaction page =
    history <- source ([] : list move);
    let
        fun play cell =
            moves <- get history;
            if markAt moves cell <> "" || winner moves <> "" then return ()
            else set history ({Cell = cell, Mark = nextPlayer moves} :: moves)

        fun undo () =
            moves <- get history;
            case moves of
                [] => return ()
              | _ :: rest => set history rest
    in
        return <xml><body>
          <h1>Tic-tac-toe</h1>
          <p>Two players, one board. X starts. Undo lets you try another branch.</p>
          <dyn signal={
            moves <- signal history;
            let
                val won = winner moves
                val finished = won <> "" || List.length moves = 9
                fun square cell =
                    let val mark = markAt moves cell in
                        <xml><button
                          title={"Square " ^ show (cell + 1)}
                          style="width:64px;height:64px;margin:3px;font-size:28px;border-radius:8px;border:1px solid #94a3b8;background:#eef2ff;color:#1e293b"
                          disabled={finished || mark <> ""}
                          onclick={fn _ => play cell}>{[if mark = "" then "·" else mark]}</button></xml>
                    end
                fun row start = <xml><div>{square start}{square (start + 1)}{square (start + 2)}</div></xml>
            in
                return <xml>
                  <p><strong>{[if won <> "" then won ^ " wins!"
                               else if finished then "Draw. Try another round!"
                               else nextPlayer moves ^ " to move"]}</strong></p>
                  {row 0}{row 3}{row 6}
                  <p>Moves: {[List.length moves]}</p>
                  <button disabled={List.length moves = 0} onclick={fn _ => undo ()}>Undo move</button>
                </xml>
            end}/>
          <button onclick={fn _ => set history []}>New game</button>
        </body></xml>
    end
