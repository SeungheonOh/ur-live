(* Every level is made by pressing a solved board, so it has a solution.
   The outstanding presses also form a hint, without a solver or randomness. *)
val cells = 0 :: 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: 8 :: 9 ::
            10 :: 11 :: 12 :: 13 :: 14 :: 15 :: []

fun touches a b =
    a = b || (a / 4 = b / 4 && (a = b + 1 || b = a + 1)) ||
    a = b + 4 || b = a + 4

fun lit presses cell =
    List.foldl (fn press on => if touches press cell then not on else on) False presses

fun toggle presses cell =
    if List.mem cell presses then List.filter (fn old => old <> cell) presses
    else cell :: presses

fun levelPresses level =
    if level % 3 = 0 then 1 :: 6 :: 8 :: []
    else if level % 3 = 1 then 0 :: 3 :: 5 :: 10 :: 12 :: []
    else 2 :: 4 :: 7 :: 9 :: 13 :: 15 :: []

type puzzle = {Level : int, Presses : list int, Moves : int, Hint : bool}

fun main () : transaction page =
    state <- source {Level = 0, Presses = levelPresses 0, Moves = 0, Hint = False};
    let
        fun press cell =
            current <- get state;
            if not (List.exists (lit current.Presses) cells) then return ()
            else set state {Level = current.Level, Presses = toggle current.Presses cell,
                            Moves = current.Moves + 1, Hint = False}
        fun start level =
            set state {Level = level, Presses = levelPresses level, Moves = 0, Hint = False}
    in
        return <xml><body>
          <h1>Lights Out</h1>
          <p>Turn every light off. A press flips that tile and its up, down, left, and right neighbors.</p>
          <dyn signal={
            current <- signal state;
            let
                val remaining = List.length (List.filter (lit current.Presses) cells)
                fun square cell =
                    let
                        val on = lit current.Presses cell
                        val title = "Tile " ^ show (cell + 1)
                    in
                        if on then <xml><button title={title}
                          style="width:56px;height:56px;margin:3px;border-radius:8px;border:2px solid #b45309;background:#fde68a;color:#78350f"
                          onclick={fn _ => press cell}>ON</button></xml>
                        else <xml><button title={title}
                          style="width:56px;height:56px;margin:3px;border-radius:8px;border:2px solid #475569;background:#1e293b;color:#cbd5e1"
                          onclick={fn _ => press cell}>off</button></xml>
                    end
                fun row start = <xml><div>{square start}{square (start + 1)}{square (start + 2)}{square (start + 3)}</div></xml>
            in
                return <xml>
                  <p><strong>Level {[current.Level + 1]} / 3</strong> · Moves: {[current.Moves]} · Lights on: {[remaining]}</p>
                  {row 0}{row 4}{row 8}{row 12}
                  {if remaining = 0 then <xml><p><strong>All dark. You solved it!</strong></p></xml>
                   else if current.Hint then
                     case current.Presses of
                         [] => <xml/>
                       | cell :: _ => <xml><p>Try row {[cell / 4 + 1]}, column {[cell % 4 + 1]}.</p></xml>
                   else <xml><p>Need a nudge? Ask for a hint.</p></xml>}
                  <button onclick={fn _ => latest <- get state; start latest.Level}>Restart level</button>
                  <button onclick={fn _ => latest <- get state;
                    set state {Level = latest.Level, Presses = latest.Presses,
                               Moves = latest.Moves, Hint = True}}>Hint</button>
                  <button onclick={fn _ => latest <- get state; start ((latest.Level + 1) % 3)}>Next level</button>
                </xml>
            end}/>
        </body></xml>
    end
