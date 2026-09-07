val person = {Name = "Ada", Scores = 11 :: 17 :: 14 :: []}

fun sum xs = List.foldl (fn n acc => n + acc) 0 xs

fun main () : transaction page =
    return <xml><body>
      <h1>{[person.Name]}</h1>
      <p>Scores total: {[sum person.Scores]}</p>
    </body></xml>
