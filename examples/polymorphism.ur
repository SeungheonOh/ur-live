fun identity [a] (x : a) : a = x

val foo = identity 42
val bar = identity 42
val baz = identity 41
val greeting = identity "Hello, λ & Ur"

fun main () : transaction page =
    return <xml><body>
      <h1>{[greeting]}</h1>
      <p>{[foo]}, {[bar]}, {[baz]}</p>
    </body></xml>
