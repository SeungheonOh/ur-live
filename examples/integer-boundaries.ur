fun add (a : int) (b : int) = a + b

fun main () : transaction page =
    return <xml><body>
      <p>Wrapped: {[add 9223372036854775807 1]}.</p>
      <p>Remainder: {[(-17) % 5]}.</p>
      <p>Division: {[(-17) / 5]}.</p>
    </body></xml>
