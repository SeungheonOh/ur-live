fun identity [a] (x : a) : a = x

fun main () : transaction page =
    return <xml><body>
      <h1>Hello from Ur</h1>
      <p>The answer is {[identity 42]}.</p>
    </body></xml>
