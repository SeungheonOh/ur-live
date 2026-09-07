fun main () : transaction page =
    count <- source 0;
    return <xml><body>
      <h1>A browser-only counter</h1>
      <button onclick={fn _ => n <- get count; set count (n + 1)}>Increment</button>
      <p>Count: <dyn signal={n <- signal count; return <xml>{[n]}</xml>}/></p>
    </body></xml>
