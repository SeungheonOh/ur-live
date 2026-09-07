(* Port of the official Ur/Web react demo.
   Original: http://www.impredicative.com/ur/demo/react.html
   Source and BSD license: vendor/urweb-demos (55a881ff9b50).
   The original Ur program below is unchanged.
*)

fun main () =
  s <- source "You didn't click it yet.";
  return <xml><body>
    <button value="Click me!" onclick={fn _ => set s "Now you clicked it."}/><br/>
    <dyn signal={v <- signal s; return <xml>{[v]}</xml>}/>
  </body></xml>
