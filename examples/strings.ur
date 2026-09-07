fun main () : transaction page =
    return <xml><body>
      <p>Characters: {[strlen "λab"]}; bytes: {[strlenUtf8 "λab"]}.</p>
      <p>First byte: {[ord (strsubUtf8 "λab" 0)]}.</p>
      <p>Suffix: {[case strchr "λab" #"a" of None => "missing" | Some s => s]}.</p>
      <p>Rounded: {[round (-1.5)]}.</p>
    </body></xml>
