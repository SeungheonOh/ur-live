cookie preference : string

fun main () : transaction page =
    value <- getCookie preference;
    return <xml><body>{[case value of None => "None" | Some s => s]}</body></xml>
