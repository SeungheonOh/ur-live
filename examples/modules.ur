signature ITEM = sig
    type t
    val value : t
    val display : t -> string
end

functor Present(M : ITEM) = struct
    val message = M.display M.value
end

structure Answer = Present(struct
    type t = int
    val value = 42
    fun display n = "A functor produced " ^ show n
end)

fun main () : transaction page =
    return <xml><body><p>{[Answer.message]}</p></body></xml>
