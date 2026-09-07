datatype tree = Leaf of int | Branch of tree * tree

fun total t =
    case t of
        Leaf n => n
      | Branch (left, right) => total left + total right

val example = Branch (Leaf 12, Branch (Leaf 17, Leaf 13))

fun main () : transaction page =
    return <xml><body>
      <h1>A recursive datatype</h1>
      <p>The tree sums to {[total example]}.</p>
    </body></xml>
