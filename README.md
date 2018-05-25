# containersandbox

Random data structures written while learning Idris:

* Data.FiniteVect: a length-typed vector which also carries a maximum capacity in its type
* Data.SizedVect: length-typed vectors which keep track of some metric of size in addition to their length (with a size function that takes each element of the vector and produces a size)
* Data.RelVect: length-typed vector which also carries proof that some binary relation holds between each pair of adjacent elements. `rmap`, the equivalent of `map` on this structure, is rather complicated; for a usage example, see [the `VerifiedCardinality` implementation for `Fin`](https://github.com/ericbaer/verifiedenum/blob/master/Data/Enum/Verified/WithBounded.idr) in the `verifiedenum` package
* Data.RoseTree: tree where each node has a variable number of children
* Data.LabelledTree: tree with a value at each node, labelled edges to children, and a different value type at the leaves 
* Data.Either.Variadic: like `Either`, but on more than two elements
* Data.Function.Variadic: treating functions (particularly, type constructors) similarly regardless of how many arguments they take
