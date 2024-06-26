# Visualization of First-Order Logic

types are wires
predicates are nodes

p and q         : put the nodes side-by-side
match variables : plug in the "copy" map
some x, p[x]    : cap wire x
not p           : wrap p in annulus of opposite color

p or q      = not( not(p) and not(q) )
all x, p[x] = not( some x, not p[x] )
if p then q = not( p and not(q) )

---------------------------------

> build in stack for haskell
> stack exec holdtt-exe "basics.txt"

displays options for basic predicate operations,
including a more complex example like "herbivore".

> load 1 ___ : plug an option to display it
> load 0 ___ : same, without all the syntax

> draw 1/0 ___ : plug a hand-written predicate
> set p := ___ : make a key to store a new predicate
> delete p     : delete p from key-value store
> save         : save the key-value store


overall, not super organized yet.
tons of room for improvement ---
but graphviz is limited, so it's not a high priority.
this is mainly a basic proof of concept.