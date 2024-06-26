# Visualization of First-Order Logic

Types are wires, and relations are nodes.

All relations are built from the following operations.

| | |
|--|--|
| p and q | put the nodes side-by-side |
| match variables | plug in the "copy" map |
| some x, p[x] | cap wire x |
| not p | wrap p in annulus of opposite color |

| | |
|--|--|
| p or q | = | not( not(p) and not(q) ) |
| all x, p[x] | = | not( some x, not p[x] ) |
| if p then q | = | not( p and not(q) ) |

---------------------------------

`stack build`
`stack exec holdtt-exe "basics.txt"`

Displays options for basic predicate operations,
including a more complex example like "herbivore".

- `load 1 ___` : plug an option to display it
- `load 0 ___` : same, without all the syntax

- `draw 1/0 ___` : view a hand-written predicate
- `set p := ___` : make a key to store a new predicate
- `delete p`     : delete p from key-value store
- `save`         : save the key-value store

Overall, tons of room for improvement --
but Graphviz is limited, so it's not a high priority.

This is mainly a simple proof of concept.