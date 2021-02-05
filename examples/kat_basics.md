```
PRIMITIVE PREDICATES
alpha ::= command = C
        | room = R
        | in(inventory, I)
        | pantry_door_locked = true

PRIMITIVE ACTIONS
pi ::= command := C
     | room := R 
     | insert(inventory, I)
     | pantry_door_locked := B

PREDICATES
a, b ::= alpha
       | a /\ b
       | a \/ b
       | !a
       | true
       | false

ACTIONS
p, q ::= pi
       | a
       | p;q
       | p+q
       | p*
       
if a then p else q
  == a;p + !a;q

logic = 
(if command = north
 then if room = foyer 
      then room := dining
      else if room = kitchen /\ !pantry_door_locked
      then room := pantry
      else fail
 else ...)
 
player = (command := north + command := south + ...)

game = (player;logic)*
```

It is possible to decide if `p == q` (i.e., they behave the same on
all traces).

So, we can ask:

```
game 
== 
(player;logic;
 if room = pantry /\ !in(inventory, key)
 then fail
 else ok)*
```

Which basically asks... is playing the game the same as playing the
game and being in the pantry without the key at some point?

A clearer way to put it, using temporal logic:

```
game
==
game;!EVER(room = pantry /\ !in(inventory, key))
```
