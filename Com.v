
Require Export imports.
Require Export AExp.
Require Export BExp.

Inductive com :=
| Skip : com
| Assign : vname -> aexpr -> com
| Seq : com -> com -> com
| If : bexpr -> com -> com -> com
| While : bexpr -> com -> com.
