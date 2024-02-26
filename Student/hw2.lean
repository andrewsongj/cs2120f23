/-!
(1) Write a function called add that takes two natural
numbers, a and b, and returns their sum, a + b.
Hint: do case analysis on the second argument
(a Nat can be either Nat.zero or (Nat.succ n') and
use the fact that n + (1 + m) = 1 + (n + m).
-/
def add : Nat → Nat → Nat
| n, Nat.zero => n
| n, (Nat.succ m) => Nat.succ (add n m)

#eval add 6 7

/-!
(2) Write a function called append, polymorphic in a type, T,
that takes two lists values, n and m of type List T and that
returns the result of appending the two lists.
For example, append [1,2,3] [4,5,6], should return [1,2,3,4,5,6].
Hint: It's very much list Nat addition.
-/
