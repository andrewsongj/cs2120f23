def comp4 (α : Type) : (α → α) → (α → α)
-- | f => λ a => f (f (f (f a)))
| f => (λ a => (f ∘ f ∘ f ∘ f) a)
-- call incoming function argument f, return the lambda function which takes an argument and return smth
-- takes a function returning alpha to alpha and returns functions returning alpha to alpha term of some type, and return


-- in this function we want to apply the composition an arbitrary n number of times
-- n binds to the nat, f binds to the function arg
-- define two cases
-- is the arg is 10, then n' is bind to 9
def compn {α : Type} : Nat → (α → α) → (α → α)
| Nat.zero, f => λ a => a
| (Nat.succ n'), f => (λ a => f (compn n' f a))

#eval (compn 5 Nat.succ) 0

def e : List Nat := List.nil
def l1 : List Nat := List.cons 1 e
def l2 : List Nat := List.cons 0 l1

#reduce l2
def list_len {α : Type} : List α → Nat
| List.nil => 0
-- head and tail list
| (List.cons h t) => 1 + list_len t

#eval list_len l2
