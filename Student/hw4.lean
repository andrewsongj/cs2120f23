--reduce a list of strings to a bool that is true if all string in list have even length
--takes string and answer for rest of list and returns a bool
--def foldr : (String → Bool → Bool) → Bool → List String → Bool

def foldr {α β : Type} : (α → β → β) → β → List α → β
| op, id, List.nil => id
| op, id, (h::t) => op h (foldr op id t)

def isEvenLen : String → Bool := λ s => s.length%2 ==0
def combine : String → Bool → Bool
| s, b => and (isEvenLen s) b

#eval foldr combine true []
#eval foldr combine true ["hello,","lean"]
#eval foldr combine true ["hello,","lean!"]

--tkae string at head of list and answer for the rest of the list,a bool, and returns a bool
--reduce head of list to a bool and combine the answer of the head for the answer of the rest

--need to make sure that the id is really the identity element for op

structure my_monoid (α : Type) where
(op: α → α → α)
(id : α)
(left_id : ∀ (a : α), op id a = a)
(right_id : ∀ (a : α), op a id = a)

def a_monoid : my_monoid Nat := my_monoid.mk Nat.add 0 sorry sorry

#check my_monoid

#check Empty
