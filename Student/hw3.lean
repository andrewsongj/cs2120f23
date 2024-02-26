/-!
#1

Define a function, dec' : Nat → Nat, that takes any Nat, n, and that
returns 0 if n is 0 and that otherwise returns one less than n. Hint:
case analysis on n. When you've succeeded the following test cases
should run and return the expected values.
-/
def dec' : Nat → Nat
| Nat.zero     => 0
| (Nat.succ n') => n'

#eval dec' 2    -- expect 1
#eval dec' 1    -- expect 0
#eval dec' 0    -- expect 0

def dec2 : Nat → Nat
| Nat.zero => 0
| 1 => 0
| (Nat.succ (Nat.succ n'')) => n''

/-
#2

Define a function, l2l, polymorphic in two type parameters, α and β, that
also takes a function, f, from α to β and a list of α values and that returns
a  list of corresponding β values. As an example, (l2l Nat.succ [0, 1, 2]) is
expected to return [1, 2, 3]. Write a few test cases where α is String, β is
Nat, and f is String.length. Hint: Use case analysis on the incoming list: it
will be either List.nil or (List.cons h t), the latter of which can also be
written as (h::t).

this is map reduce
-/
def l2l {α β : Type} : (α → β) → (List α) → List β
| f, []      => []
| f, (h::t)  => (f h) :: l2l f t

#eval l2l String.length ["hello", "world", "lean"]    -- expect [5, 5, 4]

/-!
#3

Define a data type, called PRFV (short for "partial function return value"),
polymorphic in one type, α, where a value of this type is either "undefined"
or "defined α". If α is Nat, for example, then you would have (undefined) and
(defined 3) as values of this type. In the case of undefined,, you will have
to disable implicit arguments, as there's no value provided to this constructor
from which Lean can infer α.
-/

inductive PRFV (α : Type)
| undefined
| defined (a : α)


#check @PRFV.undefined Nat    -- expect PRFV
#check PRFV.defined 3         -- Expect PRFV

/-!
#4

Define a variant of dec', called dec, that takes a natural number, n, as an
argument and that returns a (PRFV Nat). This value must be "PFRV.undefined"
if n = 0, reflecting the idea that dec is a partial function, one that is not
defined for the argument value, 0; and that returns one less than n otherwise.
You will thus represent a partial function from Nat to Nat as a total function
from Nat to PRFV Nat.
-/
def dec : Nat → PRFV Nat
| 0     => PRFV.undefined
| (n'+1) => PRFV.defined n'

#reduce dec 2

/-!
#5

Define a function, isZero from Nat to Bool that returns true if its argument
is zero and false otherwise. Write a few test cases to show that it works.
-/
def isZero : Nat → Bool
| 0 => true
| _ => false

#eval isZero 0    -- expect true
#eval isZero 1    -- expect false

/-!
#6

Define a function, isDef, from PFRV α to Bool, that returns false if the given
PFRV α is "undefined" and true otherwise. The following test cases should then
return the expected values.
-/

def isDef {α : Type} : PRFV α → Bool
| PRFV.undefined => false
| PRFV.defined _ => true

#eval isDef (dec 0)   -- expect false
#eval isDef (dec 1)   -- expect true

/-!
The fold right function
-/
-- v1: add up numbers in list
def foldr''' : (Nat → Nat → Nat) → List Nat → Nat
| _, List.nil => 0
| op, h::t => op h (foldr''' op t)

-- that doesnt work for multiplication bc base case of 0, use another arg to indicate the identity base case of 0 or 1
def foldr'' : (Nat → Nat → Nat) → Nat → List Nat → Nat
| _, id, List.nil => id
| op, id, h::t => op h (foldr'' op id t)

#reduce foldr'' Nat.mul 1 [1, 2,3,4,5]

-- foldstr: take list of strings, returns single string in which all given strings are appended using String.append
def foldstr : (String → String → String) → String → (List String) → String
| _, id, List.nil => id
| op, id, h::t => op h (foldstr op id t)

#eval foldstr String.append "" ["tg", "rgr"]

--generalize foldr further so u can do for nat or string or whatever
def foldr' {α : Type} : (α → α → α) → α → List α → α
| _, id, List.nil => id
| op, id, h::t => op h (foldr' op id t)

#reduce foldr' Nat.mul 1 [1, 2,3,4,5]
#eval foldr' String.append "" ["tg", "rgr"]

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
