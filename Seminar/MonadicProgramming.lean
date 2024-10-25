/- Author: Arend Mellendijk -/

import Mathlib
set_option autoImplicit false

/- Our aim is to give a quick runthrough of monadic programming.

For a more detailed introduction to functional programming in lean, see [Functional programming in Lean](https://lean-lang.org/functional_programming_in_lean/)

[The Lean 4 manual](https://lean-lang.org/lean4/doc/) has some good information about the specific monads covered in this talk.
-/

/-
In imperative languages a program is a series of instructions that are executed in sequence. These steps have all sorts of "side effects", like creating a file or printing to the console.

In functional languages a program is like a mathematical definition. Variables cannot be reassigned. The output depends only on the input. If two functions output the same value, replacing one with the other will not cause your program to compute a different result.
-/

def square (n : Rat) : Rat := n^2

def sum : List Rat → Rat
| [] => 0
| a :: as => a + sum as

/- Variables in Lean are immutable. The `let` is a definition, and cannot be modified. -/
def sqNorm (l : List Rat) : Rat :=
  let squares := List.map square l
  sum squares

#eval sqNorm [1, 4, 1/2]

/- Monads are a way to do imperative-style programming in a functional language. All functions are still pure, but any side-effects are stored in the return type, hidden from the programmer. `IO` (input-output) is the monad that gives us access to the console and file system. The return type `IO Nat` indicates that the function returns a natural number and has IO side-effects. -/
def printHelloAndReturn3 : IO Nat := do
  IO.println "Hello, World!"
  return 3

#eval printHelloAndReturn3

/- `do` notation lets us write programs like we would in the imperative world. Functions in a `do`-block are executed in order, and any side-effects they have are tracked under the hood by the monad.-/

def twoPlusThreeHelloWorld : IO Nat := do
  /- the ← lets us access the value returned by `printHelloAndReturn3`-/
  let three ← printHelloAndReturn3
  IO.println s!"Adding 2 and {three}"
  return 2 + three

#eval twoPlusThreeHelloWorld


/- The Reader Monad.
The reader monad carries around some pre-defined bit of state that cannot be changed. When calling another function within the same monad, you do not have to pass this state manually. This is mostly useful for keeping track of configuration settings.

You can access this state using the function
`read : ReaderM α α`
Its type tells you that `read` lives in the monad `ReaderM α`, and returns a value of type `α`.
-/

inductive Lang where
| EN : Lang
| DE : Lang

structure Config where
  language : Lang
  name : String

def getLanguage : ReaderM Config Lang := do
  let config ← read
  return config.language

def getName : ReaderM Config String := do
  return (← read).name

def getLocalizedHello : ReaderM Config String := do
  let lang ← getLanguage
  return match lang with
  | .EN => "Hello"
  | .DE => "Hallo"

def greetingBuilder : ReaderM Config String := do
  let hello ← getLocalizedHello
  let name ← getName
  return s!"{hello}, {name}"

def greeting (name : String) (language : Lang) : String :=
  (greetingBuilder).run ⟨language, name⟩

#eval greeting "Floris" .DE

/- The State Monad.
Not having to pass configuration values to every sub-function is nice, but sometimes we do want to be able to modify the ambient state. This is what the `StateM α` monad is for. One should think of `f : StateM α β` as a function with no inputs, that produces a value of type `β` and depends on and affects some ambient value of type `α`-/

structure primeSieve where
  isPrime : Array Bool
  primes : List Nat
deriving Repr

def addPrime (p : Nat) : StateM primeSieve Unit := do
  modify fun sieve =>
    { sieve with primes := p :: sieve.primes }

def setNotPrime (n : Nat) : StateM primeSieve Unit := do
  modify fun sieve =>
    { sieve with isPrime := sieve.isPrime.set! n false}
  -- This return is optional, as is the ()
  return ()

#eval Array.set! #[0, 4, 52] 0 14
#eval Array.set! #[0, 4, 52] 10 14

def isPrime (n : Nat) : StateM primeSieve Bool := do
  let sieve ← get
  return sieve.isPrime[n]!

def eratosthenes (n : Nat) : StateM primeSieve (List Nat) := do
  set (⟨mkArray n true, []⟩ : primeSieve)
  for p in [2:n] do
    if ← isPrime p then
      addPrime p
      -- for (int k = 2*p; k < n; k += p)
      for k in [2*p : n : p] do
        setNotPrime k
  return (← get).primes.reverse

def primesLt (n : Nat) : List Nat :=
  ((eratosthenes n).run ⟨#[], []⟩).1

#eval primesLt 100

/- The Except Monad.
The `Except` monad allows us to throw errors of a specified type. Once an error has been thrown, all subsequent operations are no longer executed.-/

def divide (m n : Rat) : Except String Rat := do
  if n == 0 then
    throw "Division by zero error."
  return m / n

def H_oops (n : Nat) : Except String Rat := do
  let mut s := 0
  for i in [0 : n] do
    s := s + (← divide 1 i)
  return s

#eval H_oops 6

/- do-blocks have special support for exception handling using try-catch blocks-/
def H (n : Nat) : Except String Rat := do
  let mut s := 0
  for i in [0 : n] do
    try
      s := s + (← divide 1 i)
    catch
    | err =>
      dbg_trace s!"On iteration {i} got error message {err}"
  return s
#eval H 6


def doubleNat (s : String) : Except String String := do
  let mut total : Nat := 0
  for c in s.toList do
    if c.isDigit then
      total := 10*total + (c.toNat - ('0'.toNat))
    else
      throw s!"Character '{c}' is not a digit."
  return s!"{2*total}"

#eval doubleNat "494234"
#eval doubleNat "12312.24"

def shout (s : String) : Except String String := do
  return s ++ "!"

def doubleNatElseShout (s : String) : Except String String :=
  (doubleNat s) <|> (shout s)

#eval doubleNatElseShout "494234"
#eval doubleNatElseShout "12312.24"

/- Consider a function like `map : (α → β) → List α → List β` that takes a function and a list, applies the function to all elements in the list and returns the resulting list. This function is pure, meaning that you can't apply it to a function with monadic side effects.

If you do want to map a function with side effects onto a list, you can reach
List.mapM : (α → IO β) → List α → IO (List β) -/

def print_numbers (n : ℕ) :=
    List.mapM IO.println (List.range n)
/- Ask yourself: What is the type of `print_numbers`?-/

#eval print_numbers 10

/- Many of the operators on lists have monadic variants. Consider `filter : (α → Bool) → List α → List α` that removes elements from a list that do not satisfy a given predicate. If your predicate function has side-effects in some monad `m`, you will have to use `filterM : (α → m Bool) → List α → m (List α)` instead.-/
def hasSpace : StateM Int Bool := do
  if (← get) == 0 then
    return false
  modify fun n => n-1
  return true

def takeN_helper {α : Type} (l : List α) : StateM Int (List α) :=
  filterM (fun _ => hasSpace) l

def take {α : Type} (n : Nat) (l : List α) : List α :=
  (takeN_helper l).run' n

#eval take 5 (List.range 10)


/- Monad tranformers.
Let's say you want to store some global state, and also throw an exception if something goes wrong. None of the monad we discussed are able to help you, but they each have a monad combinator that allows you to add their functionality to an existing monad. (IO is the exception here: it does not have a combinator). They are called ReaderT, StateT and ExceptT. If you want a state monad that stores a natural numbers can also handle exceptions by throwing a string, you would write ExceptT String (StateM Nat)
-/

def decrement : ExceptT String (StateT Nat IO) Unit := do
  let n ← get
  match n with
  | 0 => do
    throw "Cannot decrement zero!"
  | k+1 => do
    IO.println s!"New value is {k}"
    set k


/- If you want to use `do` notation to define a pure function, you can use the `Id` monad. It does not not store any state. `n : Id Nat` is just a natural number. You can use `Id.run : Id α → α` to exit the monad. Here we prepend it to the `do` block so that it knows to execute the code in the `Id` monad. -/

def sum' (l : List Nat) : Nat := Id.run do
  let mut s := 0
  for n in l do
    s := s + n
  return s

#eval sum' [1,2,4,4]

/- To define your own monad you need to provide a way to return a value (the `pure` function), and a way to compose two functions that keeps track of both their side effects (`bind`). -/
instance : Monad Option where
  pure a := Option.some a
  bind x f := match x with
    | .some n => f n
    | .none => none

#synth Monad List
