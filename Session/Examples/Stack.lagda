[2013-2014 matteo.acerbi@gmail.com](https://www.gnu.org/licenses/gpl.html)

## Stack

See Toninho, Caires, Pfenning "Higher-Order Processes, Functions, and
Sessions: A Monadic Integration".

\begin{code}
module Session.Examples.Stack where
\end{code}

\begin{code}
open import Base
open import Session
\end{code}

The original type was a ``μ``: processes that interact forever to
build an infinite stack should be forbidden. We temporarily lift the
restriction.

\begin{code}
module AlmostOriginal where

  data Op : Set where push pop dealloc : Op

  Stack : (X : Set) → ⊤ ◂ ⊤
  Stack X = `ν (λ _ → `Π^ Op λ { push    → `Π (X   ) (`I (inr _))
                               ; pop     → `Σ (1+ X) (`I (inr _))
                               ; dealloc →            `I (inl _)  }) _
\end{code}

We cannot implement `stack1` as in the paper, as a direct recursive
definition is not possible.

-- \begin{code}
-- stack1 : ∀ {X} → List X → [] ∷ (»» Stack X) [IO ⊤ ]> []
-- stack1 xs = {!!}
-- \end{code}

We can instead make explicit at the type level (as an index to `` `ν
``) the arguments to the recursive calls.

We also explicitly allow the user of the stack to carry through the
computation data from a type `Y` of her/his/its choice.

\begin{code}
tryPop : {X : Set} → List X → List X
tryPop []       = []
tryPop (xs ∷ _) = xs
\end{code}

We rename `dealloc` to `stop` as we do not actually "deallocate" the
list, in fact we return it.

\begin{code}
data Op : Set where {- reset -} push pop stop : Op

Stack : {X Y : Set} → List X → Y → (ny : Op → List X → Y → Y) → (List X × Y) ◂ List X
Stack is y ny =
  `ν (λ { (xs , y) → `Π^ Op λ { -- reset → `I (inr (is , ny reset xs y))
                                push → `Π^ _ λ x → `I (inr ((xs ∷ x) , ny push xs y))
                              ; pop  → `I (inr (tryPop xs , ny pop xs y))
                              ; stop → `I (inl xs)                        }}) (is , y)
\end{code}

The type looks complicated but the process is straightforward.

\begin{code}
open IO

stack : ∀ {X Y}(xs : List X)(y : Y) ny → [] ∷ »» Stack xs y ny
                                         [IO (List X) ]>
                                         []
stack xs y ny =
  corec Z| (xs , y) λ _ → _ , get Z| λ { push → get Z| λ _ → end Z|
                                       ; pop  → end Z|
                                       ; stop → end Z|              }
\end{code}

Let's see a concrete example.

\begin{code}
open import Data.Nat
open import Data.Bool using (Bool ; true ; false ; not)
open import Relation.Nullary

even : ℕ → Bool
odd  : ℕ → Bool
even zero    = true
even (suc n) = odd n
odd  zero    = false
odd  (suc n) = even n
\end{code}

A user of a stack of booleans which simply pushes `n` alternating
booleans.

\begin{code}
stack-user : (xs : List Bool)(n : ℕ) → [] ∷ Stack xs n (λ _ _ → pred) ««
                                       [IO List Bool ]>
                                       []
stack-user xs n =
  corec Z| (xs , n)
    λ { (ys , m) → _ , (case m ≟ 0 of λ {
                          (yes _) → put Z| stop                   » end Z|
                        ; (no  _) → put Z| push » put Z| (even m) » end Z| }) }
\end{code}

\begin{code}
main : IO.IO C.<>
main = run test [] >> C.threadDelay C.onesec where
  open import Data.Bool.Show
  test = new
       » fork ([] ,̇ +-) (stack-user [] 42 » ⇑ return tt)
       » xs <- stack [] _ _
       ⋯ L.foldl (λ m b → ⇑ putStrLn « show b » » m)
                 (⇑ return tt)
                 xs
\end{code}
