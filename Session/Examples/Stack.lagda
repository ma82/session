[2013-2014 matteo.acerbi@gmail.com](https://www.gnu.org/licenses/gpl.html)

\begin{code}
module Session.Examples.Stack where
\end{code}

\begin{code}
open import Session
\end{code}

\begin{code}
module AlmostOriginal where

  data Op : Set where push pop dealloc : Op

  Stack : (X : Set) → ⊤ ◂ ⊤
  Stack X = `ν (λ _ → `Π^ Op λ { push    → `Π (X   ) (`I (inr _))
                               ; pop     → `Σ (1+ X) (`I (inr _))
                               ; dealloc →            `I (inl _)  }) _
\end{code}

\begin{code}
tryPop : {X : Set} → List X → List X
tryPop []       = []
tryPop (xs ∷ _) = xs
\end{code}

\begin{code}
data Op : Set where {- reset -} push pop stop : Op

Stack : {X Y : Set} → List X → Y → (ny : Op → List X → Y → Y) → (List X × Y) ◂ List X
Stack is y ny =
  `ν (λ { (xs , y) → `Π^ Op λ { -- reset → `I (inr (is , ny reset xs y))
                                push → `Π^ _ λ x → `I (inr ((xs ∷ x) , ny push xs y))
                              ; pop  → `I (inr (tryPop xs , ny pop xs y))
                              ; stop → `I (inl xs)                        }}) (is , y)
\end{code}

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

\begin{code}
open import Control.Concurrent as C
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
                 (⇑ return true)
                 xs
\end{code}
