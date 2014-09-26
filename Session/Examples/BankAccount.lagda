[2013-2014 matteo.acerbi@gmail.com](https://www.gnu.org/licenses/gpl.html)

## Bank account

Example from Brady and Hammond's "Correct-by-Construction Concurrency".

Reference (unsafe) code:

    moveMoney(sum, sender, receiver) {
      lock(sender);
      lock(receiver);
      sendFunds = read(sender);
      recvFunds = read(receiver);
      if (sendFunds < sum) {
        putStrLn("Insufficient funds");
        return;
      }
      write(sender, sendFunds - sum);
      write(receiver, recvFunds + sum);
      unlock(receiver);
      unlock(sender);
    }

Instead of defining safe locking protocols as in the paper, we simply
model the memory locations as processes.

\begin{code}
module Session.Examples.BankAccount where

open import Control.Concurrent as C
open import Session
open import Data.Nat as ℕ
open import IO.Primitive
\end{code}

\begin{code}
moveMoney : (sum : ℕ) →
            [] ∷ (»» (De ⊤ ∋ `Π^ ℕ λ _ → `Σ^ (1+ ℕ) λ _ → `I tt))
               ∷ (»» (De ⊤ ∋ `Π^ ℕ λ _ → `Σ^ (1+ ℕ) λ _ → `I tt))
            [IO ⊤ ]>
            []
moveMoney sum = get (S> Z|) λ sendFunds → 
                get (   Z|) λ recvFunds → 
                respond sum sendFunds recvFunds where
  success : ℕ → ℕ → ℕ → _
  success sum sendFunds recvFunds = put (S> Z|) (> sendFunds) » end (S> Z|)
                                  » put     Z|  (> recvFunds) » end     Z| 
  respond : ℕ → ℕ → ℕ → _
  respond sum  sendFunds recvFunds with compare sendFunds sum -- TODO ≤?
  respond ._   sendFunds recvFunds | less    ._ k = ⇑ putStrLn « "Insufficient funds" »
                                                  » put  (S> Z|) ε » end (S> Z|)
                                                  » put      Z|  ε » end     Z| 
  respond sum  ._        recvFunds | equal   ._   = success sum      0  (sum ℕ.+ recvFunds)
  respond sum  ._        recvFunds | greater ._ k = success sum (suc k) (sum ℕ.+ recvFunds)
\end{code}

\begin{code}
fund : (init : ℕ) → [] ∷ ((De ⊤ ∋ `Π^ ℕ  λ _ → `Σ^ (1+ ℕ) λ _ → `I tt) ««)
                    [IO ℕ ]>
                    []
fund init = put Z| init
          » get Z| (1+.maybe (λ n → end Z| » ⇑ return n   )
                             (      end Z| » ⇑ return init))
\end{code}

\begin{code}
test : IOProc ⊤
test = l <- new
     ⋯ r <- new
     ⋯ fork ([] ,̇ +- ,̇  +) (  res <- fund 10
                            ⋯ ⇑ log "Source = " res)
     » fork ([] ,̇ +  ,̇ +-) (  res <- fund 30
                            ⋯ ⇑ log "Target = " res)
     » moveMoney 8
  where open import Data.Nat.Show
        log : _ → ℕ → IO ⊤
        log xs n = putStr   « xs     » >>
                   putStrLn « show n » >>
                   return _
\end{code}

\begin{code}
main : IO C.<>
main = run test [] >> C.threadDelay C.onesec
\end{code}
