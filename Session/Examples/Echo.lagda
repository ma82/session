[2013-2014 matteo.acerbi@gmail.com](https://www.gnu.org/licenses/gpl.html)

\begin{code}
module Session.Examples.Echo where

open import Session
\end{code}

\begin{code}
open import Control.Concurrent as C
open IO
open import Data.String

Ty : Code
Ty = ⊤ , ⊤ , `Π^ String λ x → `Σ (Σ String (_≡_ x)) (`I _)
\end{code}

The server receives a string and sends back the same string, together
with an (irrelevant) proof of their equality.

\begin{code}
server : [] ∷ (> + , ⊤ , ⊤ , ¡ Ty) [IO ⊤ ]> []
server = accept Z| [] (get Z| λ x → ⇑ putStrLn « "Server received " ++ x »
                                  » write Z| (x , Session.<>)
                                  » ⇑ putStrLn « "Server sent "     ++ x »
                                  » end Z|)
\end{code}

The client connects to the server three times.

\begin{code}
client : [] ∷ (> - , ⊤ , ⊤ , ¡ Ty) [IO ⊤ ]> []
client = twice Z| » twice Z| »
         x <- connect Z| (put Z| "A" » read Z| »= λ x → end Z| » ⇑ return x)
       ⋯ ⇑ putStrLn « "Client received " ++ fst x »
       » y <- connect Z| (put Z| "B" » read Z| »= λ x → end Z| » ⇑ return x)
       ⋯ ⇑ putStrLn « "Client received " ++ fst y »
       » z <- connect Z| (put Z| "C" » read Z| »= λ x → end Z| » ⇑ return x)
       ⋯ ⇑ putStrLn « "Client received " ++ fst z »
       » ⇑ return tt
\end{code}

\begin{code}
main : IO.IO C.<>
main = run test [] >> C.threadDelay C.onesec where
  test = x <- new
       ⋯ fork ([] ,̇ -+) server
       » client
\end{code}
