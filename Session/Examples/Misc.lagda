[2013-2014 matteo.acerbi@gmail.com](https://www.gnu.org/licenses/gpl.html)

\begin{code}
module Session.Examples.Misc where
\end{code}

\begin{code}
open import Session
\end{code}

\begin{code}
module Basic (M : Set → Set)(η : ∀ {X} → X → M X)
             (A : Entry)(B : ⊤ ▹ ⊤) where

  a : [] ∷ (»» (A ⊗ B)) ∷ A [ M ⊢ ⊤ ]> [] ∷ »» B
  a = send Z| Z| »= λ _ → ⇑ η _

  b : [] ∷ (A ⅋ B) «« ∷ A [ M ⊢ ⊤ ]> [] ∷ B ««
  b = send Z| Z| »= λ _ → ⇑ η _

  c : [] ∷ »» (A ⅋ B) [ M ⊢ ⊤ ]> [] ∷ »» B ∷ A
  c = receive Z| »= λ _ → ⇑ η _
\end{code}

\begin{code}
module Ex1 (M : Set → Set)(η : ∀ {X} → X → M X) where

  ex1 : [] [ M ⊢ ⊤ ]> []
  ex1 = new⊤
      » fork ([] ,̇ -+) (  write Z| 42
                        » end   Z|   )
      » _ <- read Z|
      ⋯ end Z|
\end{code}

\begin{code}
open IO ; open C ; open CS
open import Unit as U
open import Data.String

open Ex1 IO return
\end{code}

\begin{code}
ex2 : IOProc _
ex2 = new⊤
    » ⇑ putStrLn « "A channel was created!" »
    » fork ([] ,̇ -+) (  ⇑ putStrLn « "Child has started" »
                      » ⇑ threadDelay onesec
                      » write Z| "Message"
                      » ⇑ putStrLn « "Child has written" »
                      » ⇑ threadDelay onesec
                      » end Z|
                      » ⇑ putStrLn « "Child has finished" »
                      » ⇑ return tt)
    » ⇑ threadDelay onesec
    » s <- read Z|
    ⋯ ⇑ putStrLn « "Parent has received \"" ++ s ++ "\"" »
    » ⇑ threadDelay onesec
    » end Z|
    » ⇑ putStrLn « "Parent has finished" »
\end{code}

\begin{code}
ex3 : IOProc ⊤
ex3 = ⇑ putStrLn « "Enter 0" »
    » l <- new⊤
    ⋯ r <- new⊤
    ⋯ fork ([] ,̇ +- ,̇ +-) (  ⇑ putStrLn « "Enter 1" »
                           » write Z| « "1 -> 0" »
                           » send Z| Z|
                           » a <- read Z|
                           ⋯ ⇑ putStrLn a
                           » ⇑ putStrLn « "Exit 1" »
                           » end Z|)
    » fork ([] ,̇ -  ,̇  +) (  receive Z|
                           » ⇑ putStrLn « "Enter 2" »
                           » write Z| « "2 -> 0" »
                           » end Z|
                           » write Z| « "2 -> 1" »
                           » ⇑ putStrLn « "Exit 2" »
                           » end Z|)
    » x <- read Z|
    ⋯ y <- read Z|
    ⋯ ⇑ (putStrLn x >> putStrLn y >> putStrLn « "Exit 0" »)
    » end Z|
\end{code}

\begin{code}
main : IO C.<>
main = putStrLn « "*** Ex 1 ***" » >>
       run ex1 []                  >>
       putStrLn « "*** Ex 2 ***" » >>
       run ex2 []                  >>
       putStrLn « "*** Ex 3 ***" » >>
       run ex3 []                  >>
       threadDelay onesec
\end{code}
