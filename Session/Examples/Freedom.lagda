[2013-2014 Matteo Acerbi](https://www.gnu.org/licenses/gpl.html)

# (Deadlock-freedom)-freedom

\begin{code}
module Session.Examples.Freedom where

open import Session
\end{code}

\begin{code}
module M (M : Set → Set)(η : ∀ {X} → X → M X)(A : Set) where
\end{code}

\begin{code}
  p : ∀ {Γ si sj}(i : (> si , ⊤ , ⊤ , ([ si ]Π A $ `I _)) ∈ Γ   ) →
                 (j : (> sj , ⊤ , ⊤ , ([ sj ]Σ A $ `I _)) ∈ rm (∈ud i)) →
                  Γ [ M ⊢ A ]> rm (∈ud j)
  p i j = read i    »= λ a → end (∈ud i) »
          write j a »= λ _ → end (∈ud j) »
          ⇑ (η a)
\end{code}

\begin{code}
  S : 1+ Side × Code
  S = (ε , ⊤ , ⊤ , `Σ A (`I _))

  CA = S ; BC = S ; AB = S

  abC : [] ∷ CA ∷ BC ∷ AB [ M ⊢ A ]> []
  abC = -- fork process A which reads from CA and writes on AB
        fork ([] ,̇ -+ ,̇ + ,̇ +-) (p (Z|   ) Z| » ⇑ η tt)
        -- fork process B which reads from AB and writes on BC
      » fork ([] ,̇ +  ,̇ +- ,̇ -) (p (S> Z|) Z| » ⇑ η tt)
        -- become process C which reads from BC and writes on AC
      » p (S> Z|) Z|

  test : [] [ M ⊢ A ]> []
  test = new » new » new » abC
\end{code}

\begin{code}
open import IO.Primitive
open import Unit as U

open M IO return ⊥ -- !!!

main : IO U.<>
main = run test [] >>= ((λ ()) ∘ fst) -- !!!
\end{code}
