[2013-2014 Matteo Acerbi](https://www.gnu.org/licenses/gpl.html)

TODO Merge with AD

\begin{code}
module Session.Base where
\end{code}

\begin{code}
data   ⊥ {l} : Set l where
\end{code}

\begin{code}
record ⊤ {l} : Set l where constructor tt
\end{code}

\begin{code}
open import Function  public
\end{code}

\begin{code}
open import Data.List public using (List ; [])
module L = Data.List

infixl 5 _∷_
pattern _∷_ xs x = x L.∷ xs
\end{code}

\begin{code}
open import Data.Product public
  using    (Σ ; _×_ ; _,_ ; ,_)
  renaming (proj₁ to fst ; proj₂   to snd
           ;curry to cu  ; uncurry to uc)
module Σ = Data.Product

mapΣ : ∀ {lA lB lP lQ}
         {A : Set lA}{B : Set lB}{P : A → Set lP}{Q : B → Set lQ} →
         (f : A → B)(g : ∀ x → P x → Q (f x)) → Σ A P → Σ B Q
mapΣ f g = Σ.map f (g _)
\end{code}

\begin{code}
open import Data.Maybe public
  using () renaming (Maybe to 1+ ; just to > ; nothing to ε)
module 1+ = Data.Maybe
\end{code}

Needed by Simple

\begin{code}
infixl 4 _‼_
pattern _‼_ xs x = xs ∷ (> (_,_ _ (_,_ _ x)))
-- pattern ♯_ x = _,_ _ (_,_ _ x)
\end{code}

\begin{code}
import Level as Le ; module Level = Le ; open Le

⟰ : {l1 : Level}(lδ : Level) → Set l1 → Set (l1 ⊔ lδ)
⟰ lδ X = Lift {_}{lδ} X

Π : ∀ {lA lB}(A : Set lA) → (A → Set lB) → Set _
Π A B = ∀ a → B a

infixr 4 _⇛_

_⇛_ : ∀ {lI}{I : Set lI} → ∀ {lX} → (I → Set lX) → ∀ {lY} → (I → Set lY) → Set _
P ⇛ Q = ∀ i → P i → Q i

open import Relation.Binary.PropositionalEquality public
  using (_≡_ ; subst ; Extensionality ; cong ; cong₂)
  renaming (refl to <>)
module ≡ = Relation.Binary.PropositionalEquality

_Π≡_ : ∀ {a b}{A : Set a}{B : A → Set b}(f g : ∀ x → B x) → Set _
f Π≡ g = ∀ x → f x ≡ g x

IsProp : ∀ {l}(A : Set l) → Set l
IsProp A = (p q : A) → p ≡ q
\end{code}

TODO Use □List from Mod.Base instead.

\begin{code}
open import Data.List.All public
  using    (All ; [])
  renaming (map to □map)

module □List = Data.List.All
\end{code}

TODO Avoid this horror by defining All via Σ by recursion.
     (You have one in Mod.Base)

\begin{code}
infixl 4 _,̇_ -- press comma and then slash dot
pattern _,̇_ ps p = □List._∷_ p ps
\end{code}

\begin{code}
elim_to_[]⟼_∷⟼_ :
  ∀ {lI}{I : Set lI}{lX}{X : I → Set lX}{lP}
    {is}(xs : All X is)
    (P : {is : List I} → All X is → Set lP)
    (m[] : P [])
    (m∷ : ∀ {i}(x : X i){is}{xs : All X is} → P xs → P (xs ,̇ x)) →
    P xs
elim []       to P []⟼ m[] ∷⟼ m∷ = m[]
elim (ps ,̇ p) to P []⟼ m[] ∷⟼ m∷ = m∷ _ (elim ps to P []⟼ m[] ∷⟼ m∷)
\end{code}

\begin{code}
allK : ∀ {lI}{I : Set lI}{xs : List I}{lX}{X : Set lX} →
       All (λ (_ : I) → X) xs → List X
allK []       = []
allK (ps ,̇ p) = allK ps ∷ p
\end{code}

TODO Move to `Ix` from `AD` instead.
TODO Use `⋄List` from AD, instead?

\begin{code}
open import Data.List.Any as Any public
  using    (Any ; module Membership-≡)
  renaming (here to Z>_ ; there to S>_)

pattern Z| = Z> <>

open Membership-≡ public
\end{code}

\begin{code}
module _ {lA}{A : Set lA}{lP}{P : A → Set lP} where

  rm : {xs : List A} → Any P xs → List A
  rm (Z>_ {_}{xs} px) = xs
  rm (S>_ {x}      i) = rm i ∷ x

  prefix : {xs : List A} → Any P xs → List A
  prefix (Z>_ {_}{xs} px) = []
  prefix (S>_ {x}      i) = prefix i ∷ x

  suffix : {xs : List A} → Any P xs → List A
  suffix (Z>_  {_}{xs} px) = xs
  suffix (S>_ {x}       i) = suffix i
\end{code}

\begin{code}
  ud : {xs : List A} → A → Any P xs → List A
  ud a (Z>_ {_}{xs} px) = xs          ∷ a
  ud a (S>_ {x}      i) = ud a i ∷ x

  ∈ud : {x : A}{xs : List A} → (i : Any P xs) → x ∈ ud x i
  ∈ud (Z> px) = Z> <>
  ∈ud (S>  i) = S> ∈ud i
\end{code}

In `lookupAll`'s type `Any P xs` should read `Ix xs` (`= Any (λ _ → ⊤) xs`).

We should have probably used `Ix` instead.

TODO Add lookup□ to Mod.Base

\begin{code}
  module _ {lQ}{Q : A → Set lQ} where

    lookupAll : {xs : List A} → Any P xs → All Q xs → Σ _ Q
    lookupAll (Z> _) (_  ,̇ q) = , q
    lookupAll (S> i) (qs ,̇ q) = lookupAll i qs
\end{code}

TODO name?

\begin{code}
    wk/ : {xs : List A}(i : Any P xs) → Any Q (rm i) → Any Q xs
    wk/ {xs ∷ x} (Z> _ ) (q   ) = S> q
    wk/          (S> i ) (Z> q) = Z> q
    wk/          (S> i ) (S> a) = S> wk/ i a
\end{code}

\begin{code}
    all-rm : {xs : List A}(j : Any P xs) → All Q xs → All Q (rm j)
    all-rm (Z> _) (qs ,̇ _) = qs
    all-rm (S> j) (qs ,̇ q) = all-rm j qs ,̇ q

    all-ud : {xs : List A}{a : A}
             (j : Any P xs) → All Q xs → Q a → All Q (ud a j)
    all-ud (Z> _) (qs ,̇ _) qa = qs ,̇ qa
    all-ud (S> j) (qs ,̇ q) qa = all-ud j qs qa ,̇ q
\end{code}

TODO rename, clean-up

\begin{code}
open import Data.String using (toCostring)

«_» = toCostring
\end{code}

\begin{code}
import Data.Sum
module ⊎ = Data.Sum
  renaming (inj₁ to inl ; inj₂ to inr ; map to map⊎)
open ⊎ public
\end{code}

\begin{code}
data Side : Set where + - : Side

infix 7 −_

−_ : Side → Side
− + = -
− - = +

−-inv : ∀ {s} → s ≡ − − s
−-inv { + } = <>
−-inv { - } = <>
\end{code}

TODO. Avoid?

\begin{code}
module Σ̂ where
  infixr 6 %_

  record Σ̂ {lA}(A : Set lA){lB}(B : A → Set lB) : Set (lA ⊔ lB) where
    constructor %_
    field      {l̂} : A
               r̂   : B l̂
  open Σ̂ public

  infixr 4 _,̂_

  pattern _,̂_ x y = %_ {l̂ = x} y
\end{code}

\begin{code}
  infixr 6 %%_
  pattern %%_ x = % % x

  infixr 6 %2_ %3_ %4_ %5_ %6_ %7_ %8_
  pattern %2_ x = %%   x
  pattern %3_ x = %2 % x
  pattern %4_ x = %3 % x
  pattern %5_ x = %4 % x
  pattern %6_ x = %5 % x
  pattern %7_ x = %6 % x
  pattern %8_ x = %7 % x

  infixl 4 _⟫_
  pattern _⟫_ xs x = xs ∷ > (%2 x)
\end{code}

\begin{code}
  infixr 6 »»_
  infixl 6 _««

  pattern »»_ x = > + , %2 x
  pattern _«« x = > - , %2 x
\end{code}

\begin{code}
open import Function using (_∘_)

open import Data.List using (List)
\end{code}
