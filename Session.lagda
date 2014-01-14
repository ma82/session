[2013-2014 Matteo Acerbi](https://www.gnu.org/licenses/gpl.html)

# Linear dependent session types [WIP]

What follows is an incomplete draft: do not read this unless given
explicit permission by the author. :-)

## Introduction

This document describes and contains an Agda implementation of an
embedded concurrent language with linear dependent session types.

The reader must be warned that in this work we are using Agda *only*
to try and mimic features typical of a session typed process calculi
with a by-construction well-typed representation: we are in no way in
the position to prove any correspondence with a logical system.

We nonetheless adopt notations and ideas from more theoretical works
in the fields of process algebras and linear logic, in particular from
Philip Wadler's "Propositions as Sessions" paper (for the main type
and terms constructs), and from the recent line of work by Caires,
Pfenning and Toninho (on monadic syntax, corecursion and dependent
types).

The immediate goal of this development is not to formalise a typed
process calculus, but to allow Agda users to experiment with an
*embedded* concurrency-oriented DSL: before attempting to prove the
properties of the system or even of specific processes, we aim at
designing a programmer-friendly interface.

We provide an evaluation function making use of the Haskell FFI: it is
therefore possible to compile and execute programs in the DSL as
Haskell process (see the [README](http://github.com/ma82/session/) for
instructions on how to attempt compilation). Note that in order to
obtain the evaluator (see the end of this file) we had to (locally)
disable totality checking and to use `unsafeCoerce` in several places.

We are currently studying how to define a total non-deterministic
reference semantics which will allow formalised reasoning concerning
the concurrent execution of processes.

\begin{code}
module Session where

open import Base
\end{code}

## Types

The syntax for types is heavily inspired by both *Strictly Positive
Families* (the version in Peter Morris's PhD thesis) and (indexed)
*Descriptions* (Chapman et al, "The Gentle Art of Levitation").

In our case, however, we do not want to describe indexed functors: we
just want to be able to close the language under a (greatest) fixpoint
operator/binder `` `nu ``, allowing nested usages thanks to a
"well-typed Bird-Paterson" encoding of binding.

To compare with the cited universes, note that if we tried to give a
`(I → Set) → (O → Set)` semantics to the `` `I ``, `` `Σ `` , `` `Π ``
, `` `ν `` codes we would have to ignore the input of type `O`: in any
case, such an interpretation would not make much sense here.

As opposed to Wadler's CP, the typing rules for the additional
constructors `⊗`, `⅋`, `¡`, `¿` will not correspond directly to those
of classical linear logic: however, the corresponding syntax maintains
similar operational meaning (channel transmission and client/server
interactions).

We add a type called `Side` (endpoint of a channel), with two only
inhabitants: `+`, `-` . `Entry` is a type of optionally "sided"
(session typed) codes, where absence of a side corresponds to the
session not having started yet.

When a `Side` is specified, the `Entry` corresponds to an obligation
for the process that contains it in its (input) context: if it is `+`
then the session type is to be interpreted without changes, otherwise
the process must behave along that channel by following the *dual*
obligation (receiving vs sending, reading vs writing, connecting vs
accepting).

Note that for what concerns `_⊗_` and `_⅋_` a whole `Entry` is
required as the description of how a process participates to a channel
needs to be preserved by the transfer.

\begin{code}
mutual 

  De    = λ I → I ▹ ⊤
  Code  = Σ _ λ I → Σ _ λ O → I ▹ O
  Entry = 1+ Side × Code

  data _▹_ (I O : Set) : Set₁ where
\end{code}

- Exiting a session

\begin{code}
    `I      :                     (i : I) → I ▹ O
\end{code}

- Writing and reading values

\begin{code}
    `Σ `Π   : (S : Set)(T : I ▹ S)        → I ▹ O
\end{code}

- Dependency on previously exchanged values

\begin{code}
    `^      : (T : O → De I)              → I ▹ O
\end{code}

- Sending and receiving channels

\begin{code}
    _⊗_ _⅋_ : (L : Entry)(R : I ▹ O)      → I ▹ O
\end{code}

- Servers and clients

\begin{code}
    ¡_ ¿_   : Code                        → I ▹ O
\end{code}

- Corecursion

\begin{code}
    `ν      : (F : O → De (I ⊎ O))(o : O) → I ▹ O
\end{code}

\begin{code}
`Σ^ `Π^ : {I O : Set}(S : Set)(T : S → De I) → I ▹ O
`Σ^ S T = `Σ S (`^ T)
`Π^ S T = `Π S (`^ T)
\end{code}

\begin{code}
_◂_ : Set → Set → Set₁
O ◂ I = I ▹ O
\end{code}

This representation of the language of types should not be considered
definitive but it seems reasonably effective.

Other approaches, where the session types inductive definition `_▹_`
would only have one parameter (as in *Descriptions*), seemed more
difficult to implement and led to more awkward encodings of the
syntax: we probably did not try all the possibilities, though.

### Types and sides

A "sided" type former (code) `[_]F` is the type former (code) `F` when
the side is `+`, the *dual* of `F` when it is `-`.

\begin{code}
[_]Σ   [_]Π   : Side  → {I O : Set}(S : Set)(T : I ▹ S)    → I ▹ O
[_]Σ^  [_]Π^  : Side  → {I O : Set}(S : Set)(T : S → De I) → I ▹ O
_[_]⊗_ _[_]⅋_ : Entry → Side → {I O : Set} → I ▹ O         → I ▹ O
[_]¡_  [_]¿_  : Side  → Code  → {I O : Set}                → I ▹ O
[ + ]Σ     = `Σ
[ - ]Σ     = `Π
[ + ]Π     = `Π 
[ - ]Π     = `Σ 
[ s ]Σ^ S T = [ s ]Σ S (`^ T)
[ s ]Π^ S T = [ s ]Π S (`^ T)
L [ + ]⊗ R = L ⊗ R
L [ - ]⊗ R = L ⅋ R
L [ + ]⅋ R = L ⅋ R
L [ - ]⅋ R = L ⊗ R
[ + ]¡ F   = ¡ F    
[ - ]¡ F   = ¿ F    
[ + ]¿ F   = ¿ F     
[ - ]¿ F   = ¡ F
\end{code}

### Contexts

A context is a simple list of entries, i.e. codes paired with an
optional side. Absence of the side corresponds to the session not
being started yet: in this situation we say that the channel is "new".

\begin{code}
Cx = List Entry
\end{code}

`is¿` means "is it safe to duplicate this entry?".

\begin{code}
is¿ : Entry → Set
is¿ (> + , (_ , _ , ¿ F)) = ⊤
is¿ (> - , (_ , _ , ¡ F)) = ⊤
is¿  _                    = ⊥
\end{code}

To construct a server we must check (at compile time) that it will be
safe to duplicate all the channels that its runtime copies will have
access to: `All¿` is the predicate over contexts which corresponds to
this condition.

\begin{code}
All¿ : Cx → Set _
All¿ = All is¿
\end{code}

### Splitting contexts

We need to define what it means to split an (input) context in two.

\begin{code}
data SplitNew : Set where 
  + - +- -+ : SplitNew

Split : 1+ Side × Code → Set
Split (> _ , x) = Side
Split (ε   , x) = SplitNew

split : (τ : 1+ Side × Code) → Split τ → Cx × Cx → Cx × Cx
split (> s , C)  + (L , R) = (L ∷ (> + , C)) ,  R
split (> s , C)  - (L , R) =  L              , (R ∷ (> + , C))
split (ε   , C)  + (L , R) = (L ∷ (ε   , C)) ,  R
split (ε   , C)  - (L , R) =  L              , (R ∷ (ε   , C))
split (ε   , C) +- (L , R) = (L ∷ (> + , C)) , (R ∷ (> - , C))
split (ε   , C) -+ (L , R) = (L ∷ (> - , C)) , (R ∷ (> + , C))
\end{code}

At `fork` time, if `Γ` is the input context, the user is asked to
inhabit a `Splits Γ`, whose meaning as a pair of contexts is given by
`splits`.

\begin{code}
Splits : ∀ Γ → Set _
Splits = All Split

splits : ∀ {Γ} → Splits Γ → Cx × Cx
splits []       = [] , []
splits (ds ,̇ s) = split _ s (splits ds)
\end{code}

`all-splits` is a generic functions which allows to lift `splits` to
"boxed" predicates.

\begin{code}
all-splits : ∀ {lP}{P : Code → Set lP}{Γ} →
                     All (P ∘ snd) Γ →
                (d : Splits Γ)       → 
                     All (P ∘ snd) (fst (splits d))
                   × All (P ∘ snd) (snd (splits d))
all-splits                      ps       []         =
  [] , []
all-splits {Γ = Γ ∷ (ε   , C)} (ps ,̇ p) (ds ,̇    +) =
  Σ.map (flip _,̇_ p)  id          (all-splits ps ds)
all-splits {Γ = Γ ∷ (ε   , C)} (ps ,̇ p) (ds ,̇    -) =
  Σ.map  id          (flip _,̇_ p) (all-splits ps ds)
all-splits {Γ = Γ ∷ (ε   , C)} (ps ,̇ p) (ds ,̇   +-) = 
  Σ.map (flip _,̇_ p) (flip _,̇_ p) (all-splits ps ds)
all-splits {Γ = Γ ∷ (ε   , C)} (ps ,̇ p) (ds ,̇   -+) =
  Σ.map (flip _,̇_ p) (flip _,̇_ p) (all-splits ps ds)
all-splits {Γ = Γ ∷ (> _ , C)} (ps ,̇ p) (ds ,̇    +) = 
  Σ.map (flip _,̇_ p)  id          (all-splits ps ds)
all-splits {Γ = Γ ∷ (> _ , C)} (ps ,̇ p) (ds ,̇    -) = 
  Σ.map  id          (flip _,̇_ p) (all-splits ps ds)
\end{code}

We use some patterns to deal more easily with dependent tuples and
objects of type `Entry`.

\begin{code}
pattern %_  x = _ , x
pattern %2_ x = % %  x
pattern %3_ x = % %2 x
pattern %4_ x = % %3 x

pattern »»_ x = > + , %2 x
pattern _«« x = > - , %2 x
\end{code}

## Terms

## Introduction

Here we would like to provide a human-readable representation of the
syntax which is encoded below, also discussing the choice of encoding.

For now we limit ourselves to illustrating the Agda code step-by-step.

### Functors

We define several (indexed) functors: we will obtain our process
syntax by taking their fixpoint. While in the future we plan to move
to codes for a universe of functors such as the ones cited above, for
the purpose of illustrating the method we do not want to add further
complications.

Most of the productions are non-recursive, so we will first define
some families in `Ty`.

\begin{code}
private Ty = Cx → Cx → Set₁
\end{code}

The functor corresponding to the `new` grammar production/constructor
simply imposes that the output context contains a *new* channel,
i.e. a channel whose side is `ε` (`Maybe.nothing`).

\begin{code}
New : Ty
New Γ Δ = Σ _ λ F → Δ ≡ Γ ∷ ε , F
\end{code}

We can send and receive channels along channels: in the former case
the sent session type is omitted from the output context, in the
latter the context is extended with the entry corresponding to the
received channel.

\begin{code}
Send Receive : Ty
Send Γ Δ = Σ (Entry × Side × Code) λ W →
           let L , s , %2 R = W in
           Σ (                      L ∈ Γ   ) λ i →
           Σ ((> s , %2 (L [ s ]⊗ R)) ∈ rm i)
             (_≡_ Δ ∘ ud (> s , _ , _ , R))
Receive Γ Δ = Σ (Side × _ × Code) λ W →
              let s , L , _ , _ , R = W in
              Σ ((> s , %2 (L [ s ]⅋ R)) ∈ Γ) λ i → 
                Δ ≡ ud (> s , %2 R) i ∷ L
\end{code}

Writing to and reading from channels changes the type accordingly,
without necessarily introducing dependencies.

\begin{code}
Write Read : Ty
Write Γ Δ = Σ (Σ Code λ { (I , J , T) → J × Side × Set }) λ W →
            let (I , J , T) , j , s , O = W in
            Σ ((> s , I , O , [ s ]Σ J T) ∈ Γ)
              (_≡_ Δ ∘ ud (> s , %2 T))
Read Γ Δ = Σ (Code × Side × _) λ W →
           let (I , J , T) , s , O = W in
           Σ ((> s , I , O , [ s ]Π J T) ∈ Γ)
             (_≡_ Δ ∘ ud (> s , %2 T))
\end{code}

This functor "consumes" `` `^ `` from the session type: it "allows"
you to choose a value from which the rest of the type is dependent,
but *most often* this value will be forced by the type.

\begin{code}
At : Ty
At Γ Δ = Σ (Σ _ λ I → Σ _ λ O → Σ (O → De I) λ _ → O × Side) λ W →
         let I , O , T , o , s = W in
         Σ ((> s , %2 `^ T) ∈ Γ)
            (_≡_ Δ ∘ ud (> s , %2 T o))
\end{code}

Session types have "identity" codes `` `I `` as leaves, so to end a
session we need to consume it and remove the type from the context.

\begin{code}
End : Ty
End Γ Δ = Σ (Σ Set λ I → Set × I × Side) λ W →
          let I , O , i , s = W in
          Σ ((> s , (I , O , `I i)) ∈ Γ)
            (_≡_ Δ ∘ rm)
\end{code}

The following definitions are actual (strictly positive) indexed
functors: calls to the `F` argument correspond to recursion in the
grammar.

When forking, we need to split the input context sensibly (see
`Splits` above): the child must do *all* `ΓR`, the continuation must
do `ΓL`.

\begin{code}
Fork : Ty → Ty
Fork F Γ Δ = Σ (Splits Γ) λ ds →
             let ΓL , ΓR = splits ds in
               F ΓR []
             × Δ ≡ ΓL
\end{code}

A server process can only be launched in a context where it is
possible to duplicate all channels.

The server is located on the `+` side of the channel.

\begin{code}
Server : Ty → Ty
Server F Γ Δ = Σ (Code × Side × _) λ W → let A , s , I , O = W in
               Σ ((> s , I , O , [ s ]¡ A) ∈ Γ) λ i →
                 All¿ Δ
               × F (ud (> + , A) i) Δ
               × Δ ≡ rm i
\end{code}

The client is positioned on the `-` side of the channel.

In this case execution is synchronous: we account for the fact that
the client might also interact on some other channels by passing `Δ`
to `F`.

\begin{code}
Client : (Set → Ty) → Set → Ty
Client F X Γ Δ = Σ (Code × Side × _) λ W → let A , s , I , O = W in
                 Σ ((> s , I , O , [ s ]¿ A) ∈ Γ) λ i →
                   F X (ud (> - , A) i) Δ
\end{code}

We are free to run clients as many times as we want (`Ctr`), or even
refrain from doing so (`Wk`).

\begin{code}
Wk Ctr : Ty
Wk Γ Δ = Σ (Code × Side × _) λ W →
         let A , s , I , O = W in
         Σ ((> s , I , O , [ s ]¿ A) ∈ Γ)
           (_≡_ Δ ∘ rm)
Ctr Γ Δ = Σ (Code × Side × _) λ W →
          let A , s , I , O = W in
          let τ = > s , I , O , [ s ]¿ A in
            τ ∈ Γ
          × Δ ≡ Γ ∷ τ
\end{code}

To add corecursion, we must first define what we consider a *guarded*
(hence, hopefully, *productive*) session.

\begin{code}
Guarded : ∀ {I O} → I ▹ O → Set₁
Guarded (`I i    ) = ⊥
Guarded (`Σ S T  ) = ⊤
Guarded (`Π S T  ) = ⊤
Guarded (`^ T    ) = ∀ s → Guarded (T s)
Guarded (%3 L ⊗ R) = Guarded L × Guarded R
Guarded (%3 L ⅋ R) = Guarded L × Guarded R
Guarded (¡ F     ) = ⊥
Guarded (¿ F     ) = ⊥
Guarded (`ν F _  ) = ∀ o → Guarded (F o)
\end{code}

To provide syntax to productive nested loops that run for a possibly
infinite amount of time, we use the following definition:

\begin{code}
CoRec : (Set → Ty) → Set → Ty
CoRec F X Γ Δ = Σ (Side × Σ _ λ I → Σ _ λ O → (O → De (I ⊎ O)) × O) λ W →
                let s , I , O , T , o = W in 
                Σ ((> s , %2 `ν T o) ∈ Γ) λ i →
                  ((o : O) →   Guarded (T o)
                             × F (X ⊎ O) (ud (> s , %2 T o) i) Δ)
                × Δ ≡ rm i
\end{code}

### Small, *collapsed* functors

\begin{code}
private [Ty] = Cx → Cx → Set
\end{code}

We might want to switch to *small* functors (compare `[Ty]` and `Ty`),
also avoiding us to require witnesses which are actually *forced* (see
Edwin Brady et al's "Inductive Families Need Not Store Their
Indices").

Here are a couple examples of how we plan to proceed.

\begin{code}
module Small where

  [New] : Ty
  [New] Γ (Δ ∷ ε , F) = Γ ≡ Δ
  [New] _ _           = ⊥

  open import AD.Ix ; open Ix Level.zero

  isI? : {Γ : Cx} → Ix Γ → 1+ (Σ Set id)
  isI? i with lookup i
  ... | %3 (`I j) = > (% j)
  ... | _         = ε

  [End] : Ty
  [End] Γ Δ = Σ (Σ Set λ I → Set × I × Side) λ W →
              let I , O , i , s = W in
              Σ (Ix Γ) λ i →
                case isI? i of 1+.maybe (λ _ → Δ ≡ Ix.− _ i) ⊥
\end{code}

While it seems possible to treat all the syntax in this way, we prefer
to use the large version for now as we think it leads to better type
errors when constructing programs.

We will investigate the possibility of using the large version as
syntax for the small one, by executing the translation at compile
time.

### Tags

We adopt a "tagful" syntax, where nodes of the syntax tree are made of
dependent pairs whose first component is of type `Tag`.

\begin{code}
module T where

  data Tag : Set where
    new fork       : Tag
    send recv      : Tag
    !! ?? wk ctr   : Tag
    corec          : Tag
    write read     : Tag
    at             : Tag
    end            : Tag

open T using (Tag)
\end{code}

### The tagged family of functors

The type of the second component is given by the following family,
which groups all the above functors.

\begin{code}
π : Tag → (Set → Ty) → Set → Ty
π T.new   T X Γ Δ = New          Γ Δ                 × X ≡ ⊤
π T.fork  T X Γ Δ = Fork   (T X) Γ Δ                 × X ≡ ⊤
π T.send  T X Γ Δ = Send         Γ Δ                 × X ≡ ⊤
π T.recv  T X Γ Δ = Receive      Γ Δ                 × X ≡ ⊤
π T.!!    T X Γ Δ = Server (T X) Γ Δ                 × X ≡ ⊤
π T.??    T X Γ Δ = Client  T X  Γ Δ
π T.wk    T X Γ Δ = Wk           Γ Δ                 × X ≡ ⊤
π T.ctr   T X Γ Δ = Ctr          Γ Δ                 × X ≡ ⊤
π T.corec T X Γ Δ = CoRec   T X  Γ Δ
π T.write T X Γ Δ = Write        Γ Δ                 × X ≡ ⊤
π T.read  T X Γ Δ = Σ (Read Γ Δ) λ p →                          
                    let ((_ , J , _) , _) , _ = p in   X ≡ J       
π T.at    T X Γ Δ = Σ (At Γ Δ) λ p →
                    let (_ , O , _) , _ = p in         X ≡ O
π T.end   T X Γ Δ = Σ (End  Γ Δ) λ p →                             
                    let (I , _ , _) , _ = p in         X ≡ I
\end{code}

### Process terms

As already stated, we plan to adopt codes for indexed functors instead
of defining those directly. We could then simply use a generic indexed
free monad construction, as in McBride's "Kleisli Arrows of Outrageous
Fortune", encoding our "Atkey-style" parameterisation in the way
described there.

To make things simpler we use the following definition for now: this
is neither a monad nor a monad transfomer, it is just convenient
temporary syntax.

\begin{code}
module Process where

  infix 2 _[_⊢_]>_

  F = λ T X Γ Δ → Σ T.Tag λ t → π t T X Γ Δ

  data _[_⊢_]>_ Γ (M : Set → Set) X : Cx → Set₁ where
    ⇑_    :             M X                                → Γ [ M ⊢ X ]> Γ
    [_]   : ∀ {Δ}     → F (λ Z A B → A [ M ⊢ Z ]> B) X Γ Δ → Γ [ M ⊢ X ]> Δ
    _»=_  : ∀ {Ξ Δ Y} → Γ [ M ⊢ Y ]> Ξ                     → 
                   (Y → Ξ [ M ⊢ X ]> Δ)                    → Γ [ M ⊢ X ]> Δ

open Process using (_[_⊢_]>_ ; ⇑_ ; _»=_ ; [_]) public
\end{code}

Note that referring to the above operators as "strictly positive
functors" as we did, while very reasonable from their definitions, is
also justified by the fact that Agda's positivity checker accepts
`_[_⊢_]>_`.

### Syntactic sugar

#### Patterns

To construct and pattern match on processes we make extensive use of
Agda's `pattern` facility.

\begin{code}
pattern fork    d x    = [ T.fork  , (d , x , <>)                 , <> ] 
pattern new            = [ T.new   , (_ , <>)                     , <> ] 
pattern send    i j    = [ T.send  , % (i , j , <>)               , <> ] 
pattern receive i      = [ T.recv  , % (i , <>)                   , <> ] 
pattern accept  i a p  = [ T.!!    , % (i , a , p , <>)           , <> ] 
pattern connect i   p  = [ T.??    , % (i , p)                         ] 
pattern wont    i      = [ T.wk    , % (i , <>)                   , <> ] 
pattern twice   i      = [ T.ctr   , % (i , <>)                   , <> ] 
pattern write   i x    = [ T.write , ((_ , x , _) , i , <>)       , <> ] 
pattern read    i      = [ T.read  , % (i , <>)                   , <> ] 
pattern end/    i r    = [ T.end   , ((_ , _ , r , _) , (i , <>)) , <> ] 
pattern end     i      = end/ i _
pattern at/     i o    = [ T.at    , ((%3 (o , _) , (i , <>)))    , <> ] 
pattern at      i      = at/ i _                                         
pattern corec   i o gp = [ T.corec , (%4 o) , (i , (gp , <>))          ]
\end{code}

(We plan to also define a view for these patterns, so that Agda's
interactive splitting (`C-c C-c`) can be recovered after a `with`)

#### Monadic binding notation

For the binding operator we mimic Haskell's `do`-notation with a
`syntax` declaration.

\begin{code}
infixr 5 bind
bind : ∀ {M Γ Ξ Δ X Y} → Γ [ M ⊢ Y ]> Ξ  → 
                    (Y → Ξ [ M ⊢ X ]> Δ) → Γ [ M ⊢ X ]> Δ
bind = _»=_
syntax bind m (λ x → y) = x <- m ⋯ y
\end{code}

\begin{code}
infixr 5 _»_
_»_ : ∀ {M Γ Ξ Δ X Y} → Γ [ M ⊢ X ]> Ξ → Ξ [ M ⊢ Y ]> Δ → Γ [ M ⊢ Y ]> Δ
m » n = m »= λ _ → n
\end{code}

#### `write` and `read` dependently

We added `` `^ `` (in Strictly Positive Families we would have used ``
`Δ ``) to recover the *possibility* of making use of data exchanged by
`write` and `read` at the type level.

\begin{code}
put : ∀ {M Γ}{I O A : Set}{T : A → De I}{s} →
      (i : (> s , I , O , [ s ]Σ A (`^ T)) ∈ Γ) →
      (a : A) → Γ [ M ⊢ A ]> (ud (> s , %2 T a) (∈ud i))
put i a = write i a »= λ _ → at (∈ud i)

get : ∀ {M Γ Δ}{I O A B : Set}{T : A → De I}{s}
      (i : (> s , I , O , [ s ]Π A (`^ T)) ∈ Γ) →
      (f : ∀ a → ud (> s , %2 T a) (∈ud i) [ M ⊢ B ]> Δ) →
      Γ [ M ⊢ B ]> Δ
get i f = read i »= λ a → at (∈ud i) » f a
\end{code}

#### `new` channel for ⊤-indexed sessions

We often create channels for stateful sessions where both index sets
are `⊤`: using `new⊤` helps inference.

\begin{code}
new⊤ : ∀ {Γ M F} → Γ [ M ⊢ ⊤ ]> Γ ∷ (ε , ⊤ , ⊤ , F)
new⊤ = new
\end{code}

## Haskell evaluator

To make an efficient use of Haskell channels, while forgetting the
data required to compute their "changing" types, we resort to making a
*sensible* use of **unsafe** casts. What follows should therefore be
considered as an extension to the *trusted base*.

We provide **no correctness proof** for this evaluator.

\begin{code}
private

  postulate
    unsafeCoerce : ∀ {l1}{A : Set l1}{l2}{B : Set l2} → A → B

  {-# IMPORT   Unsafe.Coerce                                          #-}
  {-# COMPILED unsafeCoerce (\ _ _ _ _ -> Unsafe.Coerce.unsafeCoerce) #-}
\end{code}

\begin{code}
open import IO.Primitive using (IO ; return ; _>>=_ ; putStr ; putStrLn)
module IO = IO.Primitive
\end{code}

\begin{code}
infix 2 _[IO_]>_
_[IO_]>_ = λ Γ X Δ → Γ [ IO ⊢ X ]> Δ

IOProc = λ X → [] [IO X ]> []

open import Control.Concurrent
module C  = Control.Concurrent
open import Control.Concurrent.Chan.Synchronous
module CS = Control.Concurrent.Chan.Synchronous
\end{code}

We need our channels to be untyped, to obtain which we postulate an
abstract type and use unsafe coercions to and from it.

This is similar to Pucella and Tov's embedding in ["Haskell Session
Types with (Almost) No
Class"](http://www.eecs.harvard.edu/~tov/pubs/haskell-session-types/).

\begin{code}
postulate Abs : Set

UChan = Chan Abs
\end{code}

The channels for a context.

\begin{code}
⟦_⟧Cx : Cx → Set₁
⟦_⟧Cx = All λ _ → UChan
\end{code}

\begin{code}
lookupUChan : ∀ {Γ C} → (i : C ∈ Γ) → ⟦ Γ ⟧Cx → UChan
lookupUChan i cs = snd (lookupAll i cs)
\end{code}

We need some Haskell helpers.

Note that our channels are ultimately implemented on top of Jesse
Tov's `synchronous-channels` package: for this reason, currently all
the interactions are synchronous (blocking).

\begin{code}
infixl 1 _>>_

_>>_ : ∀ {lA lB}{A : Set lA}{B : Set lB} → IO A → IO B → IO B
m >> n = m >>= λ _ → n

mapIO : ∀ {lA lB}{A : Set lA}{B : Set lB} → (A → B) → IO A → IO B
mapIO f xs = xs >>= return ∘ f
\end{code}

Every communication with the untyped channels uses `unsafeCoerce`.

\begin{code}
writeUChan : {A : Set} → UChan → A → IO C.<>
writeUChan c = writeChan c ∘ unsafeCoerce

readUChan : {A : Set} → UChan → IO A
readUChan {A = A} c = readChan c >>= return ∘ unsafeCoerce
\end{code}

Here is the actual test evaluator, to implement which we disable
termination checking: we already use "unsafe" features so we do not
bother defining a *coinductive* wrapper as in the `IO` module of
Agda's standard library.

\begin{code}
{-# NO_TERMINATION_CHECK #-}
run : {Γ Δ : Cx}{X : Set} → Γ [IO X ]> Δ → ⟦ Γ ⟧Cx → IO (X × ⟦ Δ ⟧Cx)
\end{code}

We map the embedded monadic actions to themselves, and the binding
syntax to the binding operator for the `IO` monad.

\begin{code}
run (⇑ m           ) cs = mapIO (flip _,_ cs) m                                           
                                                                                          
run (m »= f        ) cs = run m cs >>= λ { (x , cs) → run (f x) cs }                      
\end{code}                                                                                

`new` just creates a new channel.

\begin{code}                                                                              
run (new           ) cs = newChan >>= λ c → return (_ , (cs ,̇ c))
\end{code}

`forks x` interprets the `Splits` in `s` obtaining two lists of
channels `ls` and `rs`: it keeps `ls` for the parent thread and leaves
access to `rs` to the child (`x`).
                                                                                          
\begin{code}
run (fork       s x) cs = let ls , rs = all-splits cs s in
                          forkIO (run x rs >> return ⟨⟩) >>                               
                          return (tt , ls)                                                
\end{code}                                                                                

`send i j` writes channel `i` on channel `j` and frees the
continuation from the burden of communicating along `i`.

We could avoid many uses of `unsafeCoerce` in the following but we
think it is more efficient to avoid calling functions like
`all-ud` as in the commented-out code: they perform no operations
on the actual lists of *untyped* channels.

The usages of `unsafeCoerce` which are more difficult justify are
those inside every call to `readUChan` and `writeUChan`.

\begin{code}                                                                              
run (send       i j) cs = let chanToSend    = lookupUChan        i  cs in                 
                          let chanToWriteOn = lookupUChan (wk/ i j) cs in                 
                          writeUChan chanToWriteOn chanToSend >>
                          return (tt , unsafeCoerce (all-rm i cs))
                       -- return (tt , all-ud j (all-rm i cs) chanToWriteOn)
\end{code}

`receive` receives a channel from channel `i` and allows/forces the
continuation to also take care of it.
                                                                                          
\begin{code}
run (receive      i) cs = let chanToReadFrom = lookupUChan i cs in                        
                          readUChan chanToReadFrom >>= λ receivedChan →                   
                          return (tt , (unsafeCoerce cs ,̇ receivedChan))                  
\end{code}

`accept i a p` forks a process that waits for channels: whenever one
is received it spawns a new copy of the server along it.

\begin{code}                                                                              
run (accept   i a p) cs = forkIO server >> return (tt , all-rm i cs)                   
  where c = lookupUChan i cs                                            
        service : UChan → IO _                                          
        service n = run p (all-ud i cs n) >> return ⟨⟩
        server : IO C.<>                                                
        server = readUChan c        >>= λ n →                           
                 forkIO (service n) >>                                  
                 server                                                 
\end{code}

`connect i p` creates a channel and sends it along the channel `i`,
which is (or should be) shared by construction with a server, then it
becomes process `p`.
                                                                                          
\begin{code}
run (connect    i p) cs = newChan                         >>= λ n →                       
                          writeUChan (lookupUChan i cs) n >>                              
                          run p (all-ud i cs n)
\end{code}

`wont i` avoids starting the client/server interaction with the server
which waits for channels on `i`.
                                                                                          
\begin{code}
run (wont         i) cs = return (tt , all-rm i cs)
\end{code}

`twice i` duplicates the server which waits for channels on `i`.
                                                                                          
\begin{code}
run (twice        i) cs = return (tt , (cs ,̇ lookupUChan i cs))                           
\end{code}

`write i x` writes `x` on channel `i`.
                                                                                          
\begin{code}                                                                              
run (write      i x) cs = let c = lookupUChan i cs in                                     
                          writeUChan c x >>                                               
                          return (tt , unsafeCoerce cs)                                   
\end{code}

`read i` reads from `i` and returns what it read.
                                                                                          
\begin{code}
run (read         i) cs = let c = lookupUChan i cs in                                     
                          readUChan c >>= λ x →
                          return (x , unsafeCoerce cs)                                    
\end{code}

`end i` terminates the (sub)session
                                                                                          
\begin{code}                                                                              
run (end/       i r) cs = return (r , all-rm i cs)                                     
\end{code}

`at/ i o` simply returns `o`.

\begin{code}
run (at/        i o) cs = return (o , unsafeCoerce cs)                                    
\end{code}

`corec` enters a loop whose body is contained in `gp`: the coiteration
will possibly be exited whenever the value the process returns is `inl
x` for some `x`.

\begin{code}
run (corec   i o gp) cs = aux o
  where aux = λ o → run (snd (gp o)) (unsafeCoerce cs) >>=
                    uc ⊎.[ cu return , (λ o _ → aux o) ]
\end{code}

Closed processes describe IO computations.

\begin{code}
run[] : ∀ {X} →  IOProc X → IO X
run[] P = mapIO fst (run P [])
\end{code}

Note that as the evaluator allows for processes that embed any `IO`
action one could easily add unwanted behaviours: the user is still
free to capture a fragment of `IO` to be considered *safe* and simply
compose this evaluator after a translation phase to `IO`.

For simplicity, the currently provided
[examples](Session.Examples.html) just use `IO` for basic operations
like suspending processes for finite amounts of time or accessing the
standard output.

## Conclusion and further work

## Acknowledgments

I must thank

- Claudio Sacerdoti Coen, who provided many useful comments on a
  previous version of this implementation;

- Peter Morris, who originally taught me the above technique to
  attempt to make families small by computation.

