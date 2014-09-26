\begin{code}
module Session where

open import Session.Base public
\end{code}

\begin{code}
mutual 

  De    = λ I → I ▹ ⊤
  Code  = Σ _ λ I → Σ _ λ O → I ▹ O
  Entry = 1+ Side × Code

  data _▹_ (I O : Set) : Set₁ where
    `I      :                     (i : I) → I ▹ O
    `Σ `Π   : (S : Set)(T : I ▹ S)        → I ▹ O
    `^      : (T : O → De I)              → I ▹ O
    _⊗_ _⅋_ : (L : Entry)(R : I ▹ O)      → I ▹ O
    ¡_ ¿_   : Code                        → I ▹ O
    `ν      : (F : O → De (I ⊎ O))(o : O) → I ▹ O

`Σ^ `Π^ : {I O : Set}(S : Set)(T : S → De I) → I ▹ O
`Σ^ S T = `Σ S (`^ T)
`Π^ S T = `Π S (`^ T)
\end{code}

\begin{code}
_◂_ : Set → Set → Set₁
O ◂ I = I ▹ O
\end{code}

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

\begin{code}
Cx = List Entry
\end{code}

\begin{code}
is¿ : Entry → Set
is¿ (> + , (_ , _ , ¿ F)) = ⊤
is¿ (> - , (_ , _ , ¡ F)) = ⊤
is¿  _                    = ⊥
\end{code}

\begin{code}
All¿ : Cx → Set _
All¿ = All is¿
\end{code}

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

\begin{code}
Splits : ∀ Γ → Set _
Splits = All Split

splits : ∀ {Γ} → Splits Γ → Cx × Cx
splits []       = [] , []
splits (ds ,̇ s) = split _ s (splits ds)
\end{code}

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

\begin{code}
pattern %_  x = _ , x
pattern %2_ x = % %  x
pattern %3_ x = % %2 x
pattern %4_ x = % %3 x

pattern »»_ x = > + , %2 x
pattern _«« x = > - , %2 x
\end{code}

\begin{code}
private Ty = Cx → Cx → Set₁
\end{code}

\begin{code}
New : Ty
New Γ Δ = Σ _ λ F → Δ ≡ Γ ∷ ε , F
\end{code}

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

\begin{code}
At : Ty
At Γ Δ = Σ (Σ _ λ I → Σ _ λ O → Σ (O → I ▹ ⊤) λ _ → O × Side) λ W →
         let I , O , T , o , s = W in
         Σ ((> s , %2 `^ T) ∈ Γ)
            (_≡_ Δ ∘ ud (> s , %2 T o))
\end{code}

\begin{code}
End : Ty
End Γ Δ = Σ (Σ Set λ I → Set × I × Side) λ W →
          let I , O , i , s = W in
          Σ ((> s , (I , O , `I i)) ∈ Γ)
            (_≡_ Δ ∘ rm)
\end{code}

\begin{code}
Fork : Ty → Ty
Fork F Γ Δ = Σ (Splits Γ) λ ds →
             let ΓL , ΓR = splits ds in
               F ΓR []
             × Δ ≡ ΓL
\end{code}

\begin{code}
Server : Ty → Ty
Server F Γ Δ = Σ (Code × Side × _) λ W → let A , s , I , O = W in
               Σ ((> s , I , O , [ s ]¡ A) ∈ Γ) λ i →
                 All¿ Δ
               × F (ud (> + , A) i) Δ
               × Δ ≡ rm i
\end{code}

\begin{code}
Client : (Set → Ty) → Set → Ty
Client F X Γ Δ = Σ (Code × Side × _) λ W → let A , s , I , O = W in
                 Σ ((> s , I , O , [ s ]¿ A) ∈ Γ) λ i →
                   F X (ud (> - , A) i) Δ
\end{code}

\begin{code}
Guarded : ∀ {I O} → I ▹ O → Set₁
Guarded (`I i    ) = ⊥
Guarded (`Σ S T  ) = ⊤
Guarded (`Π S T  ) = ⊤
Guarded (`^ T    ) = ∀ s → Guarded (T s)
Guarded (%3 L ⊗ R) = Guarded R
Guarded (%3 L ⅋ R) = Guarded R
Guarded (¡ F     ) = ⊥
Guarded (¿ F     ) = ⊥
Guarded (`ν F _  ) = ∀ o → Guarded (F o)
\end{code}

\begin{code}
CoRec : (Set → Ty) → Set → Ty
CoRec F X Γ Δ = Σ (Side × Σ _ λ I → Σ _ λ O → (O → (I ⊎ O) ▹ ⊤) × O) λ W →
                let s , I , O , T , o = W in 
                Σ ((> s , %2 `ν T o) ∈ Γ) λ i →
                  ((o : O) →   Guarded (T o)
                             × F (X ⊎ O) (ud (> s , %2 T o) i) Δ)
                × Δ ≡ rm i
\end{code}

\begin{code}
module T where

  data Tag : Set where
    new fork       : Tag
    send recv      : Tag
    !! ?? wk ctr   : Tag
    write read     : Tag
    end            : Tag
    corec          : Tag
    at             : Tag

open T using (Tag)
\end{code}

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
π T.write T X Γ Δ = Write        Γ Δ                 × X ≡ ⊤
π T.corec T X Γ Δ = CoRec   T X  Γ Δ
π T.read  T X Γ Δ = Σ (Read Γ Δ) λ p →                          
                    let ((_ , J , _) , _) , _ = p in   X ≡ J       
π T.end   T X Γ Δ = Σ (End  Γ Δ) λ p →                             
                    let (I , _ , _) , _ = p in         X ≡ I
π T.at    T X Γ Δ = Σ (At Γ Δ) λ p →
                    let (_ , O , _) , _ = p in         X ≡ O
\end{code}

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

\begin{code}
new⊤ : ∀ {Γ M F} → Γ [ M ⊢ ⊤ ]> Γ ∷ (ε , ⊤ , ⊤ , F)
new⊤ = new
\end{code}

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

open import Control.Concurrent as C
open import Control.Concurrent.Chan.Synchronous
\end{code}

\begin{code}
postulate Abs : Set

UChan = Chan Abs
\end{code}

\begin{code}
⟦_⟧Cx : Cx → Set₁
⟦_⟧Cx = All λ _ → UChan
\end{code}

\begin{code}
lookupUChan : ∀ {Γ C} → (i : C ∈ Γ) → ⟦ Γ ⟧Cx → UChan
lookupUChan i cs = snd (lookupAll i cs)
\end{code}

\begin{code}
infixl 1 _>>_

_>>_ : ∀ {lA lB}{A : Set lA}{B : Set lB} → IO A → IO B → IO B
m >> n = m >>= λ _ → n

mapIO : ∀ {lA lB}{A : Set lA}{B : Set lB} → (A → B) → IO A → IO B
mapIO f xs = xs >>= return ∘ f
\end{code}

\begin{code}
writeUChan : {A : Set} → UChan → A → IO C.<>
writeUChan c = writeChan c ∘ unsafeCoerce

readUChan : {A : Set} → UChan → IO A
readUChan {A = A} c = readChan c >>= return ∘ unsafeCoerce
\end{code}

\begin{code}
{-# NO_TERMINATION_CHECK #-}
run : {Γ Δ : Cx}{X : Set} → Γ [IO X ]> Δ → ⟦ Γ ⟧Cx → IO (X × ⟦ Δ ⟧Cx)
\end{code}

\begin{code}
run (⇑ m           ) cs = mapIO (flip _,_ cs) m                                           
                                                                                          
run (m »= f        ) cs = run m cs >>= λ { (x , cs) → run (f x) cs }                      
\end{code}                                                                                
                                                                                          
\begin{code}                                                                              
run (new           ) cs = newChan >>= λ c → return (_ , (cs ,̇ c))                         
                                                                                          
run (fork       d x) cs = let ls , rs = all-splits cs d in                                
                          forkIO (run x rs >> return ⟨⟩) >>                               
                          return (tt , ls)                                                
\end{code}                                                                                
                                                                                          
\begin{code}                                                                              
run (send       i j) cs = let chanToSend    = lookupUChan        i  cs in                 
                          let chanToWriteOn = lookupUChan (wk/ i j) cs in                 
                          writeUChan chanToWriteOn chanToSend >>
                          return (tt , unsafeCoerce (all-rm i cs))
                          -- return (tt , all-ud j (all-rm i cs)                     
                          --                       chanToWriteOn)                       
                                                                                          
run (receive      i) cs = let chanToReadFrom = lookupUChan i cs in                        
                          readUChan chanToReadFrom >>= λ receivedChan →                   
                          return (tt , (unsafeCoerce cs ,̇ receivedChan))                  
\end{code}                                                                                
                                                                                          
\begin{code}                                                                              
run (accept i   a p) cs = forkIO server >> return (tt , all-rm i cs)                   
  where c = lookupUChan i cs                                            
        service : UChan → IO _                                          
        service n = run p (all-ud i cs n) >> return ⟨⟩
        server : IO C.<>                                                
        server = readUChan c        >>= λ n →                           
                 forkIO (service n) >>                                  
                 server                                                 
                                                                                          
run (connect    i p) cs = newChan                         >>= λ n →                       
                          writeUChan (lookupUChan i cs) n >>                              
                          run p (all-ud i cs n)
                                                                                          
run (wont         i) cs = return (tt , all-rm i cs)                                    
                                                                                          
run (twice        i) cs = return (tt , (cs ,̇ lookupUChan i cs))                           
\end{code}                                                                                
                                                                                          
\begin{code}                                                                              
run (write      i x) cs = let c = lookupUChan i cs in                                     
                          writeUChan c x >>                                               
                          return (tt , unsafeCoerce cs)                                   
                                                                                          
run (read         i) cs = let c = lookupUChan i cs in                                     
                          readUChan c >>= λ x →
                          return (x , unsafeCoerce cs)                                    
\end{code}                                                                                
                                                                                          
\begin{code}                                                                              
run (end/       i r) cs = return (r , all-rm i cs)                                     
                                                                                          
run (at/        i o) cs = return (o , unsafeCoerce cs)                                    
\end{code}

\begin{code}
run (corec   i o gp) cs = aux o
  where aux = λ o → run (snd (gp o)) (unsafeCoerce cs) >>=
                    uc ⊎.[ cu return , (λ o _ → aux o) ]
\end{code}

\begin{code}
run[] : ∀ {X} →  IOProc X → IO X
run[] P = mapIO fst (run P [])
\end{code}
