module IntrinsicDependentTypes where

open import Level
open import Function using (id)
open import Data.Unit
open import Data.Product using (_×_; Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; resp₂; cong-app; icong; module ≡-Reasoning)
open import Axiom.Extensionality.Propositional using (∀-extensionality; Extensionality)

variable l l′ l₁ l₂ : Level

-- postulate
--   fun-ext : ∀{l₁ l₂} → Extensionality l₁ l₂
-- 
-- dep-ext : ∀ {l₁ l₂}{A : Set l₁}{F G : (α : A) → Set l₂}
--     → (∀ (α : A) → F α ≡ G α)
--     → ((α : A) → F α) ≡ ((α : A) → G α) 
-- dep-ext = ∀-extensionality fun-ext _ _

-- flag if value is actually just a neutral
data Neu : Set where
  neu : Neu -- neutral (i.e. blocking application)
  val : Neu -- actual value

variable μ μ′ μ₁ μ₂ : Neu

-- flag if something is value
data Val : Set where
  val : Neu → Val -- values can possibly be neutral
  red : Val       -- or reducable 
  
variable ν ν′ ν₁ ν₂ : Val

-- least upper bound of values
_⊔ᵥ_ : Val → Val → Val 
val _ ⊔ᵥ val _ = val val 
_ ⊔ᵥ red = red
red ⊔ᵥ _ = red

-- special case for neutral reduction of applications
_⊔ₙ_ : Val → Val → Val 
val neu ⊔ₙ val _ = val neu -- is a neutral if left side of application is neu and right side is val
val val ⊔ₙ val _ = red     -- reducable otherwise
_ ⊔ₙ red = red
red ⊔ₙ _ = red

-- type environment
data Env : Set
variable Γ Γ′ Γ₁ Γ₂ : Env

-- renamings map variables to variables
data Ren : Env → Env → Set
variable ρ ρ′ ρ₁ ρ₂ : Ren Γ₁ Γ₂

-- substitution map variables to types 
data Sub : Env → Env → Set
variable σ σ′ σ₁ σ₂ : Sub Γ₁ Γ₂

-- expressions in type position index by their level and value status
data Type Γ : Level → Val → Set 
variable T T′ T₁ ⊤₂ : Type Γ l ν
variable τ τ′ τ₁ τ₂ : Type Γ l (val μ)

-- type environment memebership
data _∋_ : (Γ : Env) → Type Γ l ν → Set 
variable x x′ x₁ x₂ : Γ ∋ T

-- expressions are indexed by a type environment, their type and value status
data Expr Γ : Type Γ l ν → Val → Set 
variable e e′ e₁ e₂ : Expr Γ T ν
variable v v′ v₁ v₂ : Expr Γ T (val μ)
variable n n′ n₁ n₂ : Expr Γ T (val neu) 

-- renaming and substitution of types, variables and expressions
renₜ : Ren Γ₁ Γ₂ → Type Γ₁ l ν → Type Γ₂ l ν 
renₓ : (ρ : Ren Γ₁ Γ₂) → Γ₁ ∋ T → Γ₂ ∋ (renₜ ρ T)
renₑ : (ρ : Ren Γ₁ Γ₂) → Expr Γ₁ T ν → Expr Γ₂ (renₜ ρ T) ν 

subₜ : Sub Γ₁ Γ₂ → Type Γ₁ l ν → Type Γ₂ l red
subₓ : (σ : Sub Γ₁ Γ₂) → Γ₁ ∋ T → Expr Γ₂ (subₜ σ T) red
subₑ : (σ : Sub Γ₁ Γ₂) → Expr Γ₁ T ν → Expr Γ₂ (subₜ σ T) red

-- big step reduction of types
data _⇓ₜ_ : Type Γ l ν → Type Γ l (val μ) → Set
variable ⇓T ⇓T′ ⇓T₁ ⇓T₂ : T ⇓ₜ τ  

-- big reduction on expressions along a possible type reduction
data _⇓ₑ[_]_ : Expr Γ T ν → T ⇓ₜ τ → Expr Γ τ (val μ) → Set

data Env where
  ∅      : Env                          
  _▶_    : (Γ : Env) → Type Γ l ν → Env

-- special cases for renamings and substitutions that need _▶_ constructor to be definable
wkₜ : Type Γ l ν → Type (Γ ▶ T) l ν
wkₑ : Expr Γ T ν → Expr (Γ ▶ T) (wkₜ T) ν
_[_]ₜ : Type (Γ ▶ T) l ν → Expr Γ T ν′ → Type Γ l red
_[_]ₑ : Expr (Γ ▶ T) T′ ν → (e : Expr Γ T ν′) → Expr Γ (T′ [ e ]ₜ) red

-- renamings and substitions
data Ren where 
  idᵣ   : Ren Γ Γ
  liftᵣ : (ρ : Ren Γ₁ Γ₂) → Ren (Γ₁ ▶ T) (Γ₂ ▶ renₜ ρ T)
  wkᵣ   : (ρ : Ren Γ₁ Γ₂) → Ren Γ₁ (Γ₂ ▶ T)
  dropᵣ : Ren (Γ₁ ▶ T) Γ₂ → Ren Γ₁ Γ₂

data Sub where 
  idₛ   : Sub Γ Γ
  liftₛ : (σ : Sub Γ₁ Γ₂) → Sub (Γ₁ ▶ T) (Γ₂ ▶ subₜ σ T)
  wkₛ   : Sub Γ₁ Γ₂ → Sub Γ₁ (Γ₂ ▶ T)
  dropₛ : Sub (Γ₁ ▶ T) Γ₂ → Sub Γ₁ Γ₂
  extₛ  : Sub Γ₁ Γ₂ → Expr Γ₁ T ν → Sub (Γ₁ ▶ T) Γ₂

-- composition of renamings and substitions

-- types, variables and expressions
data Type Γ where
  *_     : (l : Level) → Type Γ (suc l) (val val) 
  `⊤     : Type Γ zero (val val)
  ∀x∶_,_ : (T : Type Γ l ν) → Type (Γ ▶ T) l′ ν′ → Type Γ (l ⊔ l′) (ν ⊔ᵥ ν′) 
  _≣_    : {T : Type Γ l ν} → Expr Γ T ν₁ → Expr Γ T ν₂ → Type Γ l (ν₁ ⊔ᵥ ν₂)  
  ↓_     : Expr Γ (* l) ν → Type Γ l ν
  _ᵣ     : Type Γ l ν → Type Γ l red

data _∋_ where
  here  : (Γ ▶ T) ∋ wkₜ T 
  there : Γ ∋ T → (Γ ▶ T′) ∋ wkₜ T

data Expr Γ where
  `_    : Γ ∋ T → Expr Γ T (val neu)
  tt    : Expr Γ `⊤ (val val)
  λ→_   : Expr (Γ ▶ T) T′ ν → Expr Γ (∀x∶ T , T′) (val val)
  _·_   : Expr Γ (∀x∶ T , T′) ν₁ → (e₂ : Expr Γ T ν₂) → Expr Γ (T′ [ e₂ ]ₜ) (ν₁ ⊔ₙ ν₂)
  rfl_  : (e : Expr Γ T ν) → Expr Γ (e ≣ e) ν
  _⇝[_] : Expr Γ T ν → T ⇓ₜ τ → Expr Γ τ ν
  ↑_    : (T : Type Γ l ν) → Expr Γ (* l) ν 
  _ᵣ    : Expr Γ T ν → Expr Γ T red

-- big step semantics

postulate
  lemma : Type (Γ ▶ T) l ν → T ⇓ₜ τ → Type (Γ ▶ τ) l ν

data _⇓ₜ_ where
  ⇓id : τ ⇓ₜ τ 
  ⇓ᵣ  : T ⇓ₜ τ → (T ᵣ) ⇓ₜ τ
  ⇓∀  : (⇓T : T ⇓ₜ τ) → T′ ⇓ₜ τ′ → 
        (∀x∶ T , T′) ⇓ₜ (∀x∶ τ , lemma τ′ ⇓T) -- reduction of type in context preserves typing
  ⇓≣  : e₁ ⇓ₑ[ ⇓T ] v₁ → e₂ ⇓ₑ[ ⇓T ] v₂ → 
        (e₁ ≣ e₂) ⇓ₜ (v₁ ≣ v₂)
  ⇓↓  : e ⇓ₑ[ ⇓id ] (↑ τ) → (↓ e) ⇓ₜ τ

data _⇓ₑ[_]_ where 
  ⇓id  : v ⇓ₑ[ ⇓id ] v
  ⇓ᵣ   : e ⇓ₑ[ ⇓T ] v → (e ᵣ) ⇓ₑ[ ⇓T ] v
  -- ⇓λ   : e ⇓ₑ[ ⇓T ] v → 
  --       (λ→ e) ⇓ₑ[ ⇓∀ ⇓id ⇓T ] (λ→ v)
  ⇓·₁  : e₁ ⇓ₑ[ ⇓∀ ⇓T ⇓T′ ] (λ→ v₁) → (⇓e : e₂ ⇓ₑ[ ⇓id ] v₂) → ((v₁ [ v₂ ]ₑ) ⇓ₑ[ ⇓T₂ ] v) →
        (e₁ · e₂) ⇓ₑ[ {! ⇓e ⇓T ⇓T′!} ] v      -- substitution preserves type level big step semantics 
  -- ⇓·₂  : e₁ ⇓ₑ[ ⇓∀ ⇓T ⇓T′ ] n → (⇓e : e₂ ⇓ₑ[ ⇓id ] v₂) →  
  --         (e₁ · e₂) ⇓ₑ[ {! ⇓e ⇓T ⇓T′!} ] (n · v₂) -- substitution preserves type level big step semantics
  ⇓rfl : (⇓e :  e ⇓ₑ[ ⇓T ] v) → 
          (rfl e) ⇓ₑ[ ⇓≣ ⇓e ⇓e ] (rfl v)
  ⇓⇝   : (⇓e :  e ⇓ₑ[ ⇓T ] v) → (e ⇝[ ⇓T ]) ⇓ₑ[ ⇓id ] v
  ⇓↑   : (⇓ₜ : T ⇓ₜ τ) → 
          (↑ T) ⇓ₑ[ ⇓id ] (↑ τ)   

-- renaming

-- lemmas on renaming
idᵣT≡T : renₜ idᵣ T ≡ T
idₑx≡x : renₓ idᵣ x ≡ subst (_ ∋_) (sym (idᵣT≡T)) x
idₑe≡e : {T : Type Γ l ν′} {e : Expr Γ T ν} → 
         renₑ idᵣ e ≡ subst (λ T → Expr _ T _) (sym (idᵣT≡T)) e

renₜ ρ (* l) = * l
renₜ ρ `⊤ = `⊤
renₜ ρ (∀x∶ T , T′) = ∀x∶ renₜ ρ T , renₜ (liftᵣ ρ) T′
renₜ ρ (e₁ ≣ e₂) = renₑ ρ e₁ ≣ renₑ ρ e₂
renₜ ρ (↓ e) = ↓ renₑ ρ e
renₜ ρ (T ᵣ) = (renₜ ρ T) ᵣ

wkₜ T = renₜ (wkᵣ idᵣ) T

idᵣT≡T {T = * l} = refl
idᵣT≡T {T = `⊤} = refl
idᵣT≡T {T = ∀x∶ T , T′} = {!   !}
idᵣT≡T {T = e₁ ≣ e₂} = {! cong₂ _≣_ ? ?  !}
idᵣT≡T {T = ↓ e} = {!   !}
idᵣT≡T {T = T ᵣ} = {!   !}

renₓ idᵣ x = {!  x  !}
renₓ (liftᵣ ρ) here = {! here  !}
renₓ (liftᵣ ρ) (there x) = {! there (renₓ ρ x)  !}
renₓ (wkᵣ ρ) x = {! there (renₓ ρ x)  !}
renₓ (dropᵣ ρ) x = {! renₓ ρ (there x) !}

idₑx≡x {x = x} = {! x  !}

renₑ ρ (` x) = ` renₓ ρ x
renₑ ρ tt = tt
renₑ ρ (λ→ e) = λ→ renₑ (liftᵣ ρ) e
renₑ ρ (e₁ · e₂) = {! renₑ ρ e₁ · renₑ ρ e₂   !} -- interaction rena and sub
renₑ ρ (rfl e) = rfl (renₑ ρ e)
renₑ ρ (e ⇝[ ⇓T ]) = renₑ ρ e ⇝[ {! ⇓T  !} ] -- big step preserves ren
renₑ ρ (↑ T) = ↑ renₜ ρ T
renₑ ρ (e ᵣ) = renₑ ρ e ᵣ

wkₑ e = renₑ (wkᵣ idᵣ) e

idₑe≡e {e = e} = {! e  !}

subₜ σ (* l) = (* l) ᵣ
subₜ σ `⊤ = `⊤ ᵣ 
subₜ σ (∀x∶ T , T′) = (∀x∶ subₜ σ T , subₜ (liftₛ σ) T′)
subₜ σ (e₁ ≣ e₂) = (subₑ σ e₁ ≣ subₑ σ e₂)
subₜ σ (↓ e) = (↓ (subₑ σ e ⇝[ ⇓ᵣ ⇓id ]))
subₜ σ (T ᵣ) = subₜ σ T

T [ e ]ₜ = subₜ (extₛ idₛ e) T

subₓ idₛ x = {! x  !}
subₓ (liftₛ σ) here = {! here  !}
subₓ (liftₛ σ) (there x) = {! sub (renₓ )  !}
subₓ (wkₛ σ) x = {! wkₑ (subₓ σ x)  !}
subₓ (dropₛ σ) x = {!   !}
subₓ (extₛ e σ) here = {!   !}
subₓ (extₛ e σ) (there x) = {!   !}

subₑ σ (` x) = subₓ σ x
subₑ σ tt = {! tt ᵣ  !} -- lemma sub σ `⊤ = `⊤
subₑ σ (λ→ e) = (λ→ (subₑ (liftₛ σ) e)) ᵣ
subₑ σ (e₁ · e₂) = {! subₑ σ e₁ · subₑ σ e₂  !} -- type sub lemma
subₑ σ (rfl e) = rfl subₑ σ e
subₑ σ (e ⇝[ ⇓t ]) = {! (subₑ σ e) ⇝[ ⇓t ]  !} -- sub preserves bigstep
subₑ σ (↑ T) = {!    !}
subₑ σ (e ᵣ) = subₑ σ e

e [ e′ ]ₑ = subₑ (extₛ idₛ e′) e

-- denotational semantics

-- semantic environment 
data Env* : Env → Setω
-- semantic interpretation of types
⟦_⟧ₜ : Type Γ l ν → Env* Γ → Set l
-- semantic environment lookup
lookup : (Γ* : Env* Γ) → Γ ∋ T → ⟦ T ⟧ₜ Γ*
-- semantic interpretation of expressions
⟦_⟧ₑ : Expr Γ T ν → (Γ* : Env* Γ) → ⟦ T ⟧ₜ Γ*

data Env* where 
  ∅  : Env* ∅
  _▷_ : (Γ* : Env* Γ) → ⟦ T ⟧ₜ Γ* → Env* (Γ ▶ T)  

variable Γ* Γ*′ Γ*₁ Γ*₂ : Env* Γ

⟦ * l ⟧ₜ Γ* = Set l
⟦ `⊤ ⟧ₜ Γ* = ⊤
⟦ ∀x∶ T , T′ ⟧ₜ Γ* = ∀ (x : ⟦ T ⟧ₜ Γ*) → ⟦ T′ ⟧ₜ (Γ* ▷ x)
⟦ e₁ ≣ e₂ ⟧ₜ Γ* = ⟦ e₁ ⟧ₑ Γ* ≡ ⟦ e₂ ⟧ₑ Γ*
⟦ ↓ e ⟧ₜ Γ* = ⟦ e ⟧ₑ Γ*
⟦ T ᵣ ⟧ₜ Γ* = ⟦ T ⟧ₜ Γ*

lookup (Γ* ▷ x) here = {!  x  !}               -- renaming preserves denotational semantics
lookup (Γ* ▷ _) (there x) = {!  lookup Γ* x !} -- renaming preserves denotational semantics

-- type conversions are substs on types in agda!
⇓ₜ→≡ : T ⇓ₜ τ → ⟦ T ⟧ₜ Γ* ≡ ⟦ τ ⟧ₜ Γ* 
⇓ₑ→≡ : e ⇓ₑ[ ⇓T ] v → subst id (⇓ₜ→≡ {Γ* = Γ*} ⇓T) (⟦ e ⟧ₑ Γ*) ≡ (⟦ v ⟧ₑ Γ*)

⇓ₜ→≡ ⇓T = {!   !}
⇓ₑ→≡ ⇓e = {!  !}

⟦ ` x ⟧ₑ Γ* = lookup Γ* x
⟦ tt ⟧ₑ Γ* = tt
⟦ λ→_ {T = T} e ⟧ₑ Γ* = λ (x : ⟦ T ⟧ₜ Γ*) → ⟦ e ⟧ₑ (Γ* ▷ x)
⟦ e₁ · e₂ ⟧ₑ Γ* = {! ⟦ e₁ ⟧ₑ Γ* (⟦ e₂ ⟧ₑ Γ*)  !} -- substitution preserves denotational semantics
⟦ rfl e ⟧ₑ Γ* = refl
⟦ e ⇝[ ⇓T ] ⟧ₑ Γ* = subst id (⇓ₜ→≡ ⇓T) (⟦ e ⟧ₑ Γ*)
⟦ ↑ T ⟧ₑ Γ* = ⟦ T ⟧ₜ Γ*   
⟦ e ᵣ ⟧ₑ Γ* = ⟦ e ⟧ₑ Γ*        