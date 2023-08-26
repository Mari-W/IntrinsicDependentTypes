module IntrinsicDependentTypes where

open import Level
open import Function using (id)
open import Data.Unit
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; resp₂; cong-app; icong; module ≡-Reasoning)
open import Axiom.Extensionality.Propositional using (∀-extensionality; Extensionality)

postulate
  fun-ext : ∀{a b} → Extensionality a b

dep-ext : ∀ {a b}{A : Set a}{F G : (α : A) → Set b}
    → (∀ (α : A) → F α ≡ G α)
    → ((α : A) → F α) ≡ ((α : A) → G α) 
dep-ext = ∀-extensionality fun-ext _ _

variable l l′ l₁ l₂ : Level

data Neu : Set where
  neu : Neu
  val : Neu

variable μ μ′ μ₁ μ₂ : Neu

data Val : Set where
  val : Neu → Val -- values can be neutral values
  red : Val
  
variable ν ν′ ν₁ ν₂ : Val

_⊔ᵥ_ : Val → Val → Val -- least upper bound
val _ ⊔ᵥ val _ = val val
_ ⊔ᵥ red = red
red ⊔ᵥ _ = red

_⊔ₙ_ : Val → Val → Val -- special case for neutral reduction of applications
val neu ⊔ₙ val _ = val neu
val val ⊔ₙ val _ = red
_ ⊔ₙ red = red
red ⊔ₙ _ = red

data Env : Set
variable Γ Γ′ Γ₁ Γ₂ : Env

data Type Γ : Level → Val → Set
variable T T′ T₁ ⊤₂ : Type Γ l ν
variable τ τ′ τ₁ τ₂ : Type Γ l (val μ)

data _⇓ₜ_ : Type Γ l ν → Type Γ l (val μ) → Set
variable ⇓t ⇓t′ ⇓t₁ ⇓t₂ : T ⇓ₜ τ  

data _∋_ : (Γ : Env) → Type Γ l ν → Set 
variable x x′ x₁ x₂ : Γ ∋ T

data Expr Γ : Type Γ l ν → Val → Set 
variable e e′ e₁ e₂ : Expr Γ T ν
variable v v′ v₁ v₂ : Expr Γ T (val μ)
variable n n′ n₁ n₂ : Expr Γ T (val neu) 

data _⇓ₑ[_]_ : Expr Γ T ν → T ⇓ₜ τ → Expr Γ τ (val μ) → Set

data Env where
  ∅      : Env
  _▶_    : (Γ : Env) → Type Γ l ν → Env

data Type Γ where
  *_     : (l : Level) → Type Γ (suc l) (val val) 
  `⊤     : Type Γ zero (val val)
  ∀x∶_,_ : (T : Type Γ l ν) → Type (Γ ▶ T) l′ ν′ → Type Γ (l ⊔ l′) (ν ⊔ᵥ ν′) 
  _≣_    : {T : Type Γ l ν} → Expr Γ T ν₁ → Expr Γ T ν₂ → Type Γ l (ν₁ ⊔ᵥ ν₂)  
  ↓_     : Expr Γ (* l) ν → Type Γ l ν -- only expressions that are types can be types!

postulate
  wkₜ   : Type Γ l ν → Type (Γ ▶ T) l ν
  wkₑ   : Expr Γ T ν → Expr (Γ ▶ T) (wkₜ T) ν
  _[_]ₜ : Type (Γ ▶ T) l ν → Expr Γ T ν′ → Type Γ l (ν ⊔ᵥ ν′) 
  _[_]ₑ : Expr (Γ ▶ T) T′ ν → (e : Expr Γ T ν′) → Expr Γ (T′ [ e ]ₜ) (ν ⊔ᵥ ν′)

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

postulate
  lemma : Type (Γ ▶ T) l ν → T ⇓ₜ τ → Type (Γ ▶ τ) l ν

data _⇓ₜ_ where
  ⇓id : τ ⇓ₜ τ 
  ⇓∀  : (⇓t : T ⇓ₜ τ) → T′ ⇓ₜ τ′ → 
        (∀x∶ T , T′) ⇓ₜ (∀x∶ τ , lemma τ′ ⇓t) -- reduction of type in context preserves typing
  ⇓≣  : e₁ ⇓ₑ[ ⇓t ] v₁ → e₂ ⇓ₑ[ ⇓t ] v₂ → 
        (e₁ ≣ e₂) ⇓ₜ (v₁ ≣ v₂)
  ⇓↓  : e ⇓ₑ[ ⇓id ] (↑ τ) → (↓ e) ⇓ₜ τ

data _⇓ₑ[_]_ where 
  ⇓id  : v ⇓ₑ[ ⇓id ] v
  ⇓λ   : e ⇓ₑ[ ⇓t ] v → 
        (λ→ e) ⇓ₑ[ ⇓∀ ⇓id ⇓t ] (λ→ v)
  ⇓·₁  : e₁ ⇓ₑ[ ⇓∀ ⇓t ⇓t′ ] (λ→ v₁) → (⇓e : e₂ ⇓ₑ[ ⇓id ] v₂) → 
        (e₁ · e₂) ⇓ₑ[ {! ⇓e ⇓t ⇓t′!} ] (v₁ [ v₂ ]ₑ)     -- substitution preserves type level big step semantics 
  ⇓·₂  : e₁ ⇓ₑ[ ⇓∀ ⇓t ⇓t′ ] n → (⇓e : e₂ ⇓ₑ[ ⇓id ] v₂) →  -- substitution preserves type level big step semantics 
          (e₁ · e₂) ⇓ₑ[ {! ⇓e ⇓t ⇓t′!} ] (n · v₂)
  ⇓rfl : (⇓e :  e ⇓ₑ[ ⇓t ] v) → 
          (rfl e) ⇓ₑ[ ⇓≣ ⇓e ⇓e ] (rfl v)
  ⇓⇝   : (⇓e :  e ⇓ₑ[ ⇓t ] v) → (e ⇝[ ⇓t ]) ⇓ₑ[ ⇓id ] v
  ⇓↑   : (⇓ₜ : T ⇓ₜ τ) → 
          (↑ T) ⇓ₑ[ ⇓id ] (↑ τ)   

data Env* : Env → Setω
⟦_⟧ₜ : Type Γ l ν → Env* Γ → Set l
lookup : (Γ* : Env* Γ) → Γ ∋ T → ⟦ T ⟧ₜ Γ*
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

lookup (Γ* ▷ x) here = {!  x  !}               -- renaming preserves denotational semantics
lookup (Γ* ▷ _) (there x) = {!  lookup Γ* x !} -- renaming preserves denotational semantics

⇓ₜ→≡ : T ⇓ₜ τ → ⟦ T ⟧ₜ Γ* ≡ ⟦ τ ⟧ₜ Γ* 
⇓ₑ→≡ : e ⇓ₑ[ ⇓t ] v → subst id (⇓ₜ→≡ {Γ* = Γ*} ⇓t) (⟦ e ⟧ₑ Γ*) ≡ (⟦ v ⟧ₑ Γ*)

⇓ₜ→≡ ⇓id = refl
⇓ₜ→≡ (⇓∀ ⇓t ⇓t′) = {!   !}
⇓ₜ→≡ (⇓≣ ⇓e₁ ⇓e₂) = {!   !} 
⇓ₜ→≡ (⇓↓ ⇓t) = {!   !} 

⇓ₑ→≡ e = {! e  !}

⟦ ` x ⟧ₑ Γ* = lookup Γ* x
⟦ tt ⟧ₑ Γ* = tt
⟦ λ→_ {T = T} e ⟧ₑ Γ* = λ (x : ⟦ T ⟧ₜ Γ*) → ⟦ e ⟧ₑ (Γ* ▷ x)
⟦ e₁ · e₂ ⟧ₑ Γ* = {! ⟦ e₁ ⟧ₑ Γ* (⟦ e₂ ⟧ₑ Γ*)  !} -- substitution preserves denotational semantics
⟦ rfl e ⟧ₑ Γ* = refl
⟦ e ⇝[ ⇓t ] ⟧ₑ Γ* = subst id (⇓ₜ→≡ ⇓t) (⟦ e ⟧ₑ Γ*)
⟦ ↑ T ⟧ₑ Γ* = ⟦ T ⟧ₜ Γ*      