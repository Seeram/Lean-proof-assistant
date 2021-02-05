import algebra.group_with_zero.power

-- Vseobecny subor pre skusanie kdecoho elementarneho v leane

-- definicie

def x:ℕ :=5

-- typ sa da inferovat, netreba ho pisat

def x' := 5

-- funkcia "plna definicia"

def f:ℕ → ℕ := λ x:ℕ , 5+x

-- typova inferencia

def f' := λ x:ℕ , 5+x

def f'' := λ x, 5+x 

def fz := λ x:ℤ , 5+x

-- syntakticky cukor pre definovanie funkcii 
-- zatvorky musia byt!

def f'''(x:ℕ):= 5+x

-- typova inferencia

def f''''(x) := 5+x 

-- funkcia dvoch argumentov
def s(x:ℕ) (y:ℕ) := x+y -- s : ℕ → ℕ → ℕ

-- parcialna evaluacia

def sp := s 5 -- sp : ℕ → ℕ

-- toto nejde typovo inferovat:

-- def s'(x) (y) := x + y

-- ale toto ano

 def s''(x) (y) := x+y+0

-- polymorfizmus cez typeclass -- pokus

def s'''{α : Type*} (x:α) (y:α) [has_add α] := x+y

#reduce s''' 5 5 -- ide 
--#reduce s''' 5 -5 -- nejde, usudi asi ze -5 musi byt ℕ
#check s''' 5 (-5:ℤ) 
#reduce s''' 5 (-5:ℤ) -- ale toto ide! 

def a:ℤ := -5
def b:ℤ := -5

#reduce s''' a b -- ide
#reduce s''' a 10 -- ide tiez 


-- lokalne definicie cez let

#eval let x:=5 in x+1
#eval let x:=1, y:=x+x in y*3

-- zavisle typy 

universe u

def dependtype (α: Type u) := 
  Π (α : Type u) , (α → α) → (α → α) 

#check dependtype -- Type u_1 → Type (u_1+1)
#check dependtype ℕ 

-- explicitne uvedenie typu, komplet

def sqf : Π (α : Type u) , (α → α) → (α → α) :=
  λ (α: Type u) (f: α → α), f∘f

-- explicitne uvedenie typu + typova inferencia

def sqf' (α : Type u) := 
  λ (f: α → α), f∘f   

def sqf'' :=
  λ (α: Type u) (f: α → α), f∘f

-- typy v lambde sa daju inferovat

def sqf''' : Π (α : Type u) , (α → α) → (α → α) :=
  λ α f, f∘f

#check sqf
#check sqf'
#check sqf''
#check sqf ℕ f 
#eval sqf ℕ f 5 -- 15
#eval sqf'' ℕ f 5 -- 15

-- verzia horeuvedeneho s implicitnym typovym argumentom
-- pouzitie kuceravych zatvoriek

def sqf_implicit : Π {α : Type u} , (α → α) → (α → α) :=
  λ (α: Type u) (f: α → α), f∘f

def sqf_implicit' {α: Type u} :=
  λ (f: α → α), f∘f 
 
def sqf_implicit'' :=
  λ {α: Type u} (f: α → α), f∘f

#check sqf_implicit -- (?M_1 → ?M_1) → ?M_1 → ?M_1

#check @sqf_implicit'' -- odimplicitenie
-- sqf_implicit'' : Π {α : Type u_1}, (α → α) → α → α
            
#check sqf_implicit'
#check sqf_implicit''
#eval sqf_implicit f 5 -- 15
#eval @sqf_implicit ℕ f 5 -- 15

-- syntakticky cukrik

#eval nat.add 5 5 -- toto je realny vyraz
#eval let x:=5 in x.add 5 -- toto su skratky
#eval (5:ℕ).add 5 

#check (→) -- takto sa zabrani tomu, aby doslo k syntaktickej chybe 
#check (1=1) → (2=2)

-- assume je iba alias pre λ

#eval (assume n:ℕ , n) 2


#check or (1=1) (2=1) -- treba zatvorkovat
#check 1=1 ∨ 2=1 -- netreba zatvorkovat
#eval (1=1 ∨ 2=1:bool) -- Prop sa da castnut ako bool, potom ho mozeme vypisat
 

section pred

variables (α: Type*) (p q :α → Prop)

example: (∀ x: α, p x ∧ q x) → ∀ y: α, p y :=
  begin
    intro h1,
    intro y,
    specialize h1 y,
    exact h1.left,
  end

end pred

def fib: ℕ → ℤ
| 0 := 0
| 1 := 1
| (n+2) := fib(n+1) + fib n

#print instances has_pow  

theorem cassini : ∀ (n : ℕ), fib(n)*fib(n+2)-fib(n+1)*fib(n+1)=(-1:ℤ)^(n+1) :=
begin
  intro,
  induction n,
  {finish,},
  sorry,
end

-- typeclasses


#check has_le.le 1 2





