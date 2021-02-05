import tactic

-- monoidy a submonoidy : prvy den experimentov
-- ignoroval som vacsinu toho co uz je implementovane

-- skusil som spravit z konkretneho submonoidu neparnych cisel subtyp
-- monoidu (nat,*,1) a potom som na nom implementoval monoidovu strukturu

-- monoid je mnozina vybavena binarnou operaciou, ktora je
-- asociativna a jednotkovym prvkom ; spravim teraz
-- dvojprvkovy polozvaz S2:=({zero,one},one,⊓) holymi rukami

-- dvojprvkovy induktivny typ
inductive S2: Type
  | zero
  | one

--  ⊓   | zero | one  |
-- --------------------
-- zero | zero | zero |
-- one  | zero | one  |

#check S2.zero

-- to, ze je toto nazvane S2.mul je konvencia, nie nevyhnutnost
-- mohlo by sa to volat aj hocijako inak
-- takisto S2.monoid dolu
def S2.mul: S2 → S2 → S2
 | S2.one a := a
 | a S2.one := a
 | S2.zero S2.zero := S2.zero

-- teraz poviem, ze (S2,S2.one,S2.mul) je monoid
-- mechanizmus, ktorym sa to robi je ten,
-- ze dokazem, ze typ S2 je instanciou typeclass monoid

@[instance] 
def S2.monoid : monoid S2 :=
{
  mul:= S2.mul,
  one:= S2.one,
  -- tu musim dokazat, ze ta operacia je asociativna
  -- asi by to islo lahsie tak, ze najprv dokazem
  -- jednotkove zakony a potom ich pouzijem
  mul_assoc:=
  begin
    intros a b c,
    cases a,
    cases b,
    cases c,
    refl,
    refl,
    cases c,
    refl,
    refl,
    cases b,
    cases c,
    refl,
    refl,
    cases c,
    refl,
    refl,  
  end,
  -- jednotkovy zakon zlava a sprava
  one_mul:=
  begin
      intro a,
      cases a,
      refl,
      refl,
  end,
  mul_one :=
  begin
    intro a,
    cases a,
    refl,
    refl,
  end
} 

-- V tomto momente je S2 pouzitelny ako monoid
-- medziinym mame aj nasobenie prvkov cez *
-- kvoli tomu, ze typeclass monoid rozsiruje typeclass has_mul
-- has_mul je typeclass, ktory zavadza binarnu operaciu
-- mul a notaciu _ * _

#check S2.zero*S2.one
#reduce S2.zero*S2.one

-- takisto mame konstantu 1, (typeclass has_one) ktora sa nam prepisuje
-- na spravny prvok typu S2

#check (1:S2)
#reduce (1:S2)

-- takisto mozeme pouzivat asociativny zakon
#check monoid.mul_assoc 
#check monoid.mul_assoc S2.zero S2.one S2.zero 


-- Teraz idem vyskusat, ako funguju submonoidy
-- ked sa referencuje na ℕ ako monoid, mysli sa nasobenie

-- idem vyrobit submonoid monoidu (ℕ,*,1)
-- pozostavajuci z neparnych cisel

-- submonoid je trojica
--    carrier : podmnozina monoidu
--    one_mem' : dokaz, ze jednotka monoidu patri do monoidu
--    mul_mem' : dokaz, ze submonoid je uzavrety na nasobenie

def odd_nat_submonoid: submonoid ℕ :=
  {
    carrier := {n:ℕ | odd n}, -- mnozina
    one_mem' := -- dokaz, ze jednotka patri do tej mnoziny
    begin
      simp,
      existsi 0,
      simp,
    end,
    mul_mem' := -- dokaz, ze ta mnozina je uzavreta na nasobenie
    begin
      intros a b,
      intro a_odd,
      intro b_odd,
      simp at a_odd,
      simp at b_odd,
      simp,
      cases a_odd with k,
      cases b_odd with l,
      existsi 2*k*l+k+l, -- som musel toto zratat na papieri
      rw a_odd_h,
      rw b_odd_h,
      ring, -- taktika pre okruhy (nasobenie+scitanie), usetri robotu
    end
  }

-- v mathlib je implementovana o submonoidoch cela kopa veci:
-- submonoidy monoidu tvoria poset vzhladom na inkluziu
-- prienik sumbonoidov je submonoid,
-- atd ...

--- ALE!

-- submonoid nie je monoid, nie v leane

-- teraz idem z toho submonoidu neparnych cisel vytvorit monoid

-- vytvorime subtyp (vid subtype v TPiL)

def odd_nat_subtype := {n:ℕ // n ∈ odd_nat_submonoid.carrier}

-- ten subtyp je typ struktur { val:= n:ℕ, prop:= dokaz, ze n je neparne }
-- nie je pravda, ze 3:odd_nat_subtype

-- ideme teraz pre odd_nat_subtype definovat jednotku a nasobenie

-- toto bude jednotka
@[simp]
def one_odd : odd_nat_subtype := {
  val := 1,
  property := begin -- musim dokazat, ze 1 je neparna ale to som uz robil
  exact odd_nat_submonoid.one_mem',
  end
}

-- jednotlive zlozky dvojice
#reduce one_odd.val
#reduce one_odd.property -- hmm

-- chcem este nejaky iny prvok
-- ⟨ ... ⟩ je alternativna (nepomenovana) notacia pre {...} s pomenovanymi
-- zlozkami
def three_odd : odd_nat_subtype := 
⟨ 3, 
begin
  change 3∈ { n:ℕ | odd(n)}, -- toto je strasne neobratne, ako to ide lepsie?
  simp,
  existsi 1,
  ring,
end 
⟩ 


-- teraz skusme zadefinovat nasobenie neparnych cisel aj
-- s transformaciou dokazu neparnosti 
@[simp] -- zapojime do simp mechanizmu, to sa zide neskor
def odd_mul (a b:odd_nat_subtype) : odd_nat_subtype :=
  ⟨ a.val*b.val,
    begin
      have a_odd := a.property,
      have b_odd := b.property,
      apply odd_nat_submonoid.mul_mem',
      exact a_odd,
      exact b_odd,
    end
  ⟩

lemma one_mul_odd {a :odd_nat_subtype} : odd_mul one_odd a = a :=
  by simp


lemma mul_one_odd {a :odd_nat_subtype} : odd_mul a one_odd = a :=
  by simp

#reduce odd_mul one_odd one_odd
#reduce odd_mul three_odd three_odd
def odd_nine := odd_mul three_odd three_odd 

#reduce odd_nine.val -- 9
#reduce odd_nine.property -- tato hodnota je extremne zaujimava ?!ODKIAL?!

-- skusme teraz vyvorit instanciu monoidu z odd_nat_subtype

@[instance] def odd_nat_monoid : monoid odd_nat_subtype :=
{
  mul:=odd_mul,
  one:=one_odd,
  mul_assoc := begin
    finish, -- toto ide kvoli tomu @[simp] atributu vyssie 
  end,
  one_mul:= begin
    intro,
    have ha:= @one_mul_odd a,
    exact ha,
  end,
  mul_one:= begin
     intro,
     have ha:= @mul_one_odd a,
     exact ha,
  end
}

#reduce (odd_nine*odd_nine).val -- 81, hura!
 
