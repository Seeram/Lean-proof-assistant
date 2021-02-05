import tactic
import group_theory.submonoid

-- submonoidy : druhy den experimentov
-- teraz sa idem postupne pozerat na to, co je o monoidoch implementovane
-- a skusat si to
-- skusim najma konverziu submonoid -> monoid, snad to pojde

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

#check (3 ∈ odd_nat_submonoid) -- toto ide, lebo submonoid ma has_mem implementovane
#check odd_nat_submonoid ⊓ odd_nat_submonoid -- aj prieniky submonoidov vieme
#check monoid odd_nat_submonoid
#reduce monoid odd_nat_submonoid -- aha, aj oni tam maju subtyp

-- toto sa rozbehlo az po doplneni
-- import group_theory.submonoid
  
#check (submonoid.to_monoid odd_nat_submonoid) 
#check (submonoid.to_monoid odd_nat_submonoid).mul

def one_odd : odd_nat_submonoid := {
  val := 1,
  property := begin -- musim dokazat, ze 1 je neparna ale to som uz robil
  exact odd_nat_submonoid.one_mem',
  end
}

def three_odd : odd_nat_submonoid := 
⟨ 3, 
begin
  change 3∈ { n:ℕ | odd(n)}, -- toto je strasne neobratne, ako to ide lepsie?
  simp,
  existsi 1,
  ring,
end 
⟩ 


-- submonoid.to_monoid konvertuje submonoid na monoid,
-- to som vcera robil rucne ja

#check (submonoid.to_monoid odd_nat_submonoid).mul

-- nasledujuci riadok nejde, preco? 
-- #check (submonoid.to_monoid odd_nat_submonoid).mul three_odd three_odd 

-- ale toto ide!

#reduce let mmul:=(submonoid.to_monoid odd_nat_submonoid).mul in mmul three_odd three_odd 

-- treba tam dat typ explicitne, neviem preco
#check @monoid.mul 
#reduce @monoid.mul odd_nat_submonoid (submonoid.to_monoid odd_nat_submonoid) three_odd three_odd 
-- pritom sa moze vynechat, takze nabehne typova inferencia
#reduce @monoid.mul _ (submonoid.to_monoid odd_nat_submonoid) three_odd three_odd 
-- zahada


-- HMM: 
-- https://leanprover-community.github.io/archive/stream/113489-new-members/topic/How.20to.20access.20the.20multiplication.20inside.20the.20monoid.20inside.20.2E.2E.html
-- Nie je mi to jasne

-- ale ide spravit instancia

@[instance]
def odd_nat_monoid : monoid odd_nat_submonoid :=
  submonoid.to_monoid odd_nat_submonoid

#print instances monoid 

-- kedze som ten submonoid zaregistroval ako monoid, mozem robit toto:

#reduce three_odd*three_odd









 
