module Product
%default total


using (n:Nat, m:Nat, p:Nat)
  divisors : n = p * m -> (Nat, Nat)
  divisors {n = (p * m)} Refl = (p, m)


divs : (S (S (S (S Z)))) = (S (S (S (S Z)))) * (S Z) -> (Nat, Nat)
divs four_equals_four_times_one = divisors four_equals_four_times_one
