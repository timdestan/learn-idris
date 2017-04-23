module Nats

add : Nat -> Nat -> Nat
add Z m = m
add (S n) m = S (add n m)

sub : Nat -> Nat -> Maybe Nat
sub Z Z = Just Z
sub Z (S _) = Nothing
sub (S n) (S m) = sub n m

mult : Nat -> Nat -> Nat
mult Z k = Z
mult (S j) k = add k (Nats.mult j k)

left_identity : (n: Nat) ->  plus Z n = n
left_identity n = Refl

right_identity : (n: Nat) -> plus n Z = n
right_identity Z = Refl
right_identity (S k) = cong (right_identity k)
