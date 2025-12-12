# Codename: Bin

A collection of binary related property proofs proved in Agda.

## Description

This library contains lots of proofs of binary operations, and was proved in "hardcore"
way, which disallows converting from and to natural numbers. In other words, the proofs
are done in a way that only uses inductive definitions of binary numbers.

This approach allows us to prove that:
- For arbitrary-length binary numbers, the proof are always correct. 

This library is still under development.

## Author's Note

The original idea of this project is meant to prove the properties of binary operations, 
such as verifying the mathematical properties of binary addition, defined in Ripple Carry
Adder.

Later on, I plan to prove some theorems described in Hacker's Delight, so you might see some
proofs related to that book.
