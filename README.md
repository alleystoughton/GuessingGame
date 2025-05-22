Security Through Indirection of a Two-party Guessing Game in EasyCrypt
======================================================================

This repository contains the formalization in
[EasyCrypt](https://github.com/EasyCrypt/easycrypt) of a two-party
boolean guessing game, together with the definition and proof of the
security of an honest party against a possibly malicious one in a
real/ideal simulation-based style. Security is achieved by relying not
on cryptographic mechanisms, but on a shared trusted computing base in
which immutable objects are stored in a physical memory, and the two
parties have virtual memories giving them indirect access to certain
objects. We call this "security through indirection". Correctness of
the protocol is also proved, assuming both parties are honest.

This work is part of a collaboration between myself
([Alley Stoughton](https://alleystoughton.us))
and
[Arthur Azevedo de Amorim](https://arthuraa.net),
[Marco Gaboardi](https://cs-people.bu.edu/gaboardi/) and
[Jared Pincus](https://jaredpincus.com).

