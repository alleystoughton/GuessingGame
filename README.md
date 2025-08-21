Security Through Indirection of a Two-party Guessing Game in EasyCrypt
======================================================================

This repository contains the formalization in
[EasyCrypt](https://github.com/EasyCrypt/easycrypt) of a two-party
boolean guessing game, together with the definition and proof of the
security of an honest party against a possibly malicious one in a
real/ideal simulation-based style.

Security is achieved by relying not on cryptographic mechanisms, but
on a shared trusted computing base in which immutable objects are
stored in a physical memory, and the two parties have virtual memories
giving them indirect access to certain objects. We call this "security
through indirection".

Correctness of the protocol is also proved, assuming both parties are
honest.

This work is part of a collaboration between myself
([Alley Stoughton](https://alleystoughton.us))
and
[Arthur Azevedo de Amorim](https://arthuraa.net),
[Marco Gaboardi](https://cs-people.bu.edu/gaboardi/) and
[Jared Pincus](https://jaredpincus.com).

Here are the [slides](../main/fcs2025.pdf) for my 2025 Workshop on
Foundations of Computer Security (FCS) presentation on this work.

EasyCrypt Theories:

 * [`Memory.ec` - physical and party-indexed virtual memories](../main/Memory.ec)

 * [`Protocol.ec` - guessing game protocols, adversaries, experiments,
   real protocol and honest party](../main/Protocol.ec)

 * [`Correctness.ec` - correctness of the real protocol as applied to
   honest party and clone of honest party](../main/Correctness.ec)

 * [`Security.ec` - definition/proof of security of honest party against
   malicious party/adversary](../main/Security.ec)

There is also a shell script
[`check-all-scripts`](../main/check-all-scripts) for checking all
theories using two SMT provers: Alt-Ergo and Z3. It uses a default
SMT timeout of 2 seconds, but takes the timeout as an optional
command line argument.

The scripts check using versions 2.6.0 of Alt-Ergo and 4.15.3 of Z3.
If you use later versions of these provers and an up-to-date version
of EasyCrypt, feel free to report any script failures.
