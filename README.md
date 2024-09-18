# Formally Verified Cryptography Proofs Using Lean 4

This is an ongoing port of the work found [here](https://github.com/dtumad/lean-crypto-formalization), from Lean 3 to Lean 4.
All of the basic theory is present here, but some proofs and APIs are still actively being moved. 

The library aims to provide a foundational framework in Lean for reasoning about cryptographic protocols in the computational model. The core part of the framework provides:

* A monadic syntax for representing computations with oracle access (`OracleComp`), with probabilistic computations as a special case of having uniform selection oracles
* A denotational semantics (`evalDist`) for assigning probability distributions to probabilistic computations, and tools for reasoning about the probabilities of particular outputs or events (`probOutput`/`probEvent`)
* An operational semantics (`simulate`) for implementing/simulating the behavior of a computation's oracles, including implementations of random oracles, query logging, reductions, etc.

It also aims to provide definitions for cryptographic primitives such as symmetric/asymmetric encryption, (ring) signatures, $\Sigma$-protocols, hashing algorithms, etc. 

The project can be installed and built by running:

```
lake exe cache get && lake build
```

Mathematical foundations such as probability theory, computational complexity, and algebraic structures are based on or written to the [Mathlib](https://github.com/leanprover-community/mathlib4) project, making all of that library usable in constructions and proofs.

Generally the project aims to enable proof complexity comparable to that found in mathlib.
It's most well suited to proving concrete security bounds for reductions, and for establishing the security of individual cryptographic primitives.
It allows for fully foundational proofs of things like forking/rewinding adversaries and Fiat-Shamir style transforms, but has less support for composing a large number of primitives into complex protocols.
Asymptotic reasoning is also supported, but tooling and automation for this is currently limited.

The `VCVio` directory provides all of the foundations and framework definitions / APIs. `Examples` contains example constructions of standard cryptographic algorithms.

<!-- # Framework Overview

## Representing Computations

## Probabilities of Outputs and Events

## Implementing and Simulating Oracles -->