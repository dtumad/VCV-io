# Formally Verified Cryptography Proofs in Lean 4

This library aims to provide a foundational framework in Lean for reasoning about cryptographic protocols in the computational model. The core part of the framework provides:

* A monadic syntax for representing computations with oracle access (`OracleComp`), with probabilistic computations as a special case of having uniform selection oracles
* A denotational semantics (`evalDist`) for assigning probability distributions to probabilistic computations, and tools for reasoning about the probabilities of particular outputs or events (`probOutput`/`probEvent`)
* An operational semantics (`simulate`) for implementing/simulating the behavior of a computation's oracles, including implementations of random oracles, query logging, reductions, etc.

It also provides definitions for cryptographic primitives such as symmetric/asymmetric encryption, (ring) signatures, $\Sigma$-protocols, hashing algorithms, etc. 

Assuming Lean 4 and lake are already installed, the project can be built by just running:

```
lake exe cache get && lake build
```

Mathematical foundations such as probability theory, computational complexity, and algebraic structures are based on or written to the [Mathlib](https://github.com/leanprover-community/mathlib4) project, making all of that library usable in constructions and proofs.

Generally the project aims to enable proof complexity comparable to that found in mathlib.
It's most well suited to proving concrete security bounds for reductions, and for establishing the security of individual cryptographic primitives.
It allows for fully foundational proofs of things like forking/rewinding adversaries and Fiat-Shamir style transforms, but has less support for composing a large number of primitives into complex protocols.
Asymptotic reasoning is also supported, but tooling and automation for this is currently limited.

The `VCVio` directory provides all of the foundations and framework definitions / APIs. `Examples` contains example constructions of standard cryptographic algorithms.

See [here](https://github.com/dtumad/lean-crypto-formalization) for an outdated version of the library in Lean 3.

<!-- # Framework Overview

## Representing Computations

## Probabilities of Outputs and Events

## Implementing and Simulating Oracles -->
