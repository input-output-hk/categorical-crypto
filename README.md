# Categorical Cryptogrpahy

A process calculus for cryptographic protocols using category theory, implemented in Agda. This library provides a mathematical framework for specifying, composing, and reasoning about cryptographic protocols. It can be used for cryptographic work or to prove that properties of cryptographic primitives translate into security properties of large programs.

Instead of ad-hoc specifications, cryptographic protocols are modeled via:

- **Channels**: Communication pathways with input/output types
- **Machines**: Stateful computations that communicate via channels
- **Composition operations**: Protocols can be composed using sequential and parallel composition

## Project Structure

```
src/
├── CategoricalCrypto.agda              # Main module
├── CategoricalCrypto/
│   ├── Channel/
│   │   ├── Core.agda                  # Channel definitions and morphisms
│   │   ├── Category.agda              # Category of channels and wirings
│   │   └── Selection.agda             # DSL for channel wiring patterns
│   ├── Machine/
│   │   ├── Core.agda                  # Machine definitions and UC security
│   │   └── Constraints.agda           # Adding extra constraints
│   ├── Examples/                      # Various relevant examples
│   └── SFunM.agda                     # Category of stateful, monadic functions
└── Categories/                        # Extra category theory stuff
```
