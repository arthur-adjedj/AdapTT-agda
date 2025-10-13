# Formalisation of *AdapTT: Functoriality for Dependent Type Casts*

This folder contains the formalisation done for the paper *AdapTT: Functoriality for Dependent Type Casts*.

## Building

These files were compiled using Agda 2.7.0.1.
Note that type-checking these files is quite resource-intensive, and may take a long time to compile. (Takes ~6m20s on a Ryzen 7 9800X3D/32Gb DDR5, and ~18m30s on an I7 10510U/16GB DDR4)

## Structure

The file structure is as follows:

| File | Content |
|------|---------|
| `Std.agda` | Generic definitions regarding equality and lists
| `Dir.agda` | Definition of directions (covariance, contravariance), as well as operators and equations on these directions
| `AppCx.agda` | Formalisation of parts of `AdapTT2` (excluding inductive types) (corresponding to Appendix C.x / Fig. 3-6)
| `AdapTT2.agda` | Collects the formalisation of `AdapTT2` from the AppCx files
| `Pi.agda` | Formalisation of Pi Types (Appendix C.7 / Fig. 7)
| `IndSig.agda` | Formalisation of inductive types (Appendix C.8 / Fig. 8-9)
| `IndAd.agda` | Formalisation of inductive adapter equations, without and with indices (Appendix C.8 / Fig. 10)

## Notes

The rewrite rules we add to emulate an extensional type theory are non-confluent, causing issues with Agda being incomplete, i.e. not recognizing definitional equalities that hold in a meta-theory with equality reflection.

The files `Pi.agda` and `IndAd.agda` thus contain a few holes, which we have filled with the adequate term. We checked on paper that those terms have the desired types modulo equalities that we have declared and added as rewrite rules, but rewrite rules fail to trigger in those cases, causing Agda's type-checking to be incomplete, and rejecting the terms as ill-formed.