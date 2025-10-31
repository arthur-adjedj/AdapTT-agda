# Formalisation of *AdapTT: Functoriality for Dependent Type Casts*

This folder contains the formalisation done for the POPL submission *AdapTT: Functoriality for Dependent Type Casts*.

## Building

These files were compiled using Agda 2.8.0.
Instructions to obtain agda can be found at: https://agda.readthedocs.io/en/v2.8.0/getting-started/installation.html
Once agda available the development can be built from command line using:

```
$ agda All_but_slow.agda
```

Note that this is quite resource-intensive, and may take a long time to compile.
For indication the above took ~17m20s on a Ryzen 7 9800X3D with 32Gb DDR5, and ~50m on an I7 10510U with 16GB DDR4.

The above command **does not compile the `AppC5-slow.agda` and `AppC6-slow.agda`** files: although we have managed to individually type-check the rules in these files (by commenting out all code but one rule), there seems to be a non-linear behaviour, where the type-checking of the entire file takes much longer (and much more memory) than that of the individual rules. We have not been able to complete the type-checking of these files (after 5+ hours and 30+GB memory use).
Despite this, we still include these files for the sake of completeness and future reference.

## Structure

The file structure is as follows:

| File | Content |
|------|---------|
| `Std.agda`       | Generic definitions regarding equality and lists
| `Dir.agda`       | Definition of directions (covariance, contravariance), as well as operators and equations on these directions
| `AppCx.agda`     | Formalisation of parts of `AdapTT2` (excluding inductive types) (corresponding to Appendix C.x / Fig. 3-6)
| `AppCx-slow.agda`| Formalisation of the slowest parts of `AdapTT2`, not necessary to compile `IndAd.agda`
| `AdapTT2.agda`   | Collects the formalisation of `AdapTT2` from the AppCx files
| `Pi.agda`        | Formalisation of Pi Types (Appendix C.7 / Fig. 7)
| `IndSig.agda`    | Formalisation of inductive types (Appendix C.8 / Fig. 8-9)
| `IndAd.agda`     | Formalisation of inductive adapter equations, without and with indices (Appendix C.8 / Fig. 10)
| `All.agda`       | Packaging file importing all the above files

## Notes

The rewrite rules we add to emulate an extensional type theory are non-confluent, causing issues with Agda being incomplete, i.e. not recognizing definitional equalities that hold in a meta-theory with equality reflection.

The files `AppC5.agda`, `AppC5-slow.agda`, `Pi.agda` and `IndAd.agda` thus contain a few holes, which we have filled with the adequate term. We checked on paper that those terms have the desired types modulo equalities that we have declared and added as rewrite rules, but rewrite rules fail to trigger in those cases, causing Agda's type-checking to be incomplete, and rejecting the terms as ill-formed.

Explanations of the agda options employed in the files:
- `{-# OPTIONS --rewriting #-}`: activate [rewrite rules](https://agda.readthedocs.io/en/v2.8.0/language/rewriting.html#rewriting)
- `{-# OPTIONS  --allow-unsolved-metas #-}`: [allows files with holes to compile](https://agda.readthedocs.io/en/latest/tools/command-line-options.html#cmdoption-allow-unsolved-metas), useful in the cases where Agda's definitional equality fails, as mentioned above

The point of this formalisation is not to verify any particular properties of our theory. Instead, because the definition of the theory itself contains a large amount of typing rules, this formalisation was merely used to ensure our typing rules were all type-correct.