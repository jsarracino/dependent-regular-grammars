# Dependent Regular Grammars
This is a Coq library for reasoning about data-dependent parsers.
The key idea is to extend regular languages (i.e. regexs) with a *monadic bind* operator, which replaces the traditional regular concatenation.


## Building
The implementation depends on Coq version 8.13+, Equations 1.3, and dune. To build/install the library, from the root of the project run `dune build` or `dune install` respectively.

## Parsers
The definition is found in [src/theories/Regular.v](src/theories/Regular.v), which defines a core inductive type for `parser`s, indexed by the return type of the parser. So a parser for nats has type `parser nat`. 

The definition also includes a high-level semantics, relating strings and parsers to parse results (`Parses`) and a iterative parsing function `parses_derivs s p` for calculating a list of parse results of `p` run on the string `s`. 

For more details please see our paper in LangSec '22: [Certified Parsing of Dependent Regular Grammars](https://www.cs.cornell.edu/~jsarracino/files/depgrammars.pdf)

# Example: Netstring parser
We implement a parser for netstrings in [src/theories/Libs/Netstrings.v](src/theories/Libs/NetStrings.v), called `net_str`. You can see the parsing behavior with `vm_compute`, for example:

```
(* The netstring 13:hello, world!, *)
Definition test_hw_netstr := ("1" ::
 "3" ::
 ":" ::
 "h" :: 
 "e" ::
 "l" ::
 "l" ::
 "o" ::
 "," ::
 " " ::
 "w" ::
 "o" ::
 "r" ::
 "l" ::
 "d" ::
 "!" ::
 "," :: nil).
 
Time Eval vm_compute in parse_netstr test_hw_netstr.

(* ... produces test_hw_netstr :: nil in 0.002 secs ... *)
```

We prove a strong specification for the netstring parser using the high-level parsing semantics: 

```   
Theorem net_str_spec:
  forall s v, 
    Parses s net_str v <->
    exists s', 
      s = s' ++ (":" :: v ++ ("," :: nil)) /\  
      Parses s' num (length v).
```

# Recursive parsers
We also implement a version of recursive parsers using parametric higher-order syntax (PHOAS) in [src/theories/Parsers.v](src/theories/Parsers.v). This encoding is significantly less polished than the dependent grammars and your mileage may vary :). 
