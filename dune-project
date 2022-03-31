(lang dune 2.2)
(using coq 0.1)
(name coq-monadic-grammars)

(generate_opam_files true)

(package 
 (name coq-monadic-grammars)
 (depends 
  (coq (>= 8.13.0))
 )
 (synopsis "Monadic regular parsers in Coq")
 (description  "Monadic regular parsers in Coq")
 (maintainers   "jsarracino@cornell.edu")
 (authors      "John Sarracino")
 (homepage     "https://github.com/jsarracino/dependent-regular-grammars")
 (bug_reports  "https://github.com/jsarracino/dependent-regular-grammars")
 (license      "MIT")
)
