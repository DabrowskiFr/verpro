(lang dune 3.10)

(name verpro)

(using menhir 2.0)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Frédéric Dabrowski")

(maintainers "Frédéric Dabrowski")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name verpro)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends 
  (ocaml (>= 5.1.0)) 
  dune
  menhir
  (ocamlformat (and (= 0.26.1) :with-dev-setup))
  (ocaml-lsp-server :with-dev-setup))
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
