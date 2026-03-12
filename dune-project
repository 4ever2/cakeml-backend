(lang dune 3.21)
(using rocq 0.11)
(name rocq-cakeml-extraction)
(version dev)

(generate_opam_files false)

(source (github peregrine-project/cakeml-backend))
(license MIT)
(authors "The Peregrine team")
(maintainers "The Peregrine team")

(package
 (name rocq-cakeml-extraction)
 (synopsis "CakeML backend for Peregrine")
 (depends (rocq-core (>= 9.0~))
   (rocq-stdlib (>= 9.0~))
   (rocq-metarocq-erasure-plugin (>= 1.4))
   (rocq-ceres-bytestring (>= 1.0.0))
  )
)
