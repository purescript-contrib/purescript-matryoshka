{ name = "matryoshka"
, dependencies =
  [ "bifunctors"
  , "console"
  , "control"
  , "distributive"
  , "effect"
  , "either"
  , "fixed-points"
  , "foldable-traversable"
  , "free"
  , "identity"
  , "lists"
  , "newtype"
  , "prelude"
  , "profunctor"
  , "transformers"
  , "tuples"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs", "test/**/*.purs" ]
}
