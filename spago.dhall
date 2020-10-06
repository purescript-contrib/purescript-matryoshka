{ name = "matryoshka"
, dependencies =
  [ "console"
  , "effect"
  , "fixed-points"
  , "free"
  , "prelude"
  , "profunctor"
  , "psci-support"
  , "transformers"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs", "test/**/*.purs" ]
}
